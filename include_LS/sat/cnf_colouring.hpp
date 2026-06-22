#ifndef BA_GRAPH_SAT_CNF_COLOURING_HPP
#define BA_GRAPH_SAT_CNF_COLOURING_HPP

#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>

#include "cnf.hpp"
#include "cnf_encoding.hpp"
#include "invariants/degree.hpp"
#include "invariants/girth.hpp"
#include "operations/line_graph.hpp"
#include "solution_types.hpp"

namespace ba_graph {

/**
 * @brief Self-describing encoding for k-vertex-colouring.
 *
 * Stores the CNF formula, variable map, and colour count needed to decode
 * a SAT model into a vertex colouring without needing the original graph.
 */
struct VertexColouringCnfEncoding {
    CNF cnf;
    std::map<Number, CnfVarList> vertex_colour_vars;
    int colour_count;

    sat_model::VertexColouring decode_model(const std::vector<bool> &model) const {
        validate_model_covers_vars(
            model, cnf.num_vars(), "VertexColouringCnfEncoding::decode_model"
        );
        sat_model::VertexColouring colouring;
        for (const auto &[v, var_list] : vertex_colour_vars) {
            validate_var_list_size(
                var_list, static_cast<std::size_t>(colour_count),
                "VertexColouringCnfEncoding::decode_model"
            );
            int chosen = -1;
            for (int c = 0; c < colour_count; ++c) {
                if (model.at(static_cast<std::size_t>(var_list[static_cast<std::size_t>(c)]))) {
                    if (chosen != -1) {
                        throw std::runtime_error(
                            "VertexColouringCnfEncoding::decode_model: "
                            "multiple colours assigned to vertex"
                        );
                    }
                    chosen = c;
                }
            }
            if (chosen == -1) {
                throw std::runtime_error(
                    "VertexColouringCnfEncoding::decode_model: "
                    "missing colour assignment for vertex"
                );
            }
            colouring[v] = chosen;
        }
        return colouring;
    }
};

/**
 * @brief Self-describing encoding for k-edge-colouring.
 *
 * Wraps a VertexColouringCnfEncoding for the line graph and stores a map
 * from line graph vertex numbers to original graph edge locations, so that
 * decode_model does not need the original graph for interpretation.
 */
struct EdgeColouringCnfEncoding {
    VertexColouringCnfEncoding line_graph_encoding;
    std::map<Number, Location> line_vertex_to_location;
    int colour_count;

    sat_model::EdgeColouring decode_model(const std::vector<bool> &model) const {
        sat_model::VertexColouring line_colouring = line_graph_encoding.decode_model(model);
        sat_model::EdgeColouring colouring;
        for (const auto &[line_vertex, loc] : line_vertex_to_location) {
            auto it = line_colouring.find(line_vertex);
            if (it == line_colouring.end()) {
                throw std::runtime_error(
                    "EdgeColouringCnfEncoding::decode_model: "
                    "line graph vertex not mapped"
                );
            }
            colouring[loc] = it->second;
        }
        if (static_cast<int>(colouring.size()) !=
            static_cast<int>(line_vertex_to_location.size())) {
            throw std::runtime_error(
                "EdgeColouringCnfEncoding::decode_model: "
                "incomplete edge colouring model"
            );
        }
        return colouring;
    }
};

struct ColouringCnfOptions {
    int vertex_colour_sinz_threshold = CnfBuilder::DEFAULT_SINZ_THRESHOLD_AT_MOST_ONE;
    /**
     * Precolours the first edge's endpoints (or a max-degree vertex's incident
     * edges for edge colouring) to anchor colour labels and break
     * colour-permutation symmetry.
     *
     * The raw CNF default is false: callers that add labelled constraints
     * above the base CNF, such as precolouring assumptions, may choose labels
     * that do not match this canonical representative. Decision SAT wrappers
     * may enable it explicitly when they own the full solving goal.
     */
    bool break_symmetry_by_precolouring = false;
    /**
     * For each group of parallel edges, enforces a canonical ordering of
     * colours (smaller Location index -> smaller colour). This breaks k!
     * permutation symmetry for k parallel edges. No-op on simple graphs.
     *
     * Benchmarks on random multigraphs (see benchmark/colouring/README_parallel_edge_ordering.md)
     * show this adds 2-5x overhead to chromatic index determination with no
     * measurable benefit for SAT solving -- the symmetry pruning does not
     * offset the extra clause overhead on the tested instances. Kept
     * available for AllSAT enumeration and hard UNSAT proofs where
     * pruning may help. Defaults to false.
     */
    bool break_symmetry_by_ordering_parallel_edges = false;
    OrderingEncoding parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    void validate(std::string_view context) const {
        if (vertex_colour_sinz_threshold < 0) {
            throw std::invalid_argument(
                std::string(context) + ": vertex_colour_sinz_threshold must be non-negative"
            );
        }
        switch (parallel_edge_ordering_encoding) {
            case OrderingEncoding::DIRECT:
            case OrderingEncoding::SUPPORT:
                break;
            default:
                throw std::invalid_argument(
                    std::string(context) + ": unknown parallel_edge_ordering_encoding"
                );
        }
    }
};

/**
 * @brief Generates encoding for k-vertex-colouring with given precoloring.
 *
 * @param G The input graph
 * @param k Number of colors available
 * @param precolouring Map of vertices to their preassigned colors
 * @param opts Options for CNF construction
 * @return VertexColouringCnfEncoding containing CNF and decode metadata, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline VertexColouringCnfEncoding build_vertex_colouring_cnf_encoding(
    const Graph &G, int k, std::map<Vertex, int> precolouring, const ColouringCnfOptions &opts = {}
) {
    opts.validate("build_vertex_colouring_cnf_encoding");
    if (k < 0) {
        throw std::invalid_argument("build_vertex_colouring_cnf_encoding: k must be non-negative");
    }
    if (has_loop(G)) {
        return {CNF::unsatisfiable(), {}, k};
    }
    if (k == 0) {
        if (G.order() == 0) {
            return {CNF::satisfiable(), {}, k};
        }
        return {CNF::unsatisfiable(), {}, k};
    }
    for (const auto &[v, c] : precolouring) {
        if (c < 0 || c >= k) {
            throw std::invalid_argument(
                "build_vertex_colouring_cnf_encoding: precoloured vertex has invalid colour "
                "(must be 0 <= colour < k)"
            );
        }
        if (!G.contains(v)) {
            throw std::invalid_argument(
                "build_vertex_colouring_cnf_encoding: precoloured vertex not found in graph"
            );
        }
    }
    if (static_cast<long long>(G.order()) * k > std::numeric_limits<int>::max()) {
        // LCOV_EXCL_START — requires impossibly large graph to trigger
        throw std::overflow_error(
            "build_vertex_colouring_cnf_encoding: variable count overflows int"
        );
        // LCOV_EXCL_STOP
    }

    std::map<Number, CnfVarList> vars;
    CnfBuilder builder;
    for (auto &r : G) {
        CnfVarList v = builder.new_vars(k);
        vars[r.n()] = v;
    }

    for (auto &r : G) {
        const int noColour = -1;
        auto preIt = precolouring.find(r.v());
        int preC = (preIt != precolouring.end()) ? preIt->second : noColour;

        if (preC == noColour) {
            // at least one colour for the vertex
            // at most one colour for the vertex
            builder.add_exactly_one(vars[r.n()], opts.vertex_colour_sinz_threshold);
        } else {
            // if precoloured by c, this vertex gets only colour c and no other colour
            for (int c = 0; c < k; ++c) {
                if (c == preC) {
                    builder.add_unit_clause(builder.lit(vars[r.n()][c]));
                } else {
                    builder.add_unit_clause(builder.not_lit(vars[r.n()][c]));
                }
            }
        }

        for (auto &i : r) {
            if (i.n2() <= r.n()) {
                continue;
            }
            auto preIt2 = precolouring.find(i.v2());
            int preC2 = (preIt2 != precolouring.end()) ? preIt2->second : noColour;

            // no adjacent vertices have the same colour
            if ((preC == noColour) && (preC2 == noColour)) {
                for (int c = 0; c < k; ++c) {
                    builder.add_clause(
                        {builder.not_lit(vars[r.n()][c]), builder.not_lit(vars[i.n2()][c])}
                    );
                }
            } else if ((preC == noColour) && (preC2 != noColour)) {
                builder.add_clause({builder.not_lit(vars[r.n()][preC2])});
            } else if ((preC != noColour) && (preC2 == noColour)) {
                builder.add_clause({builder.not_lit(vars[i.n2()][preC])});
            } else {
                if (preC == preC2) {
                    return {CNF::unsatisfiable(), {}, k};
                }
            }
        }
    }
    auto cnf = builder.build("build_vertex_colouring_cnf_encoding");
    for (const auto &[v, var_list] : vars) {
        validate_var_list_size(
            var_list, static_cast<std::size_t>(k), "build_vertex_colouring_cnf_encoding"
        );
        for (int c = 0; c < k; ++c) {
            validate_var_in_cnf(
                var_list[static_cast<std::size_t>(c)], cnf.num_vars(),
                "build_vertex_colouring_cnf_encoding"
            );
        }
    }
    return {std::move(cnf), std::move(vars), k};
}

/**
 * @brief Generates encoding for k-vertex-colouring.
 *
 * Symmetry breaking (controlled by opts.break_symmetry_by_precolouring)
 * precolours two adjacent vertices to colours 0 and 1 (or a triangle's
 * vertices to colours 0, 1, 2).
 *
 * @param G The input graph
 * @param k Number of colors available
 * @param opts Options for CNF construction
 * @return VertexColouringCnfEncoding containing CNF and decode metadata, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline VertexColouringCnfEncoding build_vertex_colouring_cnf_encoding(
    const Graph &G, int k, const ColouringCnfOptions &opts = {}
) {
    opts.validate("build_vertex_colouring_cnf_encoding");
    if (k < 0) {
        throw std::invalid_argument("build_vertex_colouring_cnf_encoding: k must be non-negative");
    }
    if (has_loop(G)) {
        return {CNF::unsatisfiable(), {}, k};
    }
    std::map<Vertex, int> precolouring;
    if (opts.break_symmetry_by_precolouring) {
        auto triangle = find_triangle(G);
        if (triangle.has_value()) {
            if (k < 3) {
                return {CNF::unsatisfiable(), {}, k};
            }
            precolouring[G[(*triangle)[0]].v()] = 0;
            precolouring[G[(*triangle)[1]].v()] = 1;
            precolouring[G[(*triangle)[2]].v()] = 2;
        } else if (G.size() >= 1) {
            if (k < 2) {
                return {CNF::unsatisfiable(), {}, k};
            }
            Edge e = G.find(RP::all(), IP::all()).second->e();
            precolouring[e.v1()] = 0;
            precolouring[e.v2()] = 1;
        }
    }
    return build_vertex_colouring_cnf_encoding(G, k, precolouring, opts);
}

/**
 * @brief Generates CNF formula for k-vertex-colouring with given precoloring.
 *
 * @param G The input graph
 * @param k Number of colors available
 * @param precolouring Map of vertices to their preassigned colors
 * @param opts Options for CNF construction
 * @return CNF formula that is satisfiable iff graph has a valid k-vertex-colouring, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_vertex_colouring(
    const Graph &G, int k, std::map<Vertex, int> precolouring, const ColouringCnfOptions &opts = {}
) {
    return build_vertex_colouring_cnf_encoding(G, k, std::move(precolouring), opts).cnf;
}

inline CNF cnf_vertex_colouring(const Graph &G, int k, const ColouringCnfOptions &opts = {}) {
    return build_vertex_colouring_cnf_encoding(G, k, opts).cnf;
}

namespace internal_colouring {

inline Location normalize_edge_colouring_location(const Location &loc) {
    if (loc.n1() < loc.n2()) {
        return loc;
    }
    return Location(loc.n2(), loc.n1(), loc.index());
}

inline std::map<Edge, Location> edge_to_primary_location_map(const Graph &G) {
    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    if (primary_edges.size() != primary_locations.size()) {
        throw std::runtime_error(
            "build_edge_colouring_cnf_encoding: primary edge and location list size mismatch"
        );
    }

    std::map<Edge, Location> edge_to_location;
    for (std::size_t i = 0; i < primary_edges.size(); ++i) {
        edge_to_location[primary_edges[i]] = primary_locations[i];
    }
    return edge_to_location;
}

inline std::map<Number, Location> build_line_vertex_to_location(
    const Graph &G, const std::map<Location, Number> &location_to_vertex
) {
    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    std::map<Number, Location> line_vertex_to_location;
    for (const auto &loc : primary_locations) {
        auto it = location_to_vertex.find(loc);
        if (it != location_to_vertex.end()) {
            line_vertex_to_location[it->second] = loc;
        }
    }

    if (line_vertex_to_location.size() != primary_locations.size()) {
        throw std::runtime_error(
            "build_edge_colouring_cnf_encoding: line_vertex_to_location does not cover all "
            "primary edges"
        );
    }
    std::set<Location> seen_locations;
    for (const auto &[v, loc] : line_vertex_to_location) {
        if (!seen_locations.insert(loc).second) {
            throw std::runtime_error(
                "build_edge_colouring_cnf_encoding: duplicate location in line_vertex_to_location"
            );
        }
    }
    return line_vertex_to_location;
}

inline void apply_parallel_edge_ordering(
    const Graph &G, VertexColouringCnfEncoding &line_encoding,
    const std::map<Number, Location> &line_vertex_to_location,
    const std::map<Number, int> &line_precolouring, const ColouringCnfOptions &opts
) {
    if (!opts.break_symmetry_by_ordering_parallel_edges || !has_parallel_edge(G)) {
        return;
    }

    std::map<Location, Number> location_to_vertex;
    for (const auto &[line_vertex, loc] : line_vertex_to_location) {
        location_to_vertex[normalize_edge_colouring_location(loc)] = line_vertex;
    }

    auto groups = parallel_edges(G);
    CnfBuilder builder(line_encoding.cnf);
    for (const auto &group : groups) {
        bool has_precoloured = false;
        for (const auto &loc : group) {
            auto norm_loc = normalize_edge_colouring_location(loc);
            auto it = location_to_vertex.find(norm_loc);
            if (it != location_to_vertex.end() && line_precolouring.count(it->second) > 0) {
                has_precoloured = true;
                break;
            }
        }
        if (has_precoloured) {
            continue;
        }

        std::vector<CnfVarList> group_vars;
        for (const auto &loc : group) {
            auto norm_loc = normalize_edge_colouring_location(loc);
            group_vars.push_back(line_encoding.vertex_colour_vars.at(location_to_vertex.at(norm_loc)
            ));
        }
        builder.add_ordering_chain_one_hot(group_vars, opts.parallel_edge_ordering_encoding);
    }
    line_encoding.cnf = builder.build("symmetry_broken_edge_colouring");
}

inline EdgeColouringCnfEncoding finish_edge_colouring_cnf_encoding(
    const Graph &G, VertexColouringCnfEncoding line_encoding,
    const std::map<Location, Number> &location_to_vertex,
    const std::map<Number, int> &line_precolouring, int k, const ColouringCnfOptions &opts
) {
    auto line_vertex_to_location = build_line_vertex_to_location(G, location_to_vertex);
    apply_parallel_edge_ordering(
        G, line_encoding, line_vertex_to_location, line_precolouring, opts
    );
    return {std::move(line_encoding), std::move(line_vertex_to_location), k};
}

}  // namespace internal_colouring

inline EdgeColouringCnfEncoding build_edge_colouring_cnf_encoding(
    const Graph &G, int k, std::map<Edge, int> precolouring, const ColouringCnfOptions &opts = {}
) {
    opts.validate("build_edge_colouring_cnf_encoding");
    if (k < 0) {
        throw std::invalid_argument("build_edge_colouring_cnf_encoding: k must be non-negative");
    }
    if (has_loop(G)) {
        std::map<Number, Location> empty_map;
        return {VertexColouringCnfEncoding{CNF::unsatisfiable(), {}, k}, std::move(empty_map), k};
    }
    if (k < max_deg(G)) {
        std::map<Number, Location> empty_map;
        return {VertexColouringCnfEncoding{CNF::unsatisfiable(), {}, k}, std::move(empty_map), k};
    }
    Factory f;
    auto [H, location_to_vertex] = line_graph_with_location_map(G, f);
    auto edge_to_location = internal_colouring::edge_to_primary_location_map(G);
    std::map<Vertex, int> lgPrecolouring;
    std::map<Number, int> line_precolouring;
    for (const auto &[e, c] : precolouring) {
        if (c < 0 || c >= k) {
            throw std::invalid_argument(
                "build_edge_colouring_cnf_encoding: precoloured edge has invalid colour "
                "(must be 0 <= colour < k)"
            );
        }
        auto loc_it = edge_to_location.find(e);
        if (loc_it == edge_to_location.end()) {
            throw std::invalid_argument("build_edge_colouring_cnf_encoding: edge not found in graph"
            );
        }
        Number line_vertex = location_to_vertex.at(loc_it->second);
        line_precolouring[line_vertex] = c;
        lgPrecolouring[H[line_vertex].v()] = c;
    }
    auto line_encoding = build_vertex_colouring_cnf_encoding(H, k, lgPrecolouring, opts);

    return internal_colouring::finish_edge_colouring_cnf_encoding(
        G, std::move(line_encoding), location_to_vertex, line_precolouring, k, opts
    );
}

inline EdgeColouringCnfEncoding build_edge_colouring_cnf_encoding(
    const Graph &G, int k, const ColouringCnfOptions &opts = {}
) {
    opts.validate("build_edge_colouring_cnf_encoding");
    if (k < 0) {
        throw std::invalid_argument("build_edge_colouring_cnf_encoding: k must be non-negative");
    }
    if (has_loop(G)) {
        std::map<Number, Location> empty_map;
        return {VertexColouringCnfEncoding{CNF::unsatisfiable(), {}, k}, std::move(empty_map), k};
    }
    Factory f;
    auto [H, location_to_vertex] = line_graph_with_location_map(G, f);
    auto edge_to_location = internal_colouring::edge_to_primary_location_map(G);
    std::map<Vertex, int> lgPrecolouring;
    std::map<Number, int> line_precolouring;
    if (opts.break_symmetry_by_precolouring) {
        int d = max_deg(G);
        if (k < d) {
            std::map<Number, Location> empty_map;
            return {
                VertexColouringCnfEncoding{CNF::unsatisfiable(), {}, k}, std::move(empty_map), k
            };
        }
        for (auto &r : G) {
            if (r.degree() == d) {
                int c = 0;
                for (auto &inc : r) {
                    auto loc_it = edge_to_location.find(inc.e());
                    if (loc_it == edge_to_location.end()) {
                        throw std::runtime_error(
                            "build_edge_colouring_cnf_encoding: incident edge has no primary "
                            "location"
                        );
                    }
                    auto it = location_to_vertex.find(loc_it->second);
                    if (it == location_to_vertex.end()) {
                        throw std::runtime_error(
                            "build_edge_colouring_cnf_encoding: incident edge not mapped in line "
                            "graph"
                        );
                    }
                    line_precolouring[it->second] = c;
                    lgPrecolouring[H[it->second].v()] = c++;
                }
                break;
            }
        }
    }
    auto line_encoding = build_vertex_colouring_cnf_encoding(H, k, lgPrecolouring, opts);

    return internal_colouring::finish_edge_colouring_cnf_encoding(
        G, std::move(line_encoding), location_to_vertex, line_precolouring, k, opts
    );
}

inline CNF cnf_edge_colouring(
    const Graph &G, int k, std::map<Edge, int> precolouring, const ColouringCnfOptions &opts = {}
) {
    if (k < 0) {
        throw std::invalid_argument("cnf_edge_colouring: k must be non-negative");
    }
    return build_edge_colouring_cnf_encoding(G, k, std::move(precolouring), opts)
        .line_graph_encoding.cnf;
}

inline CNF cnf_edge_colouring(const Graph &G, int k, const ColouringCnfOptions &opts = {}) {
    if (k < 0) {
        throw std::invalid_argument("cnf_edge_colouring: k must be non-negative");
    }
    return build_edge_colouring_cnf_encoding(G, k, opts).line_graph_encoding.cnf;
}

}  // namespace ba_graph

#endif
