#ifndef BA_GRAPH_SAT_CNF_CIRCULAR_COLOURING_HPP
#define BA_GRAPH_SAT_CNF_CIRCULAR_COLOURING_HPP

#include <algorithm>  // For std::sort
#include <cassert>
#include <limits>
#include <map>
#include <numeric>  // For std::gcd
#include <set>      // For std::set
#include <stdexcept>
#include <string>
#include <vector>

#include "algorithms/cycles.hpp"
#include "cnf.hpp"
#include "cnf_encoding.hpp"
#include "invariants/degree.hpp"
#include "invariants/girth.hpp"
#include "operations/line_graph.hpp"
#include "solution_types.hpp"

namespace ba_graph {

struct CircularColouringCnfOptions {
    int vertex_colour_sinz_threshold = CnfBuilder::DEFAULT_SINZ_THRESHOLD_AT_MOST_ONE;
    /**
     * Precolours the first vertex to colour 0 to break rotational symmetry,
     * and restricts its first neighbour to the lower half of the circle to
     * break reflectional symmetry.
     *
     * The raw CNF default is false: callers that add labelled constraints
     * above the base CNF, such as precolouring assumptions, may choose labels
     * that do not match this canonical representative. Decision SAT wrappers
     * may enable it explicitly when they own the full solving goal.
     */
    bool break_symmetry_by_precolouring = false;
    /**
     * If true, reduces the fraction p/q by std::gcd(p, q) before building
     * the CNF, which reduces the number of variables and clauses.
     *
     * The precolouring overloads force this to false because preassigned
     * colour labels refer to the unreduced circle.
     */
    bool reduce_fraction = true;
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

struct CircularVertexColouringCnfEncoding {
    CNF cnf;
    std::map<Number, CnfVarList> vertex_colour_vars;
    int requested_p;
    int requested_q;
    int encoded_p;
    int encoded_q;
    int colour_scale;

    sat_model::VertexColouring decode_model(const std::vector<bool> &model) const {
        validate_model_covers_vars(
            model, cnf.num_vars(), "CircularVertexColouringCnfEncoding::decode_model"
        );
        sat_model::VertexColouring colouring;
        for (const auto &[v, var_list] : vertex_colour_vars) {
            validate_var_list_size(
                var_list, static_cast<std::size_t>(encoded_p),
                "CircularVertexColouringCnfEncoding::decode_model"
            );
            int chosen = -1;
            for (int c = 0; c < encoded_p; ++c) {
                if (model.at(static_cast<std::size_t>(var_list[static_cast<std::size_t>(c)]))) {
                    if (chosen != -1) {
                        throw std::runtime_error(
                            "CircularVertexColouringCnfEncoding::decode_model: "
                            "multiple colours assigned to vertex"
                        );
                    }
                    chosen = c;
                }
            }
            if (chosen == -1) {
                throw std::runtime_error(
                    "CircularVertexColouringCnfEncoding::decode_model: "
                    "missing colour assignment for vertex"
                );
            }
            colouring[v] = chosen * colour_scale;
        }
        return colouring;
    }
};

struct CircularEdgeColouringCnfEncoding {
    CircularVertexColouringCnfEncoding line_graph_encoding;
    std::map<Number, Location> line_vertex_to_location;

    sat_model::EdgeColouring decode_model(const std::vector<bool> &model) const {
        sat_model::VertexColouring line_colouring = line_graph_encoding.decode_model(model);
        sat_model::EdgeColouring colouring;
        for (const auto &[line_vertex, loc] : line_vertex_to_location) {
            auto it = line_colouring.find(line_vertex);
            if (it == line_colouring.end()) {
                throw std::runtime_error(
                    "CircularEdgeColouringCnfEncoding::decode_model: "
                    "line graph vertex not mapped"
                );
            }
            colouring[loc] = it->second;
        }
        if (static_cast<int>(colouring.size()) !=
            static_cast<int>(line_vertex_to_location.size())) {
            throw std::runtime_error(
                "CircularEdgeColouringCnfEncoding::decode_model: "
                "incomplete edge colouring model"
            );
        }
        return colouring;
    }
};

// distance between colours along the circle of length p
inline int circular_distance(int p, int c1, int c2) {
    int cc1 = std::min(c1, c2), cc2 = std::max(c1, c2);
    return std::min(cc2 - cc1, cc1 + p - cc2);
}

namespace internal {

struct CircularVertexColouringBase {
    CNF cnf;
    std::map<Number, CnfVarList> vars;
    std::vector<Number> vertex_sequence;
    bool is_fully_constructed = false;
};

inline void validate_circular_colouring_parameters(int p, int q, const char *function_name) {
    if (p < 0) {
        throw std::invalid_argument(std::string(function_name) + ": p must be non-negative");
    }
    if (q <= 0) {
        throw std::invalid_argument(std::string(function_name) + ": q must be positive");
    }
}

inline CircularVertexColouringBase build_circular_vertex_colouring_base_cnf(
    const Graph &G, int p, int q, const std::map<Vertex, int> &precolouring,
    const CircularColouringCnfOptions &opts
) {
    CircularVertexColouringBase base;
    validate_circular_colouring_parameters(p, q, "build_circular_vertex_colouring_base_cnf");
    for (const auto &[v, c] : precolouring) {
        if (c < 0) {
            throw std::invalid_argument(
                "cnf_circular_vertex_colouring: precoloured vertex colour must be non-negative"
            );
        }
        if (c >= p) {
            throw std::invalid_argument(
                "cnf_circular_vertex_colouring: precoloured vertex colour must be less than p"
            );
        }
        if (!G.contains(v)) {
            throw std::invalid_argument(
                "cnf_circular_vertex_colouring: precoloured vertex not found in graph"
            );
        }
    }
    if (p == 0) {
        base.cnf = G.order() == 0 ? CNF::satisfiable() : CNF::unsatisfiable();
        base.is_fully_constructed = true;
        return base;
    }

    if (q > p || has_loop(G)) {
        base.cnf = CNF::unsatisfiable();
        base.is_fully_constructed = true;
        return base;
    }
    if ((q == p) && (G.size() > 0)) {
        base.cnf = CNF::unsatisfiable();
        base.is_fully_constructed = true;
        return base;
    }
    if ((G.size() > 0) && (p < 2 * q)) {
        base.cnf = CNF::unsatisfiable();
        base.is_fully_constructed = true;
        return base;
    }
    if (G.order() > std::numeric_limits<int>::max() / p) {
        // LCOV_EXCL_START — requires impossibly large graph to trigger
        throw std::overflow_error(
            "build_circular_vertex_colouring_base_cnf: variable count overflows int"
        );
        // LCOV_EXCL_STOP
    }

    CnfBuilder builder;
    std::map<Number, CnfVarList> vars;
    for (auto &r : G) {
        CnfVarList v = builder.new_vars(p);
        vars.emplace(r.n(), std::move(v));
        base.vertex_sequence.push_back(r.n());
    }

    for (auto &r : G) {
        const int NO_COLOUR = -1;
        auto preIt = precolouring.find(r.v());
        int preC = NO_COLOUR;
        if (preIt != precolouring.end()) {
            preC = preIt->second;
        }

        if (preC != NO_COLOUR) {
            for (int c = 0; c < p; ++c) {
                if (c == preC) {
                    builder.add_clause({builder.lit(vars[r.n()][c])});
                } else {
                    builder.add_clause({builder.not_lit(vars[r.n()][c])});
                }
            }
        } else {
            builder.add_exactly_one(vars[r.n()], opts.vertex_colour_sinz_threshold);
        }

        Number v1 = r.n();
        int v1_precolour = preC;
        for (auto &edge_iter : r) {
            Number v2 = edge_iter.n2();
            if (v2 <= v1) {
                continue;
            }
            auto v2preIt = precolouring.find(edge_iter.v2());
            int v2_precolour = NO_COLOUR;
            if (v2preIt != precolouring.end()) {
                v2_precolour = v2preIt->second;
            }

            if (v1_precolour != NO_COLOUR && v2_precolour != NO_COLOUR) {
                if (circular_distance(p, preC, v2_precolour) < q) {
                    base.cnf = CNF::unsatisfiable();
                    base.is_fully_constructed = true;
                    return base;
                }
                continue;
            }

            for (int c1 = 0; c1 < p; ++c1) {
                if (v1_precolour != NO_COLOUR && c1 != v1_precolour) {
                    continue;
                }
                for (int c2 = 0; c2 < p; ++c2) {
                    if (v2_precolour != NO_COLOUR && c2 != v2_precolour) {
                        continue;
                    }

                    if (circular_distance(p, c1, c2) < q) {
                        if (v1_precolour != NO_COLOUR) {
                            builder.add_clause({builder.not_lit(vars[v2][c2])});
                        } else if (v2_precolour != NO_COLOUR) {
                            builder.add_clause({builder.not_lit(vars[v1][c1])});
                        } else {
                            builder.add_clause(
                                {builder.not_lit(vars[v1][c1]), builder.not_lit(vars[v2][c2])}
                            );
                        }
                    }
                }
            }
        }
    }

    base.cnf = builder.build("build_circular_vertex_colouring_base_cnf");
    if (base.vertex_sequence.empty()) {
        base.is_fully_constructed = true;
    }
    base.vars = std::move(vars);
    return base;
}

}  // namespace internal

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring with given precoloring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of vertices to their preassigned colors
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-vertex-colouring, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_vertex_colouring(
    const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    opts.validate("cnf_circular_vertex_colouring");
    CircularColouringCnfOptions forced_opts = opts;
    forced_opts.reduce_fraction = false;
    auto base =
        internal::build_circular_vertex_colouring_base_cnf(G, p, q, precolouring, forced_opts);
    return base.cnf;
}

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring.
 *
 * Symmetry breaking (controlled by opts.break_symmetry_by_precolouring)
 * fixes the first vertex to colour 0 and restricts its first neighbour
 * to the lower half of the circle.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param opts Options for CNF construction
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-vertex-colouring, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_vertex_colouring(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(p, q, "cnf_circular_vertex_colouring");
    opts.validate("cnf_circular_vertex_colouring");
    if (opts.reduce_fraction) {
        int d = std::gcd(p, q);
        p /= d;
        q /= d;
    }

    auto base = internal::build_circular_vertex_colouring_base_cnf(G, p, q, {}, opts);
    if (base.is_fully_constructed) {
        return base.cnf;
    }

    if (opts.break_symmetry_by_precolouring) {
        auto &vars = base.vars;
        Number v0 = base.vertex_sequence[0];
        CnfBuilder builder(base.cnf);
        builder.add_clause({builder.lit(vars[v0][0])});

        bool neighbor_found = false;
        Number v1;

        for (const auto &node : G) {
            if (node.n() == v0) {
                const auto &neighs = node.neighbours();
                if (!neighs.empty()) {
                    v1 = *neighs.begin();
                    neighbor_found = true;
                }
                break;
            }
        }

        if (neighbor_found) {
            int limit = p / 2;
            for (int c = limit + 1; c < p; ++c) {
                builder.add_clause({builder.not_lit(vars[v1][c])});
            }
        }

        return builder.build("cnf_circular_vertex_colouring");
    }

    return base.cnf;
}

inline CircularVertexColouringCnfEncoding build_circular_vertex_colouring_cnf_encoding(
    const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    opts.validate("build_circular_vertex_colouring_cnf_encoding");
    CircularColouringCnfOptions forced_opts = opts;
    forced_opts.reduce_fraction = false;
    auto base =
        internal::build_circular_vertex_colouring_base_cnf(G, p, q, precolouring, forced_opts);
    for (const auto &[v, var_list] : base.vars) {
        validate_var_list_in_cnf(
            var_list, base.cnf.num_vars(), static_cast<std::size_t>(p),
            "build_circular_vertex_colouring_cnf_encoding"
        );
    }
    return {base.cnf, std::move(base.vars), p, q, p, q, 1};
}

inline CircularVertexColouringCnfEncoding build_circular_vertex_colouring_cnf_encoding(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "build_circular_vertex_colouring_cnf_encoding"
    );
    opts.validate("build_circular_vertex_colouring_cnf_encoding");
    int requested_p = p, requested_q = q;
    int colour_scale = 1;
    if (opts.reduce_fraction) {
        colour_scale = std::gcd(p, q);
        p /= colour_scale;
        q /= colour_scale;
    }

    auto base = internal::build_circular_vertex_colouring_base_cnf(G, p, q, {}, opts);
    if (base.is_fully_constructed) {
        return {base.cnf, std::move(base.vars), requested_p, requested_q, p, q, colour_scale};
    }

    if (opts.break_symmetry_by_precolouring) {
        auto &vars = base.vars;
        Number v0 = base.vertex_sequence[0];
        CnfBuilder builder(base.cnf);
        builder.add_clause({builder.lit(vars[v0][0])});

        Number v1;
        bool neighbor_found = false;
        for (const auto &node : G) {
            if (node.n() == v0) {
                const auto &neighs = node.neighbours();
                if (!neighs.empty()) {
                    v1 = *neighs.begin();
                    neighbor_found = true;
                }
                break;
            }
        }

        if (neighbor_found) {
            int limit = p / 2;
            for (int c = limit + 1; c < p; ++c) {
                builder.add_clause({builder.not_lit(vars[v1][c])});
            }
        }

        auto cnf = builder.build("build_circular_vertex_colouring_cnf_encoding");
        for (const auto &[v, var_list] : vars) {
            validate_var_list_in_cnf(
                var_list, cnf.num_vars(), static_cast<std::size_t>(p),
                "build_circular_vertex_colouring_cnf_encoding"
            );
        }
        return {std::move(cnf), std::move(vars), requested_p, requested_q, p, q, colour_scale};
    }

    for (const auto &[v, var_list] : base.vars) {
        validate_var_list_in_cnf(
            var_list, base.cnf.num_vars(), static_cast<std::size_t>(p),
            "build_circular_vertex_colouring_cnf_encoding"
        );
    }
    return {base.cnf, std::move(base.vars), requested_p, requested_q, p, q, colour_scale};
}

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring without tight cycles.
 *
 * Options control symmetry breaking and whether p/q is reduced before construction.
 * The precolouring overload below keeps the requested colours exactly and therefore
 * forces fraction reduction off.
 */
inline CNF cnf_circular_vertex_colouring_without_tight_cycles_impl(
    const Graph &G, int p, int q, const std::map<Vertex, int> &precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "cnf_circular_vertex_colouring_without_tight_cycles"
    );
    opts.validate("cnf_circular_vertex_colouring_without_tight_cycles_impl");
    if (opts.reduce_fraction) {
        int d = std::gcd(p, q);
        p /= d;
        q /= d;
    } else if (std::gcd(p, q) != 1) {
        throw std::invalid_argument(
            "cnf_circular_vertex_colouring_without_tight_cycles_impl: p and q must be coprime "
            "when fraction reduction is disabled"
        );
    }

    auto base = internal::build_circular_vertex_colouring_base_cnf(G, p, q, precolouring, opts);
    if (base.is_fully_constructed) {
        return base.cnf;
    }

    CnfBuilder builder(base.cnf);
    auto &vars = base.vars;
    auto &vertex_sequence = base.vertex_sequence;

    if (opts.break_symmetry_by_precolouring) {
        Number v0 = vertex_sequence[0];
        builder.add_clause({builder.lit(vars[v0][0])});

        bool neighbor_found = false;
        Number v1;
        for (const auto &node : G) {
            if (node.n() == v0) {
                const auto &neighs = node.neighbours();
                if (!neighs.empty()) {
                    v1 = *neighs.begin();
                    neighbor_found = true;
                }
                break;
            }
        }
        if (neighbor_found) {
            int limit = p / 2;
            for (int c = limit + 1; c < p; ++c) {
                builder.add_clause({builder.not_lit(vars[v1][c])});
            }
        }
    }

    if (G.order() < 3) {
        return builder.build("cnf_circular_vertex_colouring_without_tight_cycles_impl");
    }

    if (p == 0) {
        // LCOV_EXCL_START -- p==0 is already handled by the upstream
        // build_circular_vertex_colouring_base_cnf (is_fully_constructed);
        // this guards against direct calls bypassing that check
        throw std::invalid_argument(
            "cnf_circular_vertex_colouring_without_tight_cycles_impl: p cannot be zero"
        );
        // LCOV_EXCL_STOP
    }

    // A tight cycle in a circular (p,q)-colouring is a cycle whose consecutive
    // colours all advance by the same tight distance, either +q or -q modulo p.
    // This implementation checks circuits whose length is divisible by p. The
    // parameter validation above ensures gcd(p, q) == 1 here, so those are
    // exactly the circuit lengths that can realize a full return to the starting
    // colour under repeated +/-q steps. For each such circuit, each starting
    // colour s, and each orientation step q or -q, add one clause that forbids
    // the exact arithmetic progression
    //     s, s + step, s + 2 * step, ...
    // on that ordered circuit.
    int step1 = ((q % p) + p) % p;
    int step2 = (p - step1) % p;

    std::set<Circuit> circuits = all_circuits_mod(G, p);

    auto forbid_patterns_for_step = [&](int step) {
        // LCOV_EXCL_START -- step is always non-zero:
        // step1 = q % p = q > 0, step2 = p - q > 0 (since 0 < q < p)
        if (step == 0) {
            throw std::runtime_error(
                "cnf_circular_vertex_colouring_without_tight_cycles_impl: "
                "internal invariant violated, step is zero"
            );
        }
        // LCOV_EXCL_STOP
        for (const Circuit &C : circuits) {
            std::vector<Number> vs = C.vertices();
            int k = static_cast<int>(vs.size());
            if (k == 0) {
                // LCOV_EXCL_START -- all_circuits_mod never produces empty circuits
                throw std::runtime_error(
                    "cnf_circular_vertex_colouring_without_tight_cycles_impl: "
                    "internal invariant violated, encountered empty circuit"
                );
                // LCOV_EXCL_STOP
            }

            for (int s = 0; s < p; ++s) {
                Clause clause;
                clause.reserve(k);
                for (int i = 0; i < k; ++i) {
                    Number vnum = vs[i];
                    long long tmp = static_cast<long long>(s) +
                                    static_cast<long long>(i) * static_cast<long long>(step);
                    int col = static_cast<int>(tmp % p);
                    int xidx = vars[vnum][col];
                    clause.emplace_back(xidx, true);
                }
                builder.add_clause(std::move(clause));
            }
        }
    };

    forbid_patterns_for_step(step1);
    if (step2 != step1) {
        forbid_patterns_for_step(step2);
    }

    return builder.build("cnf_circular_vertex_colouring_without_tight_cycles_impl");
}

inline CNF cnf_circular_vertex_colouring_without_tight_cycles(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    return cnf_circular_vertex_colouring_without_tight_cycles_impl(
        G, p, q, std::map<Vertex, int>{}, opts
    );
}

inline CNF cnf_circular_vertex_colouring_without_tight_cycles(
    const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    CircularColouringCnfOptions forced_opts = opts;
    forced_opts.reduce_fraction = false;
    return cnf_circular_vertex_colouring_without_tight_cycles_impl(
        G, p, q, precolouring, forced_opts
    );
}

// forward declarations for build_circular_edge_colouring_cnf_encoding
inline CircularEdgeColouringCnfEncoding build_circular_edge_colouring_cnf_encoding(
    const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts
);
inline CircularEdgeColouringCnfEncoding build_circular_edge_colouring_cnf_encoding(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts
);

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring with given precoloring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of edges to their preassigned colors
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_edge_colouring(
    const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(p, q, "cnf_circular_edge_colouring");
    return build_circular_edge_colouring_cnf_encoding(G, p, q, std::move(precolouring), opts)
        .line_graph_encoding.cnf;
}

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring.
 *
 * Symmetry breaking (controlled by opts.break_symmetry_by_precolouring)
 * delegates to the vertex-colouring CNF.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param opts Options for CNF construction
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring, or
 * CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_edge_colouring(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(p, q, "cnf_circular_edge_colouring");
    return build_circular_edge_colouring_cnf_encoding(G, p, q, opts).line_graph_encoding.cnf;
}

inline CircularEdgeColouringCnfEncoding build_circular_edge_colouring_cnf_encoding(
    const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "build_circular_edge_colouring_cnf_encoding"
    );
    opts.validate("build_circular_edge_colouring_cnf_encoding");
    if (has_loop(G)) {
        std::map<Number, Location> empty_map;
        return {
            CircularVertexColouringCnfEncoding{CNF::unsatisfiable(), {}, p, q, p, q, 1},
            std::move(empty_map)
        };
    }
    Factory f;
    auto [H, locationToVertex] = line_graph_with_location_map(G, f);
    std::map<Vertex, int> lgPrecolouring;
    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    for (const auto &[e, c] : precolouring) {
        if (std::find(primary_edges.begin(), primary_edges.end(), e) == primary_edges.end()) {
            throw std::invalid_argument(
                "build_circular_edge_colouring_cnf_encoding: "
                "precoloured edge not found in graph"
            );
        }
    }
    for (std::size_t i = 0; i < primary_edges.size(); ++i) {
        Edge e = primary_edges[i];
        if (precolouring.count(e) > 0) {
            int edge_colour = precolouring[e];
            if (edge_colour < 0 || edge_colour >= p) {
                throw std::invalid_argument(
                    "build_circular_edge_colouring_cnf_encoding: "
                    "precoloured edge colour must be in [0, p)"
                );
            }
            auto it = locationToVertex.find(primary_locations[i]);
            if (it == locationToVertex.end()) {
                throw std::invalid_argument(
                    "build_circular_edge_colouring_cnf_encoding: "
                    "primary location not mapped"
                );
            }
            lgPrecolouring[H[it->second].v()] = edge_colour;
        }
    }
    auto vertex_encoding =
        build_circular_vertex_colouring_cnf_encoding(H, p, q, lgPrecolouring, opts);

    std::map<Number, Location> line_vertex_to_location;
    for (std::size_t i = 0; i < primary_edges.size(); ++i) {
        auto edgeIt = locationToVertex.find(primary_locations[i]);
        if (edgeIt != locationToVertex.end()) {
            Number v = edgeIt->second;
            line_vertex_to_location[v] = primary_locations[i];
        }
    }

    if (line_vertex_to_location.size() != primary_locations.size()) {
        throw std::runtime_error(
            "build_circular_edge_colouring_cnf_encoding: line_vertex_to_location"
            " does not cover all primary edges"
        );
    }
    std::set<Location> seen;
    for (const auto &[v, loc] : line_vertex_to_location) {
        if (!seen.insert(loc).second) {
            throw std::runtime_error(
                "build_circular_edge_colouring_cnf_encoding:"
                " duplicate location in line_vertex_to_location"
            );
        }
    }

    if (opts.break_symmetry_by_ordering_parallel_edges && has_parallel_edge(G)) {
        auto normalize_loc = [](const Location &l) -> Location {
            if (l.n1() < l.n2()) {
                return l;
            }
            return Location(l.n2(), l.n1(), l.index());
        };
        std::map<Location, Number> locToVertex;
        for (const auto &[lv, loc] : line_vertex_to_location) {
            locToVertex[normalize_loc(loc)] = lv;
        }
        auto groups = parallel_edges(G);
        CnfBuilder builder(vertex_encoding.cnf);
        for (const auto &group : groups) {
            bool has_precoloured = false;
            for (const auto &loc : group) {
                auto norm_loc = normalize_loc(loc);
                auto it = locToVertex.find(norm_loc);
                if (it != locToVertex.end() && lgPrecolouring.count(H[it->second].v())) {
                    has_precoloured = true;
                    break;
                }
            }
            if (has_precoloured) {
                continue;
            }
            std::vector<CnfVarList> group_vars;
            for (const auto &loc : group) {
                auto norm_loc = normalize_loc(loc);
                group_vars.push_back(vertex_encoding.vertex_colour_vars.at(locToVertex.at(norm_loc))
                );
            }
            builder.add_ordering_chain_one_hot(group_vars, opts.parallel_edge_ordering_encoding);
        }
        vertex_encoding.cnf = builder.build("symmetry_broken_circular_edge_colouring");
    }

    return {std::move(vertex_encoding), std::move(line_vertex_to_location)};
}

inline CircularEdgeColouringCnfEncoding build_circular_edge_colouring_cnf_encoding(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "build_circular_edge_colouring_cnf_encoding"
    );
    opts.validate("build_circular_edge_colouring_cnf_encoding");
    if (has_loop(G)) {
        std::map<Number, Location> empty_map;
        return {
            CircularVertexColouringCnfEncoding{CNF::unsatisfiable(), {}, p, q, p, q, 1},
            std::move(empty_map)
        };
    }
    Factory f;
    auto [H, locationToVertex] = line_graph_with_location_map(G, f);
    auto vertex_encoding = build_circular_vertex_colouring_cnf_encoding(H, p, q, opts);

    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    std::map<Number, Location> line_vertex_to_location;
    for (std::size_t i = 0; i < primary_edges.size(); ++i) {
        auto edgeIt = locationToVertex.find(primary_locations[i]);
        if (edgeIt != locationToVertex.end()) {
            Number v = edgeIt->second;
            line_vertex_to_location[v] = primary_locations[i];
        }
    }

    if (line_vertex_to_location.size() != primary_locations.size()) {
        throw std::runtime_error(
            "build_circular_edge_colouring_cnf_encoding: line_vertex_to_location"
            " does not cover all primary edges"
        );
    }
    std::set<Location> seen;
    for (const auto &[v, loc] : line_vertex_to_location) {
        if (!seen.insert(loc).second) {
            throw std::runtime_error(
                "build_circular_edge_colouring_cnf_encoding:"
                " duplicate location in line_vertex_to_location"
            );
        }
    }

    if (opts.break_symmetry_by_ordering_parallel_edges && has_parallel_edge(G)) {
        auto normalize_loc = [](const Location &l) -> Location {
            if (l.n1() < l.n2()) {
                return l;
            }
            return Location(l.n2(), l.n1(), l.index());
        };
        std::map<Location, Number> locToVertex;
        for (const auto &[lv, loc] : line_vertex_to_location) {
            locToVertex[normalize_loc(loc)] = lv;
        }
        auto groups = parallel_edges(G);
        CnfBuilder builder(vertex_encoding.cnf);
        for (const auto &group : groups) {
            std::vector<CnfVarList> group_vars;
            for (const auto &loc : group) {
                auto norm_loc = normalize_loc(loc);
                group_vars.push_back(vertex_encoding.vertex_colour_vars.at(locToVertex.at(norm_loc))
                );
            }
            builder.add_ordering_chain_one_hot(group_vars, opts.parallel_edge_ordering_encoding);
        }
        vertex_encoding.cnf = builder.build("symmetry_broken_circular_edge_colouring");
    }

    return {std::move(vertex_encoding), std::move(line_vertex_to_location)};
}

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring without tight cycles, with given
 * precoloring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of edges to their preassigned colors
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring
 * without tight cycles, or CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_edge_colouring_without_tight_cycles(
    const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "cnf_circular_edge_colouring_without_tight_cycles"
    );
    opts.validate("cnf_circular_edge_colouring_without_tight_cycles");
    if (has_loop(G)) {
        return CNF::unsatisfiable();
    }
    Factory f;
    auto [H, locationToVertex] = line_graph_with_location_map(G, f);
    std::map<Vertex, int> lgPrecolouring;
    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    if (primary_edges.size() != primary_locations.size()) {
        throw std::invalid_argument(
            "cnf_circular_edge_colouring_without_tight_cycles: primary edge/location list size "
            "mismatch"
        );
    }
    for (std::size_t i = 0; i < primary_edges.size(); ++i) {
        Edge e = primary_edges[i];
        if (precolouring.count(e) > 0) {
            int edge_colour = precolouring[e];
            if (edge_colour < 0) {
                throw std::invalid_argument(
                    "cnf_circular_edge_colouring_without_tight_cycles: precoloured edge colour "
                    "must be non-negative"
                );
            }
            if (edge_colour >= p) {
                throw std::invalid_argument(
                    "cnf_circular_edge_colouring_without_tight_cycles: precoloured edge colour "
                    "must be less than p"
                );
            }
            auto it = locationToVertex.find(primary_locations[i]);
            if (it == locationToVertex.end()) {
                throw std::invalid_argument(
                    "cnf_circular_edge_colouring_without_tight_cycles: primary location not mapped"
                );
            }
            lgPrecolouring[H[it->second].v()] = edge_colour;
        }
    }
    return cnf_circular_vertex_colouring_without_tight_cycles(H, p, q, lgPrecolouring, opts);
}

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring without tight cycles.
 *
 * Symmetry breaking (controlled by opts.break_symmetry_by_precolouring)
 * delegates to the vertex-colouring-without-tight-cycles CNF.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param opts Options for CNF construction
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring
 * without tight cycles, or CNF::unsatisfiable() if graph contains loops
 */
inline CNF cnf_circular_edge_colouring_without_tight_cycles(
    const Graph &G, int p, int q, const CircularColouringCnfOptions &opts = {}
) {
    opts.validate("cnf_circular_edge_colouring_without_tight_cycles");
    if (has_loop(G)) {
        return CNF::unsatisfiable();
    }
    Factory f;
    Graph H = line_graph(G, f);
    return cnf_circular_vertex_colouring_without_tight_cycles(H, p, q, opts);
}

namespace internal {

/**
 * @brief Computes a sorted list of unique, irreducible fractions p/q within the described
 * limitations.
 *
 * The bounds describe lb <= p/q <= ub. For a fixed p, this gives
 * p/ub <= q <= p/lb; the explicit cross-multiplied checks below handle
 * integer rounding and open endpoints. Fractions are reduced before insertion
 * so equivalent candidates are deduplicated, then sorted by cross
 * multiplication to avoid floating point comparisons.
 *
 * @param max_p Maximum value of p.
 * @param lower_bound Minimum value of p/q.
 * @param upper_bound Maximum value of p/q.
 * @param include_lb Whether to include p/q with value equal to lower_bound.
 * @param include_ub Whether to include p/q with value equal to upper_bound.
 * @return A vector of pairs {p, q} representing the sorted candidate fractions.
 */
inline std::vector<std::pair<int, int>> computeCircularColouringFractions(
    int max_p, int lower_bound, int upper_bound, bool include_lb, bool include_ub
) {
    int ub = upper_bound;
    int lb = lower_bound;
    if (lb <= 0) {
        throw std::invalid_argument("computeCircularColouringFractions(): illegal argument lb");
    }
    if (ub < lb) {
        throw std::invalid_argument("computeCircularColouringFractions(): up < lb");
    }
    std::set<std::pair<int, int>> fractions;
    for (int p = 1; p <= max_p; ++p) {
        for (int q = std::max(1, p / ub); q <= p / lb; ++q) {
            // check if lb <= p/q <= ub
            if (!(static_cast<long long>(lb) * q <= p) || !(p <= static_cast<long long>(ub) * q)) {
                continue;
            }
            if (!include_lb && static_cast<long long>(lb) * q == p) {
                continue;
            }
            if (!include_ub && static_cast<long long>(ub) * q == p) {
                continue;
            }
            // reduce p/q using std::gcd
            int d = std::gcd(p, q);
            fractions.insert({p / d, q / d});
        }
    }

    std::vector<std::pair<int, int>> sortedFractions(fractions.begin(), fractions.end());
    std::sort(
        sortedFractions.begin(), sortedFractions.end(),
        [](const std::pair<int, int> &f1, const std::pair<int, int> &f2) {
            // Compare f1.first/f1.second < f2.first/f2.second as f1.first * f2.second <
            // f2.first * f1.second Use long long for products to prevent overflow.
            return static_cast<long long>(f1.first) * f2.second <
                   static_cast<long long>(f2.first) * f1.second;
        }
    );

    return sortedFractions;
}

}  // namespace internal

}  // namespace ba_graph

#endif
