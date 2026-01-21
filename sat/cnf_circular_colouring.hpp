#ifndef BA_GRAPH_SAT_CNF_CIRCULAR_COLOURING_HPP
#define BA_GRAPH_SAT_CNF_CIRCULAR_COLOURING_HPP

#include <algorithm>  // For std::sort
#include <cassert>
#include <map>
#include <numeric>  // For std::gcd
#include <set>      // For std::set
#include <vector>

#include "../algorithms/cycles.hpp"
#include "../invariants/degree.hpp"
#include "../invariants/girth.hpp"
#include "../operations/line_graph.hpp"
#include "cnf.hpp"

namespace ba_graph {

// distance between colours along the circle of length p
inline int circular_distance(int p, int c1, int c2) {
    int cc1 = std::min(c1, c2), cc2 = std::max(c1, c2);
    return std::min(cc2 - cc1, cc1 + p - cc2);
}

namespace internal {

struct CircularVertexColouringBase {
    CNF cnf;
    std::map<Number, std::vector<int>> vars;
    std::vector<Number> vertex_sequence;
};

inline CNF make_unsatisfiable_cnf(int varcount) {
    CNF result = cnf_unsatisfiable;
    result.first = std::max(varcount, 1);
    return result;
}

inline CircularVertexColouringBase build_circular_vertex_colouring_base_cnf(
    const Graph &G, int p, int q, const std::map<Vertex, int> &precolouring
) {
    CircularVertexColouringBase base;
    auto &clauses = base.cnf.second;
    clauses.reserve(p * p * G.order());
    int nextVar = 0;
    if (p == 0) {
        if (G.order() == 0) {
            base.cnf = cnf_satisfiable;
            return base;
        }
        base.cnf = make_unsatisfiable_cnf(nextVar);
        return base;
    }

    if (q <= 0 || q > p) {
        base.cnf = make_unsatisfiable_cnf(nextVar);
        return base;
    }

    if (has_loop(G)) {
        base.cnf = make_unsatisfiable_cnf(nextVar);
        return base;
    }
    std::map<Number, std::vector<int>> vars;
    for (auto &r : G) {
        std::vector<int> v(p);
        for (int i = 0; i < p; ++i) {
            v[i] = nextVar++;
        }
        vars.emplace(r.n(), std::move(v));
        base.vertex_sequence.push_back(r.n());
    }

    for (auto &r : G) {
        const int NO_COLOUR = -1;
        auto preIt = precolouring.find(r.v());
        int preC = (preIt != precolouring.end()) ? preIt->second : NO_COLOUR;
        if (preC != NO_COLOUR) {
            assert(preC < p);
            assert(preC >= 0);
        }

        if (preC != NO_COLOUR) {
            for (int c = 0; c < p; ++c) {
                if (c == preC) {
                    clauses.push_back({Lit(vars[r.n()][c], false)});
                } else {
                    clauses.push_back({Lit(vars[r.n()][c], true)});
                }
            }
        } else {
            std::vector<int> vertex_colour_vars;
            vertex_colour_vars.reserve(p);
            for (int c = 0; c < p; ++c) {
                vertex_colour_vars.push_back(vars[r.n()][c]);
            }
            clause_exactly_one(clauses, vertex_colour_vars);
        }

        Number v1 = r.n();
        int v1_precolour = preC;
        for (auto &edge_iter : r) {
            Number v2 = edge_iter.n2();
            if (v2 <= v1) {
                continue;
            }
            auto v2preIt = precolouring.find(edge_iter.v2());
            int v2_precolour = (v2preIt != precolouring.end()) ? v2preIt->second : NO_COLOUR;

            if (v1_precolour != NO_COLOUR && v2_precolour != NO_COLOUR) {
                if (circular_distance(p, preC, v2_precolour) < q) {
                    base.cnf = make_unsatisfiable_cnf(nextVar);
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
                            clauses.push_back({Lit(vars[v2][c2], true)});
                        } else if (v2_precolour != NO_COLOUR) {
                            clauses.push_back({Lit(vars[v1][c1], true)});
                        } else {
                            clauses.push_back({Lit(vars[v1][c1], true), Lit(vars[v2][c2], true)});
                        }
                    }
                }
            }
        }
    }

    base.cnf.first = nextVar;
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
 * cnf_unsatisfiable if graph contains loops
 */
inline CNF cnf_circular_vertex_colouring(
    const Graph &G, int p, int q, std::map<Vertex, int> precolouring
) {
    auto base = internal::build_circular_vertex_colouring_base_cnf(G, p, q, precolouring);
    return base.cnf;
}

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolour Whether to precolor some vertices to break symmetry
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-vertex-colouring, or
 * cnf_unsatisfiable if graph contains loops
 */
inline CNF cnf_circular_vertex_colouring(const Graph &G, int p, int q, bool precolour = false) {
    if (p == 0) return cnf_unsatisfiable;
    int d = std::gcd(p, q);
    p /= d;
    q /= d;

    auto base = internal::build_circular_vertex_colouring_base_cnf(G, p, q, {});
    if (base.cnf.second == cnf_unsatisfiable.second) return base.cnf;
    if (base.vertex_sequence.empty()) return base.cnf;

    if (precolour) {
        auto &clauses = base.cnf.second;
        auto &vars = base.vars;
        Number v0 = base.vertex_sequence[0];
        clauses.push_back({Lit(vars[v0][0], false)});

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
                clauses.push_back({Lit(vars[v1][c], true)});
            }
        }
    }

    return base.cnf;
}

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring with a tight cycle constraint.
 *
 * Checks if there exists a (p,q)-colouring that is "tight" on at least one cycle
 * in the graph. This is often used for testing circular criticality.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolour Whether to precolor the first vertex to break symmetry
 * @return CNF formula that is satisfiable iff such a colouring exists
 */
inline CNF cnf_circular_vertex_colouring_without_tight_cycles(
    const Graph &G, int p, int q, bool precolour
) {
    if (p == 0) return cnf_unsatisfiable;
    int d = std::gcd(p, q);
    p /= d;
    q /= d;

    auto base =
        internal::build_circular_vertex_colouring_base_cnf(G, p, q, std::map<Vertex, int>{});
    if (base.cnf.second == cnf_unsatisfiable.second) {
        return base.cnf;
    }
    if (base.vertex_sequence.empty()) {
        return base.cnf;
    }
    auto &clauses = base.cnf.second;
    auto &vars = base.vars;
    auto &vertex_sequence = base.vertex_sequence;

    if (precolour) {
        Number v0 = vertex_sequence[0];
        int var0 = vars[v0][0];
        clauses.push_back({Lit(var0, false)});

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
                clauses.push_back({Lit(vars[v1][c], true)});
            }
        }
    }

    int step1 = ((q % p) + p) % p;
    int step2 = (p - step1) % p;

    std::set<Circuit> circuits = all_circuits_mod(G, p);

    auto forbid_patterns_for_step = [&](int step) {
        if (step == 0) {
            return;
        }
        for (const Circuit &C : circuits) {
            std::vector<Number> vs = C.vertices();
            int k = static_cast<int>(vs.size());
            if (k == 0) {
                continue;
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
                clauses.push_back(std::move(clause));
            }
        }
    };

    forbid_patterns_for_step(step1);
    forbid_patterns_for_step(step2);

    return base.cnf;
}

/**
 * @brief Generates CNF formula for circular (p,q)-vertex-colouring with a tight cycle constraint.
 *
 * @param G The input graph
 * @param p Circle length
 * @param q Minimum circular distance
 * @return CNF formula
 */
inline CNF cnf_circular_vertex_colouring_without_tight_cycles(const Graph &G, int p, int q) {
    return cnf_circular_vertex_colouring_without_tight_cycles(G, p, q, true);
}

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring with given precoloring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of edges to their preassigned colors
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring, or
 * cnf_unsatisfiable if graph contains loops
 */
inline CNF cnf_circular_edge_colouring(
    const Graph &G, int p, int q, std::map<Edge, int> precolouring
) {
    if (has_loop(G)) {
        return cnf_unsatisfiable;
    }
    Factory f;
    auto [H, edgeToVertex] = line_graph_with_map(G, f);
    std::map<Vertex, int> lgPrecolouring;
    for (Edge e : G.list(RP::all(), IP::primary(), IT::e())) {
        if (precolouring.count(e) > 0) {
            int edge_colour = precolouring[e];
#ifdef BA_GRAPH_DEBUG
            // Check that the precoloured edge colour is within the valid range [0, p-1].
            // If p=0, any precolouring is invalid (as no colours exist).
            // The assertion preC < p in cnf_circular_vertex_colouring handles the p=0 case
            // correctly (i.e., if p=0, preC must be < 0, which is false for any valid colour
            // index). This assertion here serves as an earlier check for edge precolourings.
            assert(edge_colour >= 0 && "Precoloured edge colour must be non-negative.");
            assert(edge_colour < p && "Precoloured edge colour must be less than p.");
#endif
            lgPrecolouring[H[edgeToVertex[e]].v()] = edge_colour;
        }
    }
    return cnf_circular_vertex_colouring(H, p, q, lgPrecolouring);
}

/**
 * @brief Generates CNF formula for circular (p,q)-edge-colouring.
 *
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolour Whether to precolor some edges to break symmetry
 * @return CNF formula that is satisfiable iff graph has a valid circular (p,q)-edge-colouring, or
 * cnf_unsatisfiable if graph contains loops
 */
inline CNF cnf_circular_edge_colouring(const Graph &G, int p, int q, bool precolour = false) {
    if (has_loop(G)) {
        return cnf_unsatisfiable;
    }
    Factory f;
    Graph H = line_graph(G, f);
    return cnf_circular_vertex_colouring(H, p, q, precolour);
}

namespace internal {

/**
 * @brief Computes a sorted list of unique, irreducible fractions p/q within the described
 * limitations.
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
        throw std::runtime_error("computeCircularColouringFractions(): illegal argument lb");
    }
    if (ub < lb) {
        throw std::runtime_error("computeCircularColouringFractions(): up < lb");
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
            // Compare f1.first/f1.second < f2.first/f2.second as f1.first * f2.second < f2.first *
            // f1.second Use long long for products to prevent overflow.
            return static_cast<long long>(f1.first) * f2.second <
                   static_cast<long long>(f2.first) * f1.second;
        }
    );

    return sortedFractions;
}

}  // namespace internal

}  // namespace ba_graph

#endif