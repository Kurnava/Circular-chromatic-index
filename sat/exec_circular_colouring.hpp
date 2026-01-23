#ifndef BA_GRAPH_SAT_EXEC_CIRCULAR_COLOURING_HPP
#define BA_GRAPH_SAT_EXEC_CIRCULAR_COLOURING_HPP

#include <optional>

#include "../invariants/colouring.hpp"
#include "../invariants/girth.hpp"
#include "cnf_circular_colouring.hpp"
#include "exec_colouring.hpp"
#include "exec_solver.hpp"
#include "solver.hpp"

namespace ba_graph {

/*
 * ==================== circular vertex- and edge-colourings =========================
 */

/**
 * @brief Determines if G has a circular (p,q)-vertex-colouring with given precoloring.
 *
 * A circular (p,q)-colouring assigns colors from {0,1,...,p-1} such that adjacent
 * vertices have colors at circular distance ≥ q on the circle of length p.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of vertices to their preassigned colors
 * @return true if a (p,q)-colouring exists, false otherwise
 */
inline bool is_circularly_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Vertex, int> precolouring
) {
    if (has_loop(G)) {
        return false;
    }
    auto cnf = cnf_circular_vertex_colouring(G, p, q, precolouring);
    return satisfiable(solver, cnf);
}

/**
 * @brief Determines if G has a circular (p,q)-vertex-colouring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @return true if a (p,q)-colouring exists, false otherwise
 */
inline bool is_circularly_colourable_sat(const SatSolver &solver, const Graph &G, int p, int q) {
    if (has_loop(G)) {
        return false;
    }
    auto cnf = cnf_circular_vertex_colouring(G, p, q, true);
    return satisfiable(solver, cnf);
}

/**
 * @brief Determines if G has a circular (p,q)-vertex-colouring with a tight cycle.
 *
 * Checks for the existence of a valid (p,q)-colouring that is "tight" on at least
 * one cycle in the graph (often used for criticality testing).
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length
 * @param q Minimum circular distance
 * @return true if such colouring exists, false otherwise
 */
inline bool exists_circular_colour_with_tight_cycle_sat(
    const SatSolver &solver, const Graph &G, int p, int q)
{
    CNF cnf = cnf_circular_vertex_colouring_with_tight_cycle_fast(G, p, q, true);
    if (cnf == cnf_unsatisfiable) return false;
    if (cnf == cnf_satisfiable)   return true;
    return satisfiable(solver, cnf);
}

/**
 * @brief Determines if G has a circular (p,q)-edge-colouring with given precoloring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of edges to their preassigned colors
 * @return true if (p,q)-edge-colouring exists, false otherwise
 */
inline bool is_circularly_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Edge, int> precolouring
) {
    auto cnf = cnf_circular_edge_colouring(G, p, q, precolouring);
    return satisfiable(solver, cnf);
}

/**
 * @brief Determines if G has a circular (p,q)-edge-colouring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @return true if (p,q)-edge-colouring exists, false otherwise
 */
inline bool is_circularly_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q
) {
    auto cnf = cnf_circular_edge_colouring(G, p, q, true);
    return satisfiable(solver, cnf);
}

/**
 * @brief Computes the circular chromatic number of graph G.
 *
 * The circular chromatic number is the infimum of p/q such that G has a circular
 * (p,q)-vertex-colouring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic number as a fraction p/q, or std::nullopt if graph is uncolourable
 * (contains loops)
 */
inline std::optional<std::pair<int, int>> circular_chromatic_number_sat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = NULL
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    int chn = chromatic_number_sat(solver, G);
    if (chn == UNCOLOURABLE) {
        return std::nullopt;
    }
    auto sortedFractions =
        internal::computeCircularColouringFractions(G.order(), chn - 1, chn, false, true);
    int minI = 0, maxI = sortedFractions.size() - 1;
    while (minI < maxI) {
        int smallestNumeratorI = minI;
        for (int j = minI; j < maxI; ++j) {
            if (sortedFractions[j].first < sortedFractions[smallestNumeratorI].first) {
                smallestNumeratorI = j;
            }
        }
        auto [p, q] = sortedFractions[smallestNumeratorI];
        if (reportProgressStream) {
            *reportProgressStream << "trying " << p << "/" << q;
            *reportProgressStream << std::flush;
        }

        bool r = is_circularly_colourable_sat(solver, G, p, q);

        if (reportProgressStream) {
            if (r) {
                *reportProgressStream << " <=";
            } else {
                *reportProgressStream << " >";
            }
            *reportProgressStream << std::endl;
        }
        if (r) {
            maxI = smallestNumeratorI;
        } else {
            minI = smallestNumeratorI + 1;
        }
    }

    if (reportProgressStream) {
        *reportProgressStream << sortedFractions[minI].first << "/" << sortedFractions[minI].second
                              << " ==" << std::endl;
    }

    return std::make_optional(sortedFractions[minI]);
}

/**
 * @brief Computes the circular chromatic index of graph G.
 *
 * The circular chromatic index is the circular chromatic number of the line graph of G.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic index as a fraction p/q, or std::nullopt if graph is uncolourable
 * (contains loops)
 */
inline std::optional<std::pair<int, int>> circular_chromatic_index_sat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = NULL
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    int chi = chromatic_index_sat(solver, G);
    if (chi == UNCOLOURABLE) {
        return std::nullopt;
    }
    if (chi == max_deg(G)) {
        // G is colourable, class 1
        return std::make_optional(std::pair<int, int>(max_deg(G), 1));
    } else {
        Factory f;
        Graph LG(line_graph(G, f));
        return circular_chromatic_number_sat(solver, LG, reportProgressStream);
    }
}

// Computes the ceiling of the division of two positive integers.
//
// @param numerator The numerator of the fraction (must be non-negative).
// @param denominator The denominator of the fraction (must be positive).
// @return The smallest integer greater than or equal to numerator/denominator.
inline long long ceiling_of_fraction(long long numerator, long long denominator) {
    if (denominator == 0) {
        throw std::runtime_error("ceiling_of_fraction(): division by zero");
    }
    return (numerator + denominator - 1) / denominator;
}

/**
 * @brief Determines if a graph is chn-vertex-critical.
 *
 * A graph G is cchn-vertex-critical if for every vertex v in V(G),
 * the circular chromatic number of G - v is less than the circular
 * chromatic number of G.
 *
 * @param solver The SAT solver instance.
 * @param G The input graph.
 * @param cchn An optional parameter for the circular chromatic number of G,
 * to avoid re-computing it.
 * @return True if the graph is chn-vertex-critical, false otherwise.
 */
/**
 * @brief Determines if a graph is circular-chromatic-number vertex-critical.
 *
 * A graph G is cchn-vertex-critical if for every vertex v in V(G),
 * the circular chromatic number of G - v is less than the circular chromatic number of G.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param cchn Optional precomputed circular chromatic number of G
 * @return true if graph is cchn-vertex-critical, false otherwise or if graph is uncolourable
 */
inline bool is_cchn_vertex_critical_sat(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchn = std::nullopt
) {
    if (G.order() == 0 || G.order() == 1) {
        return true;
    }

    // 1. Determine the circular chromatic number (cchn) of the original graph G.
    auto cchn_G_opt = cchn.has_value() ? cchn : circular_chromatic_number_sat(solver, G);
    if (!cchn_G_opt.has_value()) {
        return false;  // Graph is uncolourable
    }
    auto cchn_G = cchn_G_opt.value();
    auto chn_G = ceiling_of_fraction(cchn_G.first, cchn_G.second);

    // 2. Get all possible colouring fractions.
    auto fractions =
        internal::computeCircularColouringFractions(G.order() - 1, 1, chn_G, true, true);

    // 3. Find the largest fraction p/q that is strictly less than cchn(G).
    //    This is the fraction we will test the subgraphs against.
    std::pair<int, int> target_fraction = {0, 1};
    for (const auto &frac : fractions) {
        // Compare frac < ccn_G using cross-multiplication to avoid doubles.
        // This is equivalent to frac.first / frac.second < ccn_G.first / ccn_G.second
        if (static_cast<long long>(frac.first) * cchn_G.second <
            static_cast<long long>(cchn_G.first) * frac.second) {
            // Now, compare frac > target_fraction using the same technique.
            // This is equivalent to frac.first / frac.second > target_fraction.first /
            // target_fraction.second
            if (static_cast<long long>(frac.first) * target_fraction.second >
                static_cast<long long>(target_fraction.first) * frac.second) {
                target_fraction = frac;
            }
        }
    }

    // 4. Iterate through each vertex of the graph, sorted by degree (ascending).
    std::vector<Number> sorted_vertex_numbers;
    for (const auto &v : G) {
        sorted_vertex_numbers.push_back(v.n());
    }
    std::sort(sorted_vertex_numbers.begin(), sorted_vertex_numbers.end(), [&](Number x, Number y) {
        return G[x].degree() < G[y].degree();
    });

    // Precompute heuristic fractions (largest with denominator 1, 2, and 3 smaller than cchn_G)
    long long p1 = chn_G - 1;
    long long p2 = 0, p3 = 0;
    if (cchn_G.second > 0) {
        p2 = (static_cast<long long>(2) * cchn_G.first - 1) / cchn_G.second;
        p3 = (static_cast<long long>(3) * cchn_G.first - 1) / cchn_G.second;
    }

    Factory f;
    for (const auto &v : sorted_vertex_numbers) {
        Graph G_minus_v = copy_other_factory(G, f);
        deleteV(G_minus_v, v, f);

        // 5. Check if the subgraph G-v is colourable with a smaller fraction.
        //    We use a heuristic: first try fractions with small denominators (1, 2, 3)
        //    as these may be faster to check. If any succeeds, we continue to the next vertex.
        //    If they fail, we try the original target_fraction. If that also fails,
        //    the graph is not critical.

        // Heuristic: denominator 1
        if (p1 > 0) {
            if (is_colourable_sat(solver, G_minus_v, p1)) {
                continue;
            }
        }

        // Heuristic: denominator 2
        bool p2_is_p1 =
            (p1 > 0 && p2 > 0 && static_cast<long long>(p2) * 1 == static_cast<long long>(p1) * 2);
        if (p2 > 0 && !p2_is_p1) {
            if (is_circularly_colourable_sat(solver, G_minus_v, p2, 2)) {
                continue;
            }
        }

        // Heuristic: denominator 3
        bool p3_is_p1 =
            (p1 > 0 && p3 > 0 && static_cast<long long>(p3) * 1 == static_cast<long long>(p1) * 3);
        bool p3_is_p2 =
            (p2 > 0 && p3 > 0 && static_cast<long long>(p3) * 2 == static_cast<long long>(p2) * 3);
        if (p3 > 0 && !p3_is_p1 && !p3_is_p2) {
            if (is_circularly_colourable_sat(solver, G_minus_v, p3, 3)) {
                continue;
            }
        }

        // If we are here, the heuristics failed. Now check the target_fraction.
        // But first, make sure we haven't already checked it.
        bool target_is_p1 =
            (p1 > 0 && static_cast<long long>(target_fraction.first) * 1 ==
                           static_cast<long long>(p1) * target_fraction.second);
        if (target_is_p1) {
            return false;
        }

        bool target_is_p2 =
            (p2 > 0 && !p2_is_p1 &&
             static_cast<long long>(target_fraction.first) * 2 ==
                 static_cast<long long>(p2) * target_fraction.second);
        if (target_is_p2) {
            return false;
        }

        bool target_is_p3 =
            (p3 > 0 && !p3_is_p1 && !p3_is_p2 &&
             static_cast<long long>(target_fraction.first) * 3 ==
                 static_cast<long long>(p3) * target_fraction.second);
        if (target_is_p3) {
            return false;
        }

        // Finally, check with the target_fraction.
        if (!is_circularly_colourable_sat(
                solver, G_minus_v, target_fraction.first, target_fraction.second
            )) {
            return false;
        }
    }

    // 6. If all subgraphs were colourable with a smaller fraction, the graph is critical.
    return true;
}

/**
 * @brief Determines if a graph is circular-chromatic-index critical.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param cchi Optional precomputed circular chromatic index of G
 * @return true if graph is cchi-critical, false otherwise or if graph is uncolourable
 */
inline bool is_cchi_critical(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchi = std::nullopt
) {
    Factory f;
    Graph H = line_graph(G, f);
    return is_cchn_vertex_critical_sat(solver, H, cchi);
}

}  // namespace ba_graph

#endif
