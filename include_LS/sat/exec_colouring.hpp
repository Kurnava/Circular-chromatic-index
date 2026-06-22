#ifndef BA_GRAPH_SAT_EXEC_COLOURING_HPP
#define BA_GRAPH_SAT_EXEC_COLOURING_HPP

#include <stdexcept>
#include <string>

#include "cnf_colouring.hpp"
#include "exec_solver.hpp"
#include "invariants/colouring.hpp"
#include "invariants/colouring_cvd.hpp"
#include "invariants/girth.hpp"
#include "solution_types.hpp"
#include "solver.hpp"

namespace ba_graph {

inline bool is_valid_vertex_colouring(
    const Graph &G, int k, const sat_model::VertexColouring &colouring
) {
    if (colouring.size() != static_cast<std::size_t>(G.order())) {
        return false;
    }
    for (const auto &r : G) {
        auto it = colouring.find(r.n());
        if (it == colouring.end() || it->second < 0 || it->second >= k) {
            return false;
        }
    }
    for (const auto &r : G) {
        int c1 = colouring.at(r.n());
        for (const auto &inc : r) {
            if (colouring.at(inc.n2()) == c1) {
                return false;
            }
        }
    }
    return true;
}

inline bool is_valid_edge_colouring(
    const Graph &G, int k, const sat_model::EdgeColouring &colouring
) {
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    if (colouring.size() != edges.size()) {
        return false;
    }
    for (const auto &loc : edges) {
        auto it = colouring.find(loc);
        if (it == colouring.end() || it->second < 0 || it->second >= k) {
            return false;
        }
    }
    for (const auto &v : G) {
        std::vector<int> used;
        for (const auto &inc : v) {
            Location loc = inc.l();
            auto it = colouring.find(loc);
            if (it == colouring.end()) {
                it = colouring.find(loc.reverse());
            }
            if (it != colouring.end()) {
                used.push_back(it->second);
            }
        }
        std::sort(used.begin(), used.end());
        if (std::adjacent_find(used.begin(), used.end()) != used.end()) {
            return false;
        }
    }
    return true;
}

/*
 * ==================== regular vertex- and edge-colourings =========================
 */

/**
 * @brief Determines if G has a k-vertex-colouring with given precoloring.
 *
 * A k-vertex-colouring assigns colors from {0,1,...,k-1} such that adjacent
 * vertices have different colors.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param k Number of colors available
 * @param precolouring Map of vertices to their preassigned colors
 * @param opts Options for CNF construction
 * @return true if such a coloring exists, false if graph is uncolourable
 */
inline std::optional<sat_model::VertexColouring> is_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int k, std::map<Vertex, int> precolouring,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    opts.validate("is_colourable_sat_constructive");
    if (k < 0) {
        throw std::invalid_argument("is_colourable_sat_constructive: k must be non-negative");
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_vertex_colouring_cnf_encoding(G, k, precolouring, opts);
    auto model = solver.solve(encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_vertex_colouring(G, k, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("vertex colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_colourable_sat(
    const SatSolver &solver, const Graph &G, int k, std::map<Vertex, int> precolouring,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto result = is_colourable_sat_constructive(solver, G, k, precolouring, opts);
    return result.has_value();
}

/**
 * @brief Determines if G has a k-vertex-colouring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param k Number of colors available
 * @param opts Options for CNF construction
 * @return true if such a coloring exists, false if graph is uncolourable
 */
inline std::optional<sat_model::VertexColouring> is_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    opts.validate("is_colourable_sat_constructive");
    if (k < 0) {
        throw std::invalid_argument("is_colourable_sat_constructive: k must be non-negative");
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_vertex_colouring_cnf_encoding(G, k, opts);
    auto model = solver.solve(encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_vertex_colouring(G, k, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("vertex colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_colourable_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto result = is_colourable_sat_constructive(solver, G, k, opts);
    return result.has_value();
}

/**
 * @brief Determines if G has a k-edge-colouring with given precoloring.
 *
 * A k-edge-colouring assigns colors from {0,1,...,k-1} such that adjacent
 * edges have different colors.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param k Number of colors available
 * @param precolouring Map of edges to their preassigned colors
 * @param opts Options for CNF construction
 * @return true if such a coloring exists, false if graph is uncolourable
 */
inline std::optional<sat_model::EdgeColouring> is_edge_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int k, std::map<Edge, int> precolouring,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    opts.validate("is_edge_colourable_sat_constructive");
    if (k < 0) {
        throw std::invalid_argument("is_edge_colourable_sat_constructive: k must be non-negative");
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_edge_colouring_cnf_encoding(G, k, precolouring, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_edge_colouring(G, k, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("edge colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int k, std::map<Edge, int> precolouring,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    auto result = is_edge_colourable_sat_constructive(solver, G, k, precolouring, opts);
    return result.has_value();
}

/**
 * @brief Determines if G has a k-edge-colouring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param k Number of colors available
 * @param opts Options for CNF construction
 * @return true if such a coloring exists, false if graph is uncolourable
 */
inline std::optional<sat_model::EdgeColouring> is_edge_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    opts.validate("is_edge_colourable_sat_constructive");
    if (k < 0) {
        throw std::invalid_argument("is_edge_colourable_sat_constructive: k must be non-negative");
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_edge_colouring_cnf_encoding(G, k, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_edge_colouring(G, k, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("edge colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int k, bool use_cvd_heuristics,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    opts.validate("is_edge_colourable_sat");
    if (k < 0) {
        throw std::invalid_argument("is_edge_colourable_sat: k must be non-negative");
    }
    if (k < max_deg(G)) {
        return false;
    }
    if (use_cvd_heuristics) {
        if (has_cvd_edge_colouring(G)) {
            return true;
        }
    }
    auto result = is_edge_colourable_sat_constructive(solver, G, k, opts);
    return result.has_value();
}

inline bool is_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    return is_edge_colourable_sat(solver, G, k, false, opts);
}

/**
 * @brief Computes the chromatic number of graph G.
 *
 * The chromatic number is the minimum number of colors needed for a proper vertex coloring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param opts Options for CNF construction
 * @return The chromatic number, or UNCOLOURABLE if graph contains loops
 */
inline int chromatic_number_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    opts.validate("chromatic_number_sat");
    if (has_loop(G)) {
        return UNCOLOURABLE;
    }
    if (G.order() == 0) {
        return 0;
    }
    int k = max_deg(G) + 1;
    while (k > 0 && is_colourable_sat(solver, G, k - 1, opts)) {
        --k;
    }
    return k;
}

/**
 * @brief Computes the chromatic index of graph G.
 *
 * The chromatic index is the minimum number of colors needed for a proper edge coloring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param opts Options for CNF construction
 * @return The chromatic index, or UNCOLOURABLE if graph contains loops
 */
inline int chromatic_index_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    opts.validate("chromatic_index_sat");
    if (has_loop(G)) {
        return UNCOLOURABLE;
    }
    if (G.size() == 0) {
        return 0;
    }
    int k = max_deg(G);
    int max_k = G.size();
    while (k <= max_k) {
        if (is_edge_colourable_sat(solver, G, k, false, opts)) {
            return k;
        }
        ++k;
    }
    throw std::runtime_error(
        "chromatic_index_sat: no edge colouring found with at most one colour per edge"
    );
}

inline void validate_vertex_deletion_criticality_input(const Graph &G, int k, const char *name) {
    if (k < 2) {
        throw std::invalid_argument(
            std::string(name) + " is only meaningful for invariant values >= 2"
        );
    }

    if (G.size() == 0) {
        throw std::invalid_argument(std::string(name) + " is not defined for graphs without edges");
    }
}

inline void validate_edge_deletion_criticality_input(const Graph &G, int k, const char *name) {
    if (k < 2) {
        throw std::invalid_argument(
            std::string(name) + " is only meaningful for invariant values >= 2"
        );
    }

    if (G.size() == 0) {
        throw std::invalid_argument(std::string(name) + " is not defined for graphs without edges");
    }
}

/**
 * @brief Determines if a graph is k-critical for chromatic number under vertex deletion.
 *
 * G is k-critical if chi(G) = k and, for any vertex v, chi(G - v) < k.
 */
inline bool is_k_chromatic_number_vertex_critical_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    validate_vertex_deletion_criticality_input(G, k, "Chromatic-number vertex-criticality");

    int actual_chromatic_number = chromatic_number_sat(solver, G, opts);
    if (actual_chromatic_number != k) {
        return false;
    }

    Factory f;
    for (const auto &v : G) {
        Graph G_minus_v = copy_other_factory(G, f);
        deleteV(G_minus_v, v.n(), f);

        if (!is_colourable_sat(solver, G_minus_v, k - 1, opts)) {
            return false;
        }
    }
    return true;
}

/**
 * @brief Determines if a graph is critical for chromatic number under vertex deletion.
 */
inline bool is_chromatic_number_vertex_critical_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (G.size() == 0) {
        throw std::invalid_argument(
            "Chromatic-number vertex-criticality is not defined for graphs without edges"
        );
    }

    int k = chromatic_number_sat(solver, G, opts);
    if (k == UNCOLOURABLE || k < 2) {
        throw std::invalid_argument(
            "Chromatic-number vertex-criticality is only meaningful for chromatic number >= 2"
        );
    }

    return is_k_chromatic_number_vertex_critical_sat(solver, G, k, opts);
}

/**
 * @brief Determines if a graph is k-critical for chromatic number under edge deletion.
 *
 * G is k-critical if chi(G) = k and, for any edge e, chi(G - e) < k.
 */
inline bool is_k_chromatic_number_edge_critical_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    validate_edge_deletion_criticality_input(G, k, "Chromatic-number edge-criticality");

    int actual_chromatic_number = chromatic_number_sat(solver, G, opts);
    if (actual_chromatic_number != k) {
        return false;
    }

    Factory f;
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    for (const auto &edge_loc : edges) {
        Graph G_minus_e = copy_other_factory(G, f);
        deleteE(G_minus_e, edge_loc, f);

        if (!is_colourable_sat(solver, G_minus_e, k - 1, opts)) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for chromatic number under edge deletion.
 */
inline bool is_chromatic_number_edge_critical_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts = ColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (G.size() == 0) {
        throw std::invalid_argument(
            "Chromatic-number edge-criticality is not defined for graphs without edges"
        );
    }

    int k = chromatic_number_sat(solver, G, opts);
    if (k == UNCOLOURABLE || k < 2) {
        throw std::invalid_argument(
            "Chromatic-number edge-criticality is only meaningful for chromatic number >= 2"
        );
    }

    return is_k_chromatic_number_edge_critical_sat(solver, G, k, opts);
}

/**
 * @brief Determines if a graph is k-critical for chromatic index under vertex deletion.
 *
 * G is k-critical if chi'(G) = k and, for any vertex v, chi'(G - v) < k.
 */
inline bool is_k_chromatic_index_vertex_critical_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    validate_vertex_deletion_criticality_input(G, k, "Chromatic-index vertex-criticality");

    if (!is_edge_colourable_sat(solver, G, k, false, opts) ||
        is_edge_colourable_sat(solver, G, k - 1, false, opts)) {
        return false;
    }

    Factory f;
    for (const auto &v : G) {
        Graph G_minus_v = copy_other_factory(G, f);
        deleteV(G_minus_v, v.n(), f);

        if (!is_edge_colourable_sat(solver, G_minus_v, k - 1, false, opts)) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for chromatic index under vertex deletion.
 */
inline bool is_chromatic_index_vertex_critical_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    if (G.size() == 0) {
        throw std::invalid_argument(
            "Chromatic-index vertex-criticality is not defined for graphs without edges"
        );
    }

    int k = chromatic_index_sat(solver, G, opts);
    if (k == UNCOLOURABLE || k < 2) {
        throw std::invalid_argument(
            "Chromatic-index vertex-criticality is only meaningful for chromatic index >= 2"
        );
    }

    return is_k_chromatic_index_vertex_critical_sat(solver, G, k, opts);
}

/**
 * @brief Determines if a graph is k-critical for chromatic index under edge deletion.
 *
 * G is k-critical if chi'(G) = k and, for any edge e, chi'(G - e) < k.
 */
inline bool is_k_chromatic_index_edge_critical_sat(
    const SatSolver &solver, const Graph &G, int k,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    validate_edge_deletion_criticality_input(G, k, "Chromatic-index edge-criticality");

    if (!is_edge_colourable_sat(solver, G, k, false, opts) ||
        is_edge_colourable_sat(solver, G, k - 1, false, opts)) {
        return false;
    }

    Factory f;
    auto edges = G.list(RP::all(), IP::primary(), IT::l());

    for (const auto &edge_loc : edges) {
        Graph G_minus_e = copy_other_factory(G, f);
        deleteE(G_minus_e, edge_loc, f);

        if (!is_edge_colourable_sat(solver, G_minus_e, k - 1, false, opts)) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for chromatic index under edge deletion.
 */
inline bool is_chromatic_index_edge_critical_sat(
    const SatSolver &solver, const Graph &G,
    const ColouringCnfOptions &opts =
        ColouringCnfOptions{
            .break_symmetry_by_precolouring = true,
            .break_symmetry_by_ordering_parallel_edges = false
        }
) {
    if (G.size() == 0) {
        throw std::invalid_argument(
            "Chromatic-index edge-criticality is not defined for graphs without edges"
        );
    }

    int k = chromatic_index_sat(solver, G, opts);
    if (k == UNCOLOURABLE || k < 2) {
        throw std::invalid_argument(
            "Chromatic-index edge-criticality is only meaningful for chromatic index >= 2"
        );
    }

    return is_k_chromatic_index_edge_critical_sat(solver, G, k, opts);
}

}  // namespace ba_graph

#endif
