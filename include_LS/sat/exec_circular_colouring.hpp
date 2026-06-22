#ifndef BA_GRAPH_SAT_EXEC_CIRCULAR_COLOURING_HPP
#define BA_GRAPH_SAT_EXEC_CIRCULAR_COLOURING_HPP

#include <numeric>
#include <optional>

#include "cnf_circular_colouring.hpp"
#include "exec_colouring.hpp"
#include "exec_solver.hpp"
#include "invariants/colouring.hpp"
#include "invariants/girth.hpp"
#include "solution_types.hpp"
#include "solver.hpp"

namespace ba_graph {

inline bool is_valid_circular_vertex_colouring(
    const Graph &G, int p, int q, const sat_model::VertexColouring &colouring
) {
    if (colouring.size() != static_cast<std::size_t>(G.order())) {
        return false;
    }
    for (const auto &r : G) {
        auto it = colouring.find(r.n());
        if (it == colouring.end() || it->second < 0 || it->second >= p) {
            return false;
        }
    }
    for (const auto &r : G) {
        int c1 = colouring.at(r.n());
        for (const auto &inc : r) {
            int c2 = colouring.at(inc.n2());
            int d = (c1 - c2) >= 0 ? (c1 - c2) : (c2 - c1);
            if (std::min(d, p - d) < q) {
                return false;
            }
        }
    }
    return true;
}

inline bool is_valid_circular_edge_colouring(
    const Graph &G, int p, int q, const sat_model::EdgeColouring &colouring
) {
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    if (colouring.size() != edges.size()) {
        return false;
    }
    for (const auto &loc : edges) {
        auto it = colouring.find(loc);
        if (it == colouring.end()) {
            it = colouring.find(loc.reverse());
        }
        if (it == colouring.end() || it->second < 0 || it->second >= p) {
            return false;
        }
    }
    for (const auto &v : G) {
        std::vector<int> colors;
        for (const auto &inc : v) {
            Location loc = inc.l();
            auto it = colouring.find(loc);
            if (it == colouring.end()) {
                it = colouring.find(loc.reverse());
            }
            if (it != colouring.end()) {
                colors.push_back(it->second);
            }
        }
        for (std::size_t i = 0; i < colors.size(); ++i) {
            for (std::size_t j = i + 1; j < colors.size(); ++j) {
                int d = (colors[i] - colors[j]) >= 0 ? (colors[i] - colors[j])
                                                     : (colors[j] - colors[i]);
                if (std::min(d, p - d) < q) {
                    return false;
                }
            }
        }
    }
    return true;
}

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
inline std::optional<sat_model::VertexColouring> is_circularly_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "is_circularly_colourable_sat_constructive"
    );
    if (p == 0) {
        if (!precolouring.empty()) {
            throw std::invalid_argument(
                "is_circularly_colourable_sat_constructive: precolouring is invalid when p is 0"
            );
        }
        return G.order() == 0 ? std::make_optional(sat_model::VertexColouring{}) : std::nullopt;
    }
    if ((G.size() > 0) && (p < 2 * q)) {
        return std::nullopt;
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, p, q, precolouring, opts);
    auto model = solver.solve(encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_circular_vertex_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START -- requires solver internal bug to trigger
        throw std::runtime_error("circular vertex colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_circularly_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    auto result = is_circularly_colourable_sat_constructive(solver, G, p, q, precolouring, opts);
    return result.has_value();
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
inline std::optional<sat_model::VertexColouring> is_circularly_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "is_circularly_colourable_sat_constructive"
    );
    if (p == 0) {
        return G.order() == 0 ? std::make_optional(sat_model::VertexColouring{}) : std::nullopt;
    }
    if ((G.size() > 0) && (p < 2 * q)) {
        return std::nullopt;
    }
    if (has_loop(G)) {
        return std::nullopt;
    }
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, p, q, opts);
    auto model = solver.solve(encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_circular_vertex_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("circular vertex colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_circularly_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto result = is_circularly_colourable_sat_constructive(solver, G, p, q, opts);
    return result.has_value();
}

/**
 * @brief Determines if G has a circular (p,q)-vertex-colouring without tight cycles.
 *
 * Checks for the existence of a valid (p,q)-colouring that avoids "tight" cycles.
 * A cycle is tight if the colors along its vertices follow a tight arithmetic pattern
 * (often used for criticality testing).
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length
 * @param q Minimum circular distance
 * @return true if such colouring exists, false otherwise
 */
inline bool has_circular_vertex_colouring_without_tight_cycles_sat(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "has_circular_vertex_colouring_without_tight_cycles_sat"
    );
    if ((G.size() > 0) && (p < 2 * q)) {
        return false;
    }
    CNF cnf = cnf_circular_vertex_colouring_without_tight_cycles(G, p, q, opts);
    return solver.solve(cnf).has_value();
}

/**
 * @brief Determines if G has a circular (p,q)-vertex-colouring without tight cycles, with given
 * precoloring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length
 * @param q Minimum circular distance
 * @param precolouring Map of vertices to their preassigned colors
 * @return true if such colouring exists, false otherwise
 */
inline bool has_circular_vertex_colouring_without_tight_cycles_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Vertex, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "has_circular_vertex_colouring_without_tight_cycles_sat"
    );
    if ((G.size() > 0) && (p < 2 * q)) {
        return false;
    }
    CNF cnf = cnf_circular_vertex_colouring_without_tight_cycles(G, p, q, precolouring, opts);
    return solver.solve(cnf).has_value();
}

/**
 * @brief Determines if G has a circular (p,q)-edge-colouring without tight cycles.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @return true if (p,q)-edge-colouring without tight cycles exists, false otherwise
 */
inline bool has_circular_edge_colouring_without_tight_cycles_sat(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "has_circular_edge_colouring_without_tight_cycles_sat"
    );
    if ((max_deg(G) >= 2) && (p < 2 * q)) {
        return false;
    }
    auto cnf = cnf_circular_edge_colouring_without_tight_cycles(G, p, q, opts);
    return solver.solve(cnf).has_value();
}

/**
 * @brief Determines if G has a circular (p,q)-edge-colouring without tight cycles, with given
 * precoloring.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param p Circle length (number of colors)
 * @param q Minimum circular distance required
 * @param precolouring Map of edges to their preassigned colors
 * @return true if (p,q)-edge-colouring without tight cycles exists, false otherwise
 */
inline bool has_circular_edge_colouring_without_tight_cycles_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "has_circular_edge_colouring_without_tight_cycles_sat"
    );
    if ((max_deg(G) >= 2) && (p < 2 * q)) {
        return false;
    }
    auto cnf = cnf_circular_edge_colouring_without_tight_cycles(G, p, q, precolouring, opts);
    return solver.solve(cnf).has_value();
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
inline std::optional<sat_model::EdgeColouring> is_circularly_edge_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "is_circularly_edge_colourable_sat_constructive"
    );
    if (p == 0) {
        if (!precolouring.empty()) {
            throw std::invalid_argument(
                "is_circularly_edge_colourable_sat_constructive: precolouring is invalid when p "
                "is 0"
            );
        }
        return G.size() == 0 ? std::make_optional(sat_model::EdgeColouring{}) : std::nullopt;
    }
    if ((max_deg(G) >= 2) && (p < 2 * q)) {
        return std::nullopt;
    }
    auto encoding = build_circular_edge_colouring_cnf_encoding(G, p, q, precolouring, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_circular_edge_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("circular edge colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_circularly_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q, std::map<Edge, int> precolouring,
    const CircularColouringCnfOptions &opts = {}
) {
    auto result =
        is_circularly_edge_colourable_sat_constructive(solver, G, p, q, precolouring, opts);
    return result.has_value();
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
inline std::optional<sat_model::EdgeColouring> is_circularly_edge_colourable_sat_constructive(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    internal::validate_circular_colouring_parameters(
        p, q, "is_circularly_edge_colourable_sat_constructive"
    );
    if (p == 0) {
        return G.size() == 0 ? std::make_optional(sat_model::EdgeColouring{}) : std::nullopt;
    }
    if ((max_deg(G) >= 2) && (p < 2 * q)) {
        return std::nullopt;
    }
    auto encoding = build_circular_edge_colouring_cnf_encoding(G, p, q, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    if (!model.has_value()) {
        return std::nullopt;
    }
    auto colouring = encoding.decode_model(*model);
    if (!is_valid_circular_edge_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START — requires solver internal bug to trigger
        throw std::runtime_error("circular edge colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_circularly_edge_colourable_sat(
    const SatSolver &solver, const Graph &G, int p, int q,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto result = is_circularly_edge_colourable_sat_constructive(solver, G, p, q, opts);
    return result.has_value();
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
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    int chn = chromatic_number_sat(solver, G);
    if (chn == UNCOLOURABLE) {
        return std::nullopt;
    }
    if (chn == 0) {
        return std::make_optional(std::pair<int, int>(0, 1));
    }
    if (chn == 1) {
        return std::make_optional(std::pair<int, int>(1, 1));
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

        bool r = is_circularly_colourable_sat(solver, G, p, q, opts);

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
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
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
        return circular_chromatic_number_sat(solver, LG, reportProgressStream, opts);
    }
}

/**
 * @brief Computes the circular chromatic number of graph G using the tight-cycles method.
 *
 * This method keeps the same candidate interval/order as circular_chromatic_number_sat, but for a
 * SAT fraction p/q it first checks whether there is a (p,q)-colouring without tight cycles.
 * If not, p/q is exact and the search terminates immediately. Otherwise the method continues with
 * the standard narrowing logic.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic number as a fraction p/q, or std::nullopt if graph is uncolourable
 * (contains loops)
 */
inline std::optional<std::pair<int, int>> circular_chromatic_number_tight_cycles_method_sat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    int chn = chromatic_number_sat(solver, G);
    if (chn == UNCOLOURABLE) {
        return std::nullopt;
    }
    if (chn == 0) {
        return std::make_optional(std::pair<int, int>(0, 1));
    }
    if (chn == 1) {
        return std::make_optional(std::pair<int, int>(1, 1));
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

        bool sat = is_circularly_colourable_sat(solver, G, p, q, opts);
        if (!sat) {
            if (reportProgressStream) {
                *reportProgressStream << " >" << std::endl;
            }
            minI = smallestNumeratorI + 1;
            continue;
        }

        bool no_tight_cycle =
            has_circular_vertex_colouring_without_tight_cycles_sat(solver, G, p, q, opts);
        if (!no_tight_cycle) {
            if (reportProgressStream) {
                *reportProgressStream << " ==" << std::endl;
            }
            return std::make_optional(sortedFractions[smallestNumeratorI]);
        }

        if (reportProgressStream) {
            *reportProgressStream << " <=" << std::endl;
        }
        maxI = smallestNumeratorI;
    }

    auto [p, q] = sortedFractions[minI];
    bool sat = is_circularly_colourable_sat(solver, G, p, q, opts);
    if (!sat) {
        // LCOV_EXCL_START -- requires internal logic inconsistency to trigger
        throw std::runtime_error(
            "circular_chromatic_number_tight_cycles_method_sat: inconsistent final candidate"
        );
        // LCOV_EXCL_STOP
    }
    if (reportProgressStream) {
        *reportProgressStream << p << "/" << q << " ==" << std::endl;
    }
    return std::make_optional(sortedFractions[minI]);
}

/**
 * @brief Computes the circular chromatic index of graph G using the tight-cycles method.
 *
 * This method keeps the same candidate interval/order as circular_chromatic_index_sat, but for a
 * SAT fraction p/q it first checks whether there is a (p,q)-edge-colouring without tight cycles.
 * If not, p/q is exact and the search terminates immediately. Otherwise the method continues with
 * the standard narrowing logic.
 *
 * @param solver The SAT solver to use
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic index as a fraction p/q, or std::nullopt if graph is uncolourable
 * (contains loops)
 */
inline std::optional<std::pair<int, int>> circular_chromatic_index_tight_cycles_method_sat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    int chi = chromatic_index_sat(solver, G);
    if (chi == UNCOLOURABLE) {
        return std::nullopt;
    }
    if (chi == max_deg(G)) {
        return std::make_optional(std::pair<int, int>(max_deg(G), 1));
    }

    auto sortedFractions =
        internal::computeCircularColouringFractions(G.size(), chi - 1, chi, false, true);
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

        bool sat = is_circularly_edge_colourable_sat(solver, G, p, q, opts);
        if (!sat) {
            if (reportProgressStream) {
                *reportProgressStream << " >" << std::endl;
            }
            minI = smallestNumeratorI + 1;
            continue;
        }

        bool no_tight_cycle =
            has_circular_edge_colouring_without_tight_cycles_sat(solver, G, p, q, opts);
        if (!no_tight_cycle) {
            if (reportProgressStream) {
                *reportProgressStream << " ==" << std::endl;
            }
            return std::make_optional(sortedFractions[smallestNumeratorI]);
        }

        if (reportProgressStream) {
            *reportProgressStream << " <=" << std::endl;
        }
        maxI = smallestNumeratorI;
    }

    auto [p, q] = sortedFractions[minI];
    bool sat = is_circularly_edge_colourable_sat(solver, G, p, q, opts);
    if (!sat) {
        // LCOV_EXCL_START -- requires internal logic inconsistency to trigger
        throw std::runtime_error(
            "circular_chromatic_index_tight_cycles_method_sat: inconsistent final candidate"
        );
        // LCOV_EXCL_STOP
    }
    if (reportProgressStream) {
        *reportProgressStream << p << "/" << q << " ==" << std::endl;
    }
    return std::make_optional(sortedFractions[minI]);
}

// Computes the ceiling of the division of two positive integers.
//
// @param numerator The numerator of the fraction (must be non-negative).
// @param denominator The denominator of the fraction (must be positive).
// @return The smallest integer greater than or equal to numerator/denominator.
inline long long ceiling_of_fraction(long long numerator, long long denominator) {
    if (denominator == 0) {
        throw std::invalid_argument("ceiling_of_fraction(): division by zero");
    }
    return (numerator + denominator - 1) / denominator;
}

inline bool circular_fraction_less(std::pair<int, int> lhs, std::pair<int, int> rhs) {
    return static_cast<long long>(lhs.first) * rhs.second <
           static_cast<long long>(rhs.first) * lhs.second;
}

/**
 * @brief Determines if a graph is critical for circular chromatic number under vertex deletion.
 *
 * For any vertex v, the circular chromatic number of G - v must be smaller than that of G.
 */
inline bool is_circular_chromatic_number_vertex_critical_sat(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchn = std::nullopt,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    if (G.order() == 0 || G.order() == 1) {
        return true;
    }

    auto cchn_G_opt =
        cchn.has_value() ? cchn : circular_chromatic_number_sat(solver, G, nullptr, opts);
    if (!cchn_G_opt.has_value()) {
        return false;
    }
    auto cchn_G = cchn_G_opt.value();
    auto chn_G = ceiling_of_fraction(cchn_G.first, cchn_G.second);

    auto fractions =
        internal::computeCircularColouringFractions(G.order() - 1, 1, chn_G, true, true);

    std::pair<int, int> target_fraction = {0, 1};
    for (const auto &frac : fractions) {
        if (circular_fraction_less(frac, cchn_G)) {
            if (circular_fraction_less(target_fraction, frac)) {
                target_fraction = frac;
            }
        }
    }

    if (target_fraction.first == 0) {
        return false;
    }

    std::vector<Number> sorted_vertex_numbers;
    for (const auto &v : G) {
        sorted_vertex_numbers.push_back(v.n());
    }
    std::sort(sorted_vertex_numbers.begin(), sorted_vertex_numbers.end(), [&](Number x, Number y) {
        return G[x].degree() < G[y].degree();
    });

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

        if (p1 > 0) {
            if (is_colourable_sat(solver, G_minus_v, p1)) {
                continue;
            }
        }

        // Heuristic: denominator 2
        bool p2_is_p1 =
            (p1 > 0 && p2 > 0 && static_cast<long long>(p2) * 1 == static_cast<long long>(p1) * 2);
        if (p2 > 0 && !p2_is_p1) {
            if (is_circularly_colourable_sat(solver, G_minus_v, p2, 2, opts)) {
                continue;
            }
        }

        // Heuristic: denominator 3
        bool p3_is_p1 =
            (p1 > 0 && p3 > 0 && static_cast<long long>(p3) * 1 == static_cast<long long>(p1) * 3);
        bool p3_is_p2 =
            (p2 > 0 && p3 > 0 && static_cast<long long>(p3) * 2 == static_cast<long long>(p2) * 3);
        if (p3 > 0 && !p3_is_p1 && !p3_is_p2) {
            if (is_circularly_colourable_sat(solver, G_minus_v, p3, 3, opts)) {
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

        if (!is_circularly_colourable_sat(
                solver, G_minus_v, target_fraction.first, target_fraction.second, opts
            )) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for circular chromatic number under edge deletion.
 */
inline bool is_circular_chromatic_number_edge_critical_sat(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchn = std::nullopt,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto cchn_G_opt =
        cchn.has_value() ? cchn : circular_chromatic_number_sat(solver, G, nullptr, opts);
    if (!cchn_G_opt.has_value()) {
        return false;
    }

    Factory f;
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    for (const auto &edge_loc : edges) {
        Graph G_minus_e = copy_other_factory(G, f);
        deleteE(G_minus_e, edge_loc, f);

        auto cchn_sub = circular_chromatic_number_sat(solver, G_minus_e, nullptr, opts);
        if (!cchn_sub.has_value() || !circular_fraction_less(*cchn_sub, *cchn_G_opt)) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for circular chromatic index under vertex deletion.
 */
inline bool is_circular_chromatic_index_vertex_critical_sat(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchi = std::nullopt,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto cchi_G_opt =
        cchi.has_value() ? cchi : circular_chromatic_index_sat(solver, G, nullptr, opts);
    if (!cchi_G_opt.has_value()) {
        return false;
    }

    Factory f;
    for (const auto &v : G) {
        Graph G_minus_v = copy_other_factory(G, f);
        deleteV(G_minus_v, v.n(), f);

        auto cchi_sub = circular_chromatic_index_sat(solver, G_minus_v, nullptr, opts);
        if (!cchi_sub.has_value() || !circular_fraction_less(*cchi_sub, *cchi_G_opt)) {
            return false;
        }
    }

    return true;
}

/**
 * @brief Determines if a graph is critical for circular chromatic index under edge deletion.
 */
inline bool is_circular_chromatic_index_edge_critical_sat(
    const SatSolver &solver, const Graph &G, std::optional<std::pair<int, int>> cchi = std::nullopt,
    const CircularColouringCnfOptions &opts =
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = true}
) {
    auto cchi_G_opt =
        cchi.has_value() ? cchi : circular_chromatic_index_sat(solver, G, nullptr, opts);
    if (!cchi_G_opt.has_value()) {
        return false;
    }

    Factory f;
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    for (const auto &edge_loc : edges) {
        Graph G_minus_e = copy_other_factory(G, f);
        deleteE(G_minus_e, edge_loc, f);

        auto cchi_sub = circular_chromatic_index_sat(solver, G_minus_e, nullptr, opts);
        if (!cchi_sub.has_value() || !circular_fraction_less(*cchi_sub, *cchi_G_opt)) {
            return false;
        }
    }

    return true;
}

}  // namespace ba_graph

#endif
