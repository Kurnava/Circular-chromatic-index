#ifndef BA_GRAPH_SAT_EXEC_CIRCULAR_CPSAT_HPP
#define BA_GRAPH_SAT_EXEC_CIRCULAR_CPSAT_HPP

#include <cstddef>
#include <forward_list>
#include <list>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "cnf_circular_colouring.hpp"
#include "exec_circular_colouring.hpp"
#include "exec_colouring.hpp"
#include "invariants/girth.hpp"
#include "solution_types.hpp"
#include "solver.hpp"
#include "solver_kissat.hpp"

#if !defined(BA_GRAPH_HAS_ORTOOLS_SUPPORT)
#if __has_include(<ortools/sat/cp_model.h>) && __has_include(<ortools/sat/cp_model_solver.h>)
#define BA_GRAPH_HAS_ORTOOLS_SUPPORT 1
#else
#define BA_GRAPH_HAS_ORTOOLS_SUPPORT 0
#endif
#endif

#if BA_GRAPH_HAS_ORTOOLS_SUPPORT
#ifdef _GLIBCXX_DEBUG
#pragma push_macro("_GLIBCXX_DEBUG")
#undef _GLIBCXX_DEBUG
#define BA_GRAPH_UNDEF_GLIBCXX_DEBUG
#endif
#include <ortools/sat/cp_model.h>
#include <ortools/sat/cp_model_solver.h>
#ifdef BA_GRAPH_UNDEF_GLIBCXX_DEBUG
#pragma pop_macro("_GLIBCXX_DEBUG")
#undef BA_GRAPH_UNDEF_GLIBCXX_DEBUG
#endif
#endif

namespace ba_graph {

#if BA_GRAPH_HAS_ORTOOLS_SUPPORT
using operations_research::Domain;
using operations_research::sat::CpModelBuilder;
using operations_research::sat::CpSolverResponse;
using operations_research::sat::CpSolverStatus;
using operations_research::sat::IntVar;
using operations_research::sat::SolutionIntegerValue;
using operations_research::sat::Solve;

namespace internal {

struct CpsatEdge {
    int u;
    int v;
    Location loc;
};

inline void cpsat_build_edge_list(
    const Graph &G, std::vector<Number> &order, std::map<Number, int> &index,
    std::vector<CpsatEdge> &edges
) {
    order.clear();
    for (auto &r : G) {
        order.push_back(r.n());
    }
    int n = order.size();
    index.clear();
    for (int i = 0; i < n; ++i) {
        index[order[i]] = i;
    }
    edges.clear();
    for (auto &r : G) {
        Number v1 = r.n();
        int u = index[v1];
        for (auto &inc : r) {
            Number v2 = inc.n2();
            int v = index[v2];
            if (v <= u) {
                continue;
            }
            edges.push_back({u, v, inc.l()});
        }
    }
}

inline void cpsat_add_circular_distance_constraint(
    CpModelBuilder &model, IntVar a, IntVar b, int p, int q, int idx, const std::string &prefix
) {
    Domain d(q, p - q);
    IntVar diff = model.NewIntVar(d).WithName(prefix + "_d_" + std::to_string(idx));
    model.AddAbsEquality(diff, a - b);
}

inline bool cpsat_circular_vertex_raw(
    int n, const std::vector<CpsatEdge> &edges, int p, int q, std::vector<int> &out
) {
    if (p < 0 || q <= 0) {
        return false;
    }
    if (p == 0) {
        if (n <= 0) {
            out.clear();
            return true;
        }
        return false;
    }
    if (n <= 0) {
        out.clear();
        return true;
    }
    if (2 * q > p) {
        if (edges.empty()) {
            out.assign(n, 0);
            return true;
        }
        return false;
    }

    CpModelBuilder m;
    Domain d(0, p - 1);
    std::vector<IntVar> x;
    x.reserve(n);
    for (int i = 0; i < n; ++i) {
        x.push_back(m.NewIntVar(d).WithName("v_" + std::to_string(i)));
    }
    int c = 0;
    for (auto &e : edges) {
        cpsat_add_circular_distance_constraint(m, x[e.u], x[e.v], p, q, c++, "e");
    }
    CpSolverResponse r = Solve(m.Build());
    if (r.status() == CpSolverStatus::INFEASIBLE) {
        return false;
    }
    if (r.status() != CpSolverStatus::OPTIMAL && r.status() != CpSolverStatus::FEASIBLE) {
        // LCOV_EXCL_START — requires CP-SAT internal bug to trigger
        throw std::runtime_error(
            "CP-SAT returned status " + std::to_string(static_cast<int>(r.status()))
        );
        // LCOV_EXCL_STOP
    }
    out.resize(n);
    for (int i = 0; i < n; ++i) {
        out[i] = SolutionIntegerValue(r, x[i]);
    }
    return true;
}

inline bool cpsat_circular_edge_raw(
    int n, const std::vector<CpsatEdge> &edges, int p, int q, bool sym, std::vector<int> &out
) {
    int m = edges.size();
    if (p < 0 || q <= 0) {
        return false;
    }
    if (m == 0) {
        out.clear();
        return true;
    }
    if (n <= 0 || p == 0) {
        return false;
    }

    std::vector<std::vector<int>> inc(n);
    for (int i = 0; i < m; ++i) {
        int u = edges[i].u;
        int v = edges[i].v;
        inc[u].push_back(i);
        inc[v].push_back(i);
    }

    bool has_conflict = false;
    for (const auto &incident_edges : inc) {
        if (incident_edges.size() >= 2) {
            has_conflict = true;
            break;
        }
    }
    if (2 * q > p) {
        if (!has_conflict) {
            out.assign(m, 0);
            return true;
        }
        return false;
    }

    CpModelBuilder model;
    Domain d(0, p - 1);
    std::vector<IntVar> evar;
    evar.reserve(m);
    for (int i = 0; i < m; ++i) {
        evar.push_back(model.NewIntVar(d).WithName("e_" + std::to_string(i)));
    }
    int c = 0;
    for (int v = 0; v < n; ++v) {
        for (std::size_t i = 0; i < inc[v].size(); ++i) {
            for (std::size_t j = i + 1; j < inc[v].size(); ++j) {
                cpsat_add_circular_distance_constraint(
                    model, evar[inc[v][i]], evar[inc[v][j]], p, q, c++, "p"
                );
            }
        }
    }
    if (sym && m > 0) {
        model.AddEquality(evar[0], 0);
    }
    CpSolverResponse r = Solve(model.Build());
    if (r.status() == CpSolverStatus::INFEASIBLE) {
        return false;
    }
    if (r.status() != CpSolverStatus::OPTIMAL && r.status() != CpSolverStatus::FEASIBLE) {
        // LCOV_EXCL_START — requires CP-SAT internal bug to trigger
        throw std::runtime_error(
            "CP-SAT returned status " + std::to_string(static_cast<int>(r.status()))
        );
        // LCOV_EXCL_STOP
    }
    out.resize(m);
    for (int i = 0; i < m; ++i) {
        out[i] = SolutionIntegerValue(r, evar[i]);
    }
    return true;
}

}  // namespace internal

inline bool is_circularly_colourable_cpsat(
    const Graph &G, int p, int q, std::vector<int> *v = nullptr
) {
    if (has_loop(G)) {
        return false;
    }
    std::vector<Number> order;
    std::map<Number, int> index;
    std::vector<internal::CpsatEdge> edges;
    internal::cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> out;
    bool ok = internal::cpsat_circular_vertex_raw(order.size(), edges, p, q, out);
    if (!ok) {
        return false;
    }
    if (v) {
        *v = std::move(out);
    }
    return true;
}

inline std::optional<sat_model::VertexColouring> is_circularly_colourable_cpsat_constructive(
    const Graph &G, int p, int q
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    std::vector<Number> order;
    std::map<Number, int> index;
    std::vector<internal::CpsatEdge> edges;
    internal::cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> colours;
    bool ok = internal::cpsat_circular_vertex_raw(order.size(), edges, p, q, colours);
    if (!ok) {
        return std::nullopt;
    }
    sat_model::VertexColouring colouring;
    for (std::size_t i = 0; i < order.size(); ++i) {
        colouring[order[i]] = colours[i];
    }
    if (!is_valid_circular_vertex_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START — requires CP-SAT internal bug to trigger
        throw std::runtime_error("circular vertex colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

inline bool is_circularly_edge_colourable_cpsat(
    const Graph &G, int p, int q, std::vector<int> *out_colouring = nullptr, bool sym = true
) {
    if (has_loop(G)) {
        return false;
    }
    std::vector<Number> order;
    std::map<Number, int> index;
    std::vector<internal::CpsatEdge> edges;
    internal::cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> out;
    bool ok = internal::cpsat_circular_edge_raw(order.size(), edges, p, q, sym, out);
    if (!ok) {
        return false;
    }
    if (out_colouring) {
        *out_colouring = std::move(out);
    }
    return true;
}

inline std::optional<sat_model::EdgeColouring> is_circularly_edge_colourable_cpsat_constructive(
    const Graph &G, int p, int q, bool sym = true
) {
    if (has_loop(G)) {
        return std::nullopt;
    }
    std::vector<Number> order;
    std::map<Number, int> index;
    std::vector<internal::CpsatEdge> edges;
    internal::cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> colours;
    bool ok = internal::cpsat_circular_edge_raw(order.size(), edges, p, q, sym, colours);
    if (!ok) {
        return std::nullopt;
    }
    if (colours.size() != edges.size()) {
        // LCOV_EXCL_START — internal invariant, unreachable in normal operation
        throw std::runtime_error(
            "is_circularly_edge_colourable_cpsat_constructive: colour vector size mismatch"
        );
        // LCOV_EXCL_STOP
    }
    sat_model::EdgeColouring colouring;
    for (std::size_t i = 0; i < edges.size(); ++i) {
        colouring[edges[i].loc] = colours[i];
    }
    if (!is_valid_circular_edge_colouring(G, p, q, colouring)) {
        // LCOV_EXCL_START — requires CP-SAT internal bug to trigger
        throw std::runtime_error("circular edge colouring witness validation failed");
        // LCOV_EXCL_STOP
    }
    return colouring;
}

/**
 * @brief Computes the circular chromatic number of graph G using CP-SAT.
 *
 * The CP-SAT solver searches for the circular chromatic number directly. A SAT solver is
 * required as a subroutine to compute the ordinary chromatic number \chi(G), which provides
 * a tight upper bound for the CP-SAT search space.
 *
 * The circular chromatic number is the infimum of p/q such that G has a circular
 * (p,q)-vertex-colouring.
 *
 * @param solver SAT solver used to compute \chi(G) as an upper bound for the CP-SAT search
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic number as a fraction p/q, or std::nullopt if graph is uncolourable
 */
inline std::optional<std::pair<int, int>> circular_chromatic_number_cpsat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr
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

        bool r = is_circularly_colourable_cpsat(G, p, q);

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
 * @brief Computes the circular chromatic index of graph G using CP-SAT.
 *
 * The CP-SAT solver searches for the circular chromatic index directly. A SAT solver is
 * required as a subroutine to compute the ordinary edge chromatic number \chi'(G), which
 * provides a tight upper bound for the CP-SAT search space.
 *
 * The circular chromatic index is the circular chromatic number of the line graph of G.
 *
 * @param solver SAT solver used to compute \chi'(G) as an upper bound for the CP-SAT search
 * @param G The input graph
 * @param reportProgressStream Optional stream for progress reporting
 * @return The circular chromatic index as a fraction p/q, or std::nullopt if graph is uncolourable
 */
inline std::optional<std::pair<int, int>> circular_chromatic_index_cpsat(
    const SatSolver &solver, const Graph &G, std::ostream *reportProgressStream = nullptr
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
        return circular_chromatic_number_cpsat(solver, LG, reportProgressStream);
    }
}

#else  // BA_GRAPH_HAS_ORTOOLS_SUPPORT

inline bool is_circularly_colourable_cpsat(const Graph &, int, int, std::vector<int> * = nullptr) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

inline std::optional<sat_model::VertexColouring> is_circularly_colourable_cpsat_constructive(
    const Graph &, int, int
) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

inline bool is_circularly_edge_colourable_cpsat(
    const Graph &, int, int, std::vector<int> * = nullptr, bool = true
) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

inline std::optional<sat_model::EdgeColouring> is_circularly_edge_colourable_cpsat_constructive(
    const Graph &, int, int, bool = true
) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

inline std::optional<std::pair<int, int>> circular_chromatic_number_cpsat(
    const SatSolver &, const Graph &, std::ostream * = nullptr
) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

inline std::optional<std::pair<int, int>> circular_chromatic_index_cpsat(
    const SatSolver &, const Graph &, std::ostream * = nullptr
) {
    throw std::logic_error("OR-Tools support is not available in this build.");
}

#endif  // BA_GRAPH_HAS_ORTOOLS_SUPPORT

}  // namespace ba_graph

#endif  // BA_GRAPH_SAT_EXEC_CIRCULAR_CPSAT_HPP