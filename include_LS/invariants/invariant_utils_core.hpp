#ifndef BA_GRAPH_INVARIANTS_INVARIANT_UTILS_CORE_HPP
#define BA_GRAPH_INVARIANTS_INVARIANT_UTILS_CORE_HPP

#include <array>
#include <cstddef>
#include <map>

#include "algorithms/cycles.hpp"
#include "algorithms/matchings.hpp"
#include "algorithms/paths.hpp"
#include "algorithms/permutation_graph.hpp"
#include "graphs/basic.hpp"
#include "graphs/cubic.hpp"
#include "invariants/colouring.hpp"
#include "invariants/colouring_cvd.hpp"
#include "invariants/connectivity.hpp"
#include "invariants/cyclic_connectivity.hpp"
#include "invariants/ecd.hpp"
#include "invariants/girth.hpp"
#include "invariants/invariant_types.hpp"
#include "io/graph_with_invariants.hpp"
#include "io/unified_io.hpp"
// clang-format off
#include "sat/solver_cadical.hpp"
#include "sat/solver_kissat.hpp"
// clang-format on
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "sat/exec_circular_colouring.hpp"
#include "sat/exec_circular_cpsat.hpp"
#include "sat/exec_circumference.hpp"
#include "sat/exec_colouring.hpp"
#include "sat/exec_ecd.hpp"
#include "sat/exec_ecd_asp.hpp"
#include "sat/exec_factors.hpp"
#include "sat/exec_hcolouring.hpp"
#include "sat/exec_snarks.hpp"
#include "snarks/colouring.hpp"
#include "snarks/colouring_nagy.hpp"
#include "snarks/defect.hpp"
#include "snarks/oddness.hpp"
#include "snarks/resistance.hpp"

namespace ba_graph {

// ============================================================================
// Utility Functions
// ============================================================================

inline int compute_vertex_connectivity(
    const Graph& G, ComputationMethod method, const ComputationContext& = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return vertex_connectivity(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for vertex_connectivity. Supported: BASIC."
            );
    }
}

inline bool check_vertex_connectivity_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;

    if (target < 0) {
        throw std::invalid_argument(
            "vertex_connectivity criterion target must be non-negative, got " +
            std::to_string(target)
        );
    }

    switch (method) {
        case ComputationMethod::BASIC: {
            if (target == 0) {
                return compareValue(vertex_connectivity(G), target, comp);
            }
            if (comp == "<=") {
                return !is_k_vertex_connected(G, target + 1);
            } else if (comp == "<") {
                return !is_k_vertex_connected(G, target);
            } else if (comp == ">=") {
                return is_k_vertex_connected(G, target);
            } else if (comp == ">") {
                return is_k_vertex_connected(G, target + 1);
            } else if (comp == "==") {
                return is_k_vertex_connected(G, target) && !is_k_vertex_connected(G, target + 1);
            } else if (comp == "!=") {
                return !is_k_vertex_connected(G, target) || is_k_vertex_connected(G, target + 1);
            }
            throw std::logic_error(
                "Invalid comparator for vertex_connectivity: " + std::string(comp)
            );
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for vertex_connectivity criterion. Supported: "
                "BASIC."
            );
    }
}

inline int compute_edge_connectivity(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for edge_connectivity. Supported: BASIC."
        );
    }
    return edge_connectivity(G);
}

inline bool check_edge_connectivity_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (c.numerator < 0) {
        throw std::invalid_argument(
            "edge_connectivity criterion target must be non-negative, got " +
            std::to_string(c.numerator)
        );
    }
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for edge_connectivity criterion. Supported: BASIC."
        );
    }
    return compareValue(edge_connectivity(G), c.numerator, c.comparator);
}

enum class WarningId {
    EcdNoEcd,
    GirthAcyclic,
    GirthAcyclicNeq,
    ChromaticIndexUncolourable,
    ChromaticIndexUncolourableNeq,
    ChromaticIndexUncolourableOrdering,
    ChromaticNumberUncolourable,
    ChromaticNumberUncolourableNeq,
    ChromaticNumberUncolourableOrdering,
    CircularChromaticIndexUncolourableSat,
    CircularChromaticIndexUncolourableCpsat,
    CircularChromaticNumberUncolourableSat,
    CircularChromaticNumberUncolourableCpsat,
    CircularChromaticCachedUncolourable,
    ColouringDefectNoPmCover,
    TestOnlyFirst,
    TestOnlySecond,
    TestOnlyThird,
    Count,
};

inline constexpr std::size_t warning_id_count() {
    return static_cast<std::size_t>(WarningId::Count);
}

inline bool warn_once(WarningId id, const std::string& message) {
    static std::array<bool, warning_id_count()> warned{};
    const auto index = static_cast<std::size_t>(id);
    if (index >= warning_id_count()) {
        throw std::logic_error("warn_once: invalid warning id");
    }
    if (!warned[index]) {
        warned[index] = true;
        std::cerr << "Warning: " << message << std::endl;
        return true;
    }
    return false;
}

inline SatSolver& require_sat_solver(
    const ComputationContext& ctx, std::string_view function_name
) {
    if (ctx.sat_solver == nullptr) {
        throw std::runtime_error(
            "SAT computation for " + std::string(function_name) +
            " requires a non-null solver in context"
        );
    }
    return *ctx.sat_solver;
}

template <typename Fn>
decltype(auto) with_cpsat_bound_sat_solver(
    const ComputationContext& ctx, std::string_view function_name, Fn&& fn
) {
    (void)function_name;

    if (ctx.sat_solver != nullptr) {
        return fn(*ctx.sat_solver);
    }

#if BA_GRAPH_HAS_KISSAT_SUPPORT
    KissatSolver default_solver;
    return fn(default_solver);
#else
    throw std::runtime_error(
        "CPSAT computation for " + std::string(function_name) +
        " requires a non-null SAT solver in context when Kissat support is unavailable"
    );
#endif
}

// Helper functions for H-colourability
inline Graph create_H_graph_from_shorthand(std::string_view shorthand) {
    if (shorthand == "P") {
        return create_petersen();
    } else if (shorthand == "K") {
        return create_K_graph();
    } else if (shorthand == "A") {
        return create_A_graph();
    } else if (shorthand == "X") {
        return create_X_graph();
    } else if (shorthand.size() >= 3 && shorthand.find('C') != std::string::npos) {
        // Parse mCk format: m digits followed by 'C' followed by k digits
        size_t c_pos = shorthand.find('C');
        if (c_pos == std::string::npos || c_pos == 0 || c_pos == shorthand.size() - 1) {
            throw std::invalid_argument("Invalid cycle format: " + std::string(shorthand));
        }

        try {
            const std::string multiplicity_str(shorthand.substr(0, c_pos));
            const std::string n_str(shorthand.substr(c_pos + 1));
            size_t multiplicity_pos = 0;
            size_t n_pos = 0;
            int multiplicity = std::stoi(multiplicity_str, &multiplicity_pos);
            int n = std::stoi(n_str, &n_pos);
            if (multiplicity_pos != multiplicity_str.size() || n_pos != n_str.size()) {
                throw std::invalid_argument("Invalid cycle format");
            }
            if (n < 3 || multiplicity < 1) {
                throw std::invalid_argument(
                    "Invalid cycle parameters: k must be >= 3 and m must be >= 1"
                );
            }
            return create_C_graph(n, multiplicity);
        } catch (const std::exception& e) {
            throw std::invalid_argument(
                "Invalid H-graph shorthand: " + std::string(shorthand) + ": " + e.what()
            );
        }
    } else {
        throw std::invalid_argument("Unknown H-graph shorthand: " + std::string(shorthand));
    }
}

inline Graph create_H_graph_from_graph_string(const std::string& graph_code) {
    try {
        return read_graph_autodetect(graph_code);
    } catch (const std::exception& e) {
        throw std::invalid_argument("Invalid graph6/sparse6 code: " + graph_code + ": " + e.what());
    }
}

// Centralized boolean invariant computation functions
// These provide a single place for computation logic, including future optimizations

// ============================================================================
// Hamiltonian Computation Functions
// ============================================================================

inline bool compute_is_hamiltonian(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_hamiltonian_basic(G);

        case ComputationMethod::SAT:
            return is_hamiltonian_sat(require_sat_solver(ctx, "hamiltonian"), G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for hamiltonian. Supported: BASIC, SAT."
            );
    }
}

// ============================================================================
// Hypohamiltonian Computation Functions
// ============================================================================

inline bool compute_is_hypohamiltonian(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_hypohamiltonian_basic(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for hypohamiltonian. Supported: BASIC."
            );
    }
}

// ============================================================================
// Simple Computation Functions
// ============================================================================

inline bool compute_is_simple(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return !has_loop(G) && !has_parallel_edge(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for simple. Supported: BASIC."
            );
    }
}

// ============================================================================
// Acyclic Computation Functions
// ============================================================================

inline bool compute_is_acyclic(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_acyclic(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for acyclic. Supported: BASIC."
            );
    }
}

// ============================================================================
// Claw Free Computation Functions
// ============================================================================

inline bool compute_is_claw_free(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_claw_free(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for claw_free. Supported: BASIC."
            );
    }
}

// ============================================================================
// Bipartite Computation Functions
// ============================================================================

inline bool compute_is_bipartite(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_bipartite(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for bipartite. Supported: BASIC."
            );
    }
}

// ============================================================================
// Eulerian Computation Functions
// ============================================================================

inline bool compute_is_eulerian(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_eulerian(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for eulerian. Supported: BASIC."
            );
    }
}

// ============================================================================
// Quasi Line Graph Computation Functions
// ============================================================================

inline bool compute_is_quasi_line_graph(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_quasi_line_graph(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for quasi_line_graph. Supported: BASIC."
            );
    }
}

// ============================================================================
// Permutation Graph Computation Functions
// ============================================================================

inline bool compute_is_permutation_graph(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_permutation_graph(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for permutation_graph. Supported: BASIC."
            );
    }
}

// ============================================================================
// Criticality Computation Functions
// ============================================================================

inline bool compute_is_chromatic_number_vertex_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_chromatic_number_vertex_critical_basic(G);

        case ComputationMethod::SAT:
            return is_chromatic_number_vertex_critical_sat(
                require_sat_solver(ctx, "chromatic_number_vertex_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_number_vertex_critical. Supported: "
                "BASIC, SAT."
            );
    }
}

inline bool compute_is_chromatic_number_edge_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_chromatic_number_edge_critical_basic(G);

        case ComputationMethod::SAT:
            return is_chromatic_number_edge_critical_sat(
                require_sat_solver(ctx, "chromatic_number_edge_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_number_edge_critical. Supported: "
                "BASIC, SAT."
            );
    }
}

inline bool compute_is_chromatic_index_vertex_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_chromatic_index_vertex_critical_basic(G);

        case ComputationMethod::SAT:
            return is_chromatic_index_vertex_critical_sat(
                require_sat_solver(ctx, "chromatic_index_vertex_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_index_vertex_critical. Supported: "
                "BASIC, SAT."
            );
    }
}

inline bool compute_is_chromatic_index_edge_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return is_chromatic_index_edge_critical_basic(G);

        case ComputationMethod::SAT:
            return is_chromatic_index_edge_critical_sat(
                require_sat_solver(ctx, "chromatic_index_edge_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_index_edge_critical. Supported: "
                "BASIC, SAT."
            );
    }
}

inline bool compute_is_circular_chromatic_number_vertex_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return is_circular_chromatic_number_vertex_critical_sat(
                require_sat_solver(ctx, "circular_chromatic_number_vertex_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for circular_chromatic_number_vertex_critical. "
                "Supported: SAT."
            );
    }
}

inline bool compute_is_circular_chromatic_number_edge_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return is_circular_chromatic_number_edge_critical_sat(
                require_sat_solver(ctx, "circular_chromatic_number_edge_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for circular_chromatic_number_edge_critical. "
                "Supported: SAT."
            );
    }
}

inline bool compute_is_circular_chromatic_index_vertex_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return is_circular_chromatic_index_vertex_critical_sat(
                require_sat_solver(ctx, "circular_chromatic_index_vertex_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for circular_chromatic_index_vertex_critical. "
                "Supported: SAT."
            );
    }
}

inline bool compute_is_circular_chromatic_index_edge_critical(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return is_circular_chromatic_index_edge_critical_sat(
                require_sat_solver(ctx, "circular_chromatic_index_edge_critical"), G
            );

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for circular_chromatic_index_edge_critical. "
                "Supported: "
                "SAT."
            );
    }
}

// ============================================================================
// Critical and Bicritical Snark Computation Functions
// ============================================================================

/**
 * Optimized coloriser that combines fast CVD edge colouring detection with Nagy's algorithm and SAT
 * solver.
 *
 * For cubic (3-regular) graphs, performs a quick pre-check using CVD with
 * iteration limit 1.
 * If the graph is found to be 3-edge-colorable immediately, returns true.
 * Otherwise, uses one of the following strategies:
 * - Non-cubic subproblems: uses exact basic/SAT colourability (no cubic-only heuristics)
 * - If no SAT solver provided: uses Nagy's algorithm for cubic graphs
 * - If SAT solver provided and graph order <= boundary: uses Nagy's algorithm for cubic graphs
 * - If SAT solver provided and graph order > boundary: uses CVD with default iterations, then SAT
 * solver
 *
 * This provides significant performance improvement for detecting non-snarks.
 */
class OptimizedColouriser {
private:
    SatSolver* solver_;
    int graph_order_boundary_;

public:
    /**
     * Constructor with optional parameters for SAT solver and size boundary.
     *
     * @param solver Optional pointer to external SAT solver. If nullptr, uses Nagy's algorithm for
     * all sizes.
     * @param graph_order_boundary Graph order threshold for switching from Nagy to SAT solver when
     * solver is provided. Only used if solver is non-null. Default is 50.
     */
    explicit OptimizedColouriser(SatSolver* solver = nullptr, int graph_order_boundary = 50)
        : solver_(solver),
          graph_order_boundary_(graph_order_boundary) {}

    bool isColourable(const Graph& G) const {
        if (!is_d_regular(G, 3)) {
            if (solver_ == nullptr) {
                BasicColouriser<void> basic_colouriser;
                return basic_colouriser.isColourable(G);
            }
            SatSolverColouriser sat_colouriser(*solver_);
            return sat_colouriser.isColourable(G);
        }

        // Fast pre-check: CVD with iteration limit 1 to detect 3-edge-colorable graphs quickly
        if (has_cvd_edge_colouring_3regular(G, 1)) {
            return true;
        }

        // If no external solver available, use Nagy's algorithm for all sizes
        if (solver_ == nullptr) {
            NagyColouriser nagy_colouriser;
            return nagy_colouriser.isColourable(G);
        }

        // If solver available and graph is small, use Nagy's algorithm
        if (static_cast<int>(G.order()) <= graph_order_boundary_) {
            NagyColouriser nagy_colouriser;
            return nagy_colouriser.isColourable(G);
        }

        // For large graphs with available solver: try CVD with full iterations first, then SAT
        if (has_cvd_edge_colouring_3regular(G)) {
            return true;
        }

        // If CVD doesn't find a coloring, use SAT solver
        SatSolverColouriser sat_colouriser(*solver_);
        return sat_colouriser.isColourable(G);
    }
};

/**
 * Compute whether a graph is a critical snark.
 *
 * A critical snark is a cubic (3-regular), 3-edge-uncolorable graph that is
 * vertex-critical (removing any vertex makes it 3-edge-colorable).
 *
 * Supports both SAT-based (using KissatColouriser) and basic (using NagyColouriser)
 * computation methods.
 *
 * @param G The graph
 * @param method Computation method to use
 * @param ctx Computation context (must contain solver if method is SAT)
 * @return true if graph is a critical snark
 * @throws std::runtime_error if graph is not cubic
 */
inline bool compute_is_critical_snark(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (!is_d_regular(G, 3)) {
        throw std::invalid_argument("critical_snark is defined only for cubic (3-regular) graphs");
    }

    switch (method) {
        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "critical_snark");
            OptimizedColouriser colouriser(&solver);
            return is_critical(G, colouriser);
        }

        case ComputationMethod::BASIC: {
            OptimizedColouriser colouriser;
            return is_critical(G, colouriser);
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for critical_snark. Supported: BASIC, SAT."
            );
    }
}

/**
 * Compute whether a graph is an irreducible snark.
 *
 * An irreducible snark is a cubic (3-regular), 3-edge-uncolorable graph that is
 * both critical (vertex-critical) and cocritical (edge-critical).
 *
 * Supports both SAT-based (using KissatColouriser) and basic (using NagyColouriser)
 * computation methods.
 *
 * @param G The graph
 * @param method Computation method to use
 * @param ctx Computation context (must contain solver if method is SAT)
 * @return true if graph is an irreducible snark
 * @throws std::runtime_error if graph is not cubic
 */
inline bool compute_is_irreducible_snark(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (!is_d_regular(G, 3)) {
        throw std::invalid_argument("irreducible_snark is defined only for cubic (3-regular) graphs"
        );
    }

    switch (method) {
        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "irreducible_snark");
            OptimizedColouriser colouriser(&solver);
            return is_irreducible(G, colouriser);
        }

        case ComputationMethod::BASIC: {
            OptimizedColouriser colouriser;
            return is_irreducible(G, colouriser);
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for irreducible_snark. Supported: BASIC, SAT."
            );
    }
}

// ============================================================================
// ECD Size Computation Functions
// ============================================================================

inline int compute_ecd_size(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return ecd_size(G);

        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "ecd_size");
            return ecd_size_sat(solver, G);
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for ecd_size. Supported: BASIC, SAT."
            );
    }
}

/**
 * Check if ECD size satisfies criterion, using optimized algorithm when possible.
 *
 * @param G The graph
 * @param criterion Comparison criterion (comparator and target value)
 * @param method Computation method to use
 * @param ctx Computation context (must contain solver if method is SAT)
 * @return true if criterion is satisfied
 * @throws std::runtime_error if method is unsupported or criterion is invalid
 *
 * Note: No validation of ctx contents - caller must ensure resources are available.
 */
inline bool check_ecd_size_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target("ecd_size", target, NO_ECD, "NO_ECD");

    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for NO_ECD target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for graph with no ECD"
        );
    };

    switch (method) {
        case ComputationMethod::BASIC: {
            int ecd_val = ecd_size(G);
            if (comp == "==") {
                return ecd_val == target;  // works for both finite and NO_ECD targets
            }
            if (comp == "!=") {
                return ecd_val != target;  // works for both finite and NO_ECD targets
            }
            if (target == NO_ECD) {
                throw_meaningless_target();
            }
            if (ecd_val == NO_ECD) {
                if (comp == "<=" || comp == "<") {
                    warn_once(
                        WarningId::EcdNoEcd, "Found graph with no ECD using ecd_size comparison"
                    );
                    return false;
                }
                throw_meaningless_graph();
            }
            return compareValue(ecd_val, target, comp);
        }

        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "ecd_size criterion");

            if (comp == "==") {
                if (target == NO_ECD) {
                    return !has_ecd_sat(solver, G);
                }
                if (!has_ecd_sat(solver, G)) {
                    return false;
                }
                if (target == 0) {
                    // ECD of size == 0 iff it fits in 0 color classes (only edgeless graphs)
                    return has_ecd_size_at_most_sat(solver, G, 0);
                }
                return has_ecd_size_at_most_sat(solver, G, target) &&
                       !has_ecd_size_at_most_sat(solver, G, target - 1);
            }
            if (comp == "!=") {
                if (target == NO_ECD) {
                    return has_ecd_sat(solver, G);
                }
                if (!has_ecd_sat(solver, G)) {
                    return true;
                }
                if (target == 0) {
                    // ECD exists; size != 0 iff ECD has at least 1 color class
                    return !has_ecd_size_at_most_sat(solver, G, 0);
                }
                return !has_ecd_size_at_most_sat(solver, G, target) ||
                       has_ecd_size_at_most_sat(solver, G, target - 1);
            }
            if (target == NO_ECD) {
                throw_meaningless_target();
            }
            // <= and <: if no ECD exists, the size is undefined, so we return false
            if (comp == "<=") {
                return has_ecd_size_at_most_sat(solver, G, target);
            }
            if (comp == "<") {
                if (target <= 0) {
                    return false;
                }
                return has_ecd_size_at_most_sat(solver, G, target - 1);
            }
            // >= and > require an ECD to exist; negation optimization is invalid otherwise
            if (comp == ">=") {
                if (!has_ecd_sat(solver, G)) {
                    throw_meaningless_graph();
                }
                if (target <= 0) {
                    return true;  // ECD size >= 0 always
                }
                return !has_ecd_size_at_most_sat(solver, G, target - 1);
            }
            if (comp == ">") {
                if (!has_ecd_sat(solver, G)) {
                    throw_meaningless_graph();
                }
                if (target < 0) {
                    return true;  // ECD size > negative always
                }
                return !has_ecd_size_at_most_sat(solver, G, target);
            }

            throw std::logic_error("Invalid comparator: " + std::string(comp));
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for ecd_size criterion. Supported: BASIC, SAT."
            );
    }
}

// ============================================================================
// Perfect Matching Index Computation Functions
// ============================================================================

inline int compute_perfect_matching_index(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return perfect_matching_index(G);

        case ComputationMethod::SAT:
            return perfect_matching_index_sat(require_sat_solver(ctx, "perfect_matching_index"), G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for perfect_matching_index. Supported: BASIC, SAT."
            );
    }
}

/**
 * Check if perfect matching index satisfies criterion, using SAT solver.
 *
 * OPTIMIZATION: For some operators, avoids computing the exact index:
 * - <= uses direct is_coverable_by_k_perfect_matchings_sat(k) check
 * - < uses is_coverable_by_k_perfect_matchings_sat(k-1) check
 * - >= uses negation: !is_coverable_by_k_perfect_matchings_sat(k-1)
 * - > requires computing exact index (no incremental check)
 *
 * @param G The graph
 * @param criterion Comparison criterion (comparator and target value)
 * @param method Computation method to use
 * @param ctx Computation context (must contain solver if method is SAT)
 * @return true if criterion is satisfied
 * @throws std::runtime_error if method is unsupported or criterion is invalid
 */
inline bool check_perfect_matching_index_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target(
        "perfect_matching_index", target, NO_PERFECT_MATCHING_COVER, "NO_PERFECT_MATCHING_COVER"
    );

    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) +
            "' not meaningful for NO_PERFECT_MATCHING_COVER target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) +
            "' not meaningful for graph with no perfect matching"
        );
    };

    switch (method) {
        case ComputationMethod::BASIC: {
            int pm_val = perfect_matching_index(G);
            if (comp == "==") {
                return pm_val == target;
            }
            if (comp == "!=") {
                return pm_val != target;
            }
            if (target == NO_PERFECT_MATCHING_COVER) {
                throw_meaningless_target();
            }
            if (pm_val == NO_PERFECT_MATCHING_COVER) {
                if (comp == "<=" || comp == "<") {
                    return false;
                }
                throw_meaningless_graph();
            }
            return compareValue(pm_val, target, comp);
        }

        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "perfect_matching_index criterion");
            // Edgeless graph: PM index = 0; evaluate without SAT.
            if (G.size() == 0) {
                return check_perfect_matching_index_criterion(
                    G, criterion, ComputationMethod::BASIC
                );
            }

            if (comp == "==") {
                if (target == NO_PERFECT_MATCHING_COVER) {
                    return !has_perfect_matching_cover_sat(solver, G);
                }
                if (!has_perfect_matching_cover_sat(solver, G)) {
                    return false;
                }
                return is_coverable_by_k_perfect_matchings_sat(solver, G, target) &&
                       !is_coverable_by_k_perfect_matchings_sat(solver, G, target - 1);
            }
            if (comp == "!=") {
                if (target == NO_PERFECT_MATCHING_COVER) {
                    return has_perfect_matching_cover_sat(solver, G);
                }
                if (!has_perfect_matching_cover_sat(solver, G)) {
                    return true;
                }
                return !is_coverable_by_k_perfect_matchings_sat(solver, G, target) ||
                       is_coverable_by_k_perfect_matchings_sat(solver, G, target - 1);
            }
            if (target == NO_PERFECT_MATCHING_COVER) {
                throw_meaningless_target();
            }
            // <= and <: if no PM cover exists, the index is undefined, so we return false
            if (comp == "<=") {
                if (target < 1) {
                    return false;
                }
                return is_coverable_by_k_perfect_matchings_sat(solver, G, target);
            }
            if (comp == "<") {
                if (target <= 1) {
                    return false;
                }
                return is_coverable_by_k_perfect_matchings_sat(solver, G, target - 1);
            }
            // >= and >: negation optimization is invalid without a PM cover
            if (comp == ">=") {
                if (!has_perfect_matching_cover_sat(solver, G)) {
                    throw_meaningless_graph();
                }
                if (target <= 1) {
                    return true;  // PM index >= 1 always when PM cover exists
                }
                return !is_coverable_by_k_perfect_matchings_sat(solver, G, target - 1);
            }
            if (comp == ">") {
                if (!has_perfect_matching_cover_sat(solver, G)) {
                    throw_meaningless_graph();
                }
                if (target < 1) {
                    return true;  // PM index >= 1 always when PM cover exists
                }
                return !is_coverable_by_k_perfect_matchings_sat(solver, G, target);
            }

            throw std::logic_error("Invalid comparator: " + std::string(comp));
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for perfect_matching_index criterion. Supported: "
                "BASIC, SAT."
            );
    }
}

// ============================================================================
// Resistance Computation Functions
// ============================================================================

// Note: See ba-graph/benchmark/resistance/README.md for benchmark results.
// For resistance computations, the SAT method is typically significantly faster
// than BASIC. When speed is a priority, configure your tool to use SAT (-M sat).
inline int compute_resistance(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (method == ComputationMethod::BASIC) {
        return resistance_basic(G);
    } else if (method == ComputationMethod::SAT) {
        return resistance_sat(require_sat_solver(ctx, "resistance"), G);
    } else {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for resistance. Supported: BASIC, SAT."
        );
    }
}

inline bool check_resistance_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    if (method != ComputationMethod::BASIC && method != ComputationMethod::SAT) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for resistance criterion. Supported: BASIC, SAT."
        );
    }
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    if (target < 0) {
        throw std::invalid_argument("resistance criterion target must be non-negative");
    }

    auto at_most = [&](int k) {
        if (k < 0) {
            return false;
        }
        if (method == ComputationMethod::BASIC) {
            return is_resistance_at_most_basic(G, k);
        }
        return is_resistance_at_most_sat(require_sat_solver(ctx, "resistance criterion"), G, k);
    };

    if (comp == "<=") {
        return at_most(target);
    }
    if (comp == "<") {
        return at_most(target - 1);
    }
    if (comp == ">=") {
        return !at_most(target - 1);
    }
    if (comp == ">") {
        return !at_most(target);
    }
    if (comp == "==") {
        return at_most(target) && !at_most(target - 1);
    }
    if (comp == "!=") {
        return !(at_most(target) && !at_most(target - 1));
    }
    throw std::logic_error("Invalid comparator for resistance: " + std::string(comp));
}

// ============================================================================
// Oddness Computation Functions
// ============================================================================

// Both BASIC and SAT are exact; choose based on measured workload.
inline int compute_oddness(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (method == ComputationMethod::BASIC) {
        return oddness_basic(G);
    } else if (method == ComputationMethod::SAT) {
        return oddness_sat(require_sat_solver(ctx, "oddness"), G);
    } else {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for oddness. Supported: BASIC, SAT."
        );
    }
}

inline bool check_oddness_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    if (method != ComputationMethod::BASIC && method != ComputationMethod::SAT) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for oddness criterion. Supported: BASIC, SAT."
        );
    }
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    if (target < 0) {
        throw std::invalid_argument("oddness criterion target must be non-negative");
    }

    auto at_most = [&](int k) {
        if (k < 0) {
            return false;
        }
        if (method == ComputationMethod::BASIC) {
            return is_oddness_at_most_basic(G, k);
        }
        return is_oddness_at_most_sat(require_sat_solver(ctx, "oddness criterion"), G, k);
    };

    if (comp == "<=") {
        return at_most(target);
    }
    if (comp == "<") {
        return at_most(target - 1);
    }
    if (comp == ">=") {
        return !at_most(target - 1);
    }
    if (comp == ">") {
        return !at_most(target);
    }
    if (comp == "==") {
        return at_most(target) && !at_most(target - 1);
    }
    if (comp == "!=") {
        return !(at_most(target) && !at_most(target - 1));
    }
    throw std::logic_error("Invalid comparator for oddness: " + std::string(comp));
}

// ============================================================================
// Weak Oddness Computation Functions
// ============================================================================

// Both BASIC and SAT are exact; choose based on measured workload.
inline int compute_weak_oddness(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (method == ComputationMethod::BASIC) {
        return weak_oddness_basic(G);
    } else if (method == ComputationMethod::SAT) {
        return weak_oddness_sat(require_sat_solver(ctx, "weak_oddness"), G);
    } else {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for weak_oddness. Supported: BASIC, SAT."
        );
    }
}

inline bool check_weak_oddness_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    if (method != ComputationMethod::BASIC && method != ComputationMethod::SAT) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for weak_oddness criterion. Supported: BASIC, SAT."
        );
    }
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    if (target < 0) {
        throw std::invalid_argument("weak-oddness criterion target must be non-negative");
    }

    auto at_most = [&](int k) {
        if (k < 0) {
            return false;
        }
        if (method == ComputationMethod::BASIC) {
            return is_weak_oddness_at_most_basic(G, k);
        }
        return is_weak_oddness_at_most_sat(require_sat_solver(ctx, "weak_oddness criterion"), G, k);
    };

    if (comp == "<=") {
        return at_most(target);
    }
    if (comp == "<") {
        return at_most(target - 1);
    }
    if (comp == ">=") {
        return !at_most(target - 1);
    }
    if (comp == ">") {
        return !at_most(target);
    }
    if (comp == "==") {
        return at_most(target) && !at_most(target - 1);
    }
    if (comp == "!=") {
        return !(at_most(target) && !at_most(target - 1));
    }
    throw std::logic_error("Invalid comparator for weak-oddness: " + std::string(comp));
}

// ============================================================================
// Colouring Defect Computation Functions
// ============================================================================

inline int compute_colouring_defect(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    if (method == ComputationMethod::BASIC) {
        if (G.order() == 0) {
            return 0;
        }
        return minimum_defect_for_k_perfect_matchings(G, 3);
    } else if (method == ComputationMethod::SAT) {
        if (G.order() == 0) {
            return 0;
        }
        SatSolver& solver = require_sat_solver(ctx, "colouring_defect");
        // The colouring defect is defined for k=3 perfect matchings
        // (Steffen, J. Graph Theory 78 (2015), 195-206).
        return minimum_defect_for_k_perfect_matchings_sat(
            solver, G, 3, PerfectMatchingCnfOptions{.break_symmetry_by_ordering_matchings = true}
        );
    } else {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for colouring_defect. Supported: BASIC, SAT."
        );
    }
}

inline bool check_colouring_defect_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    if (method != ComputationMethod::BASIC && method != ComputationMethod::SAT) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for colouring_defect criterion. Supported: BASIC, SAT."
        );
    }
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target(
        "colouring_defect", target, NO_PERFECT_MATCHING_COVER, "NO_PERFECT_MATCHING_COVER"
    );

    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) +
            "' not meaningful for NO_PERFECT_MATCHING_COVER target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) +
            "' not meaningful for graph with no perfect matching cover"
        );
    };

    if (comp == "==") {
        if (target == NO_PERFECT_MATCHING_COVER) {
            return compute_colouring_defect(G, method, ctx) == NO_PERFECT_MATCHING_COVER;
        }
        if (compute_colouring_defect(G, method, ctx) == NO_PERFECT_MATCHING_COVER) {
            warn_once(
                WarningId::ColouringDefectNoPmCover,
                "Found graph with no perfect matching cover while doing colouring defect comparison"
            );
            return false;
        }
        return compute_colouring_defect(G, method, ctx) == target;
    }
    if (comp == "!=") {
        if (target == NO_PERFECT_MATCHING_COVER) {
            return compute_colouring_defect(G, method, ctx) != NO_PERFECT_MATCHING_COVER;
        }
        if (compute_colouring_defect(G, method, ctx) == NO_PERFECT_MATCHING_COVER) {
            warn_once(
                WarningId::ColouringDefectNoPmCover,
                "Found graph with no perfect matching cover while doing colouring defect comparison"
            );
            return true;
        }
        return compute_colouring_defect(G, method, ctx) != target;
    }
    if (target == NO_PERFECT_MATCHING_COVER) {
        throw_meaningless_target();
    }
    int value = compute_colouring_defect(G, method, ctx);
    if (value == NO_PERFECT_MATCHING_COVER) {
        // No perfect matching cover: defect is undefined; not "less than" any finite target.
        if (comp == "<=" || comp == "<") {
            warn_once(
                WarningId::ColouringDefectNoPmCover,
                "Found graph with no perfect matching cover while doing colouring defect comparison"
            );
            return false;
        }
        throw_meaningless_graph();
    }
    if (comp == "<=") {
        return value <= target;
    }
    if (comp == "<") {
        if (target <= 0) {
            return false;
        }
        return value < target;
    }
    if (comp == ">=") {
        return value >= target;
    }
    if (comp == ">") {
        if (target < 0) {
            return true;
        }
        return value > target;
    }
    throw std::logic_error("Invalid comparator for colouring_defect: " + std::string(comp));
}

// ============================================================================
// Order
// ============================================================================

inline int compute_order(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for order. Supported: BASIC."
        );
    }
    return G.order();
}

inline bool check_order_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for order criterion. Supported: BASIC."
        );
    }
    return compareValue(G.order(), c.numerator, c.comparator);
}

// ============================================================================
// Size
// ============================================================================

inline int compute_size(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for size. Supported: BASIC."
        );
    }
    return G.size();
}

inline bool check_size_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for size criterion. Supported: BASIC."
        );
    }
    return compareValue(G.size(), c.numerator, c.comparator);
}

// ============================================================================
// Max Degree
// ============================================================================

inline int compute_max_deg(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for max_deg. Supported: BASIC."
        );
    }
    return max_deg(G);
}

inline bool check_max_deg_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for max_deg criterion. Supported: BASIC."
        );
    }
    return compareValue(max_deg(G), c.numerator, c.comparator);
}

// ============================================================================
// Min Degree
// ============================================================================

inline int compute_min_deg(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for min_deg. Supported: BASIC."
        );
    }
    return min_deg(G);
}

inline bool check_min_deg_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for min_deg criterion. Supported: BASIC."
        );
    }
    return compareValue(min_deg(G), c.numerator, c.comparator);
}

// ============================================================================
// Cut Vertices
// ============================================================================

inline int compute_cut_vertices(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for cut_vertices. Supported: BASIC."
        );
    }
    return static_cast<int>(cut_vertices(G).size());
}

inline bool check_cut_vertices_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for cut_vertices criterion. Supported: BASIC."
        );
    }
    return compareValue(static_cast<int>(cut_vertices(G).size()), c.numerator, c.comparator);
}

// ============================================================================
// Cut Edges
// ============================================================================

inline int compute_cut_edges(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for cut_edges. Supported: BASIC."
        );
    }
    return static_cast<int>(cut_edges(G).size());
}

inline bool check_cut_edges_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for cut_edges criterion. Supported: BASIC."
        );
    }
    return compareValue(static_cast<int>(cut_edges(G).size()), c.numerator, c.comparator);
}

// ============================================================================
// Loops
// ============================================================================

inline int compute_loops(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for loops. Supported: BASIC."
        );
    }
    return count_loops(G);
}

inline bool check_loops_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for loops criterion. Supported: BASIC."
        );
    }
    return compareValue(count_loops(G), c.numerator, c.comparator);
}

// ============================================================================
// Parallel Edges
// ============================================================================

inline int compute_parallel_edges(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for parallel_edges. Supported: BASIC."
        );
    }
    return static_cast<int>(parallel_edges(G).size());
}

inline bool check_parallel_edges_criterion(
    const Graph& G, const ComparisonCriterion& c, ComputationMethod m,
    const ComputationContext& /* ctx */ = {}
) {
    if (m != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for parallel_edges criterion. Supported: BASIC."
        );
    }
    return compareValue(static_cast<int>(parallel_edges(G).size()), c.numerator, c.comparator);
}

// ============================================================================
// Girth Computation Functions
// ============================================================================

inline int compute_girth(
    const Graph& G, ComputationMethod method, const ComputationContext& /* ctx */ = {}
) {
    if (method != ComputationMethod::BASIC) {
        throw UnsupportedComputationMethod(
            "Unsupported computation method for girth. Supported: BASIC."
        );
    }
    return girth(G);
}

inline bool check_girth_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& /* ctx */ = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;

    if (target == NO_CYCLE_FOUND && comp != "==" && comp != "!=") {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for NO_CYCLE_FOUND target"
        );
    }

    switch (method) {
        case ComputationMethod::BASIC: {
            if (comp == "<=") {
                return has_short_cycle(G, target);
            } else if (comp == "<") {
                if (target <= 1) {
                    return false;
                }
                return has_short_cycle(G, target - 1);
            } else if (comp == ">=") {
                if (is_acyclic(G)) {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for acyclic graph (girth undefined)"
                    );
                }
                if (target <= 1) {
                    return true;
                }
                return !has_short_cycle(G, target - 1);
            } else if (comp == ">") {
                if (is_acyclic(G)) {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for acyclic graph (girth undefined)"
                    );
                }
                return !has_short_cycle(G, target);
            } else if (comp == "==") {
                int g = girth(G);
                if (g == NO_CYCLE_FOUND && target != NO_CYCLE_FOUND) {
                    warn_once(
                        WarningId::GirthAcyclic, "Found acyclic graph using girth comparison"
                    );
                }
                return g == target;
            } else if (comp == "!=") {
                int g = girth(G);
                if (g == NO_CYCLE_FOUND && target != NO_CYCLE_FOUND) {
                    warn_once(
                        WarningId::GirthAcyclicNeq, "Found acyclic graph using girth comparison"
                    );
                }
                return g != target;
            }
            throw std::invalid_argument("Invalid comparator for girth: " + std::string(comp));
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for girth criterion. Supported: BASIC."
            );
    }
}

// ============================================================================
// Cyclic Connectivity Computation Functions
// ============================================================================

inline int compute_cyclic_connectivity(
    const Graph& G, ComputationMethod method, const ComputationContext& = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return cyclic_connectivity(G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for cyclic_connectivity. Supported: BASIC."
            );
    }
}

inline bool check_cyclic_connectivity_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;

    if (target < 1) {
        throw std::invalid_argument(
            "cyclic_connectivity criterion target must be at least 1, got " + std::to_string(target)
        );
    }

    switch (method) {
        case ComputationMethod::BASIC: {
            int value = cyclic_connectivity(G);
            return compareValue(value, target, comp);
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for cyclic_connectivity criterion. Supported: "
                "BASIC."
            );
    }
}

// ============================================================================
// Chromatic Index Computation Functions
// ============================================================================

inline int compute_chromatic_index(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC: {
            // Use heuristics-first approach for BASIC
            if (has_loop(G)) {
                return UNCOLOURABLE;
            }
            if (has_cvd_edge_colouring(G)) {
                return max_deg(G);
            }
            if (is_d_regular(G, 3)) {
                NagyColouriser nc;
                return is_colourable(G, nc) ? 3 : 4;
            }
            return chromatic_index_basic(G);
        }

        case ComputationMethod::SAT:
            return chromatic_index_sat(require_sat_solver(ctx, "chromatic_index"), G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_index. Supported: BASIC, SAT."
            );
    }
}

inline bool check_chromatic_index_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target(
        "chromatic_index", target, UNCOLOURABLE, "UNCOLOURABLE"
    );
    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for UNCOLOURABLE target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for uncolourable graph"
        );
    };

    switch (method) {
        case ComputationMethod::BASIC: {
            int chi_val = compute_chromatic_index(G, ComputationMethod::BASIC);
            if (comp == "==") {
                if (chi_val == UNCOLOURABLE && target != UNCOLOURABLE) {
                    warn_once(
                        WarningId::ChromaticIndexUncolourable,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                }
                return chi_val == target;
            }
            if (comp == "!=") {
                if (chi_val == UNCOLOURABLE && target != UNCOLOURABLE) {
                    warn_once(
                        WarningId::ChromaticIndexUncolourableNeq,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                }
                return chi_val != target;
            }
            if (target == UNCOLOURABLE) {
                throw_meaningless_target();
            }
            if (chi_val == UNCOLOURABLE) {
                if (comp == "<=" || comp == "<") {
                    warn_once(
                        WarningId::ChromaticIndexUncolourableOrdering,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                    return false;
                }
                throw_meaningless_graph();
            }
            if (comp == "<=") {
                return chi_val <= target;
            }
            if (comp == "<") {
                return chi_val < target;
            }
            if (comp == ">=") {
                return chi_val >= target;
            }
            if (comp == ">") {
                return chi_val > target;
            }
            throw std::logic_error("Invalid comparator for chromatic_index: " + std::string(comp));
        }

        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "chromatic_index criterion");
            bool uncolourable = has_loop(G);
            if (comp == "==") {
                if (target == UNCOLOURABLE) {
                    return uncolourable;
                }
                if (uncolourable) {
                    warn_once(
                        WarningId::ChromaticIndexUncolourable,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                    return false;
                }
                if (target == 0) {
                    return is_edge_colourable_sat(solver, G, 0, true);
                }
                return is_edge_colourable_sat(solver, G, target, true) &&
                       !is_edge_colourable_sat(solver, G, target - 1, true);
            }
            if (comp == "!=") {
                if (target == UNCOLOURABLE) {
                    return !uncolourable;
                }
                if (uncolourable) {
                    warn_once(
                        WarningId::ChromaticIndexUncolourableNeq,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                    return true;
                }
                if (target == 0) {
                    return !is_edge_colourable_sat(solver, G, 0, true);
                }
                return !is_edge_colourable_sat(solver, G, target, true) ||
                       is_edge_colourable_sat(solver, G, target - 1, true);
            }
            if (target == UNCOLOURABLE) {
                throw_meaningless_target();
            }
            if (uncolourable) {
                if (comp == "<=" || comp == "<") {
                    warn_once(
                        WarningId::ChromaticIndexUncolourableOrdering,
                        "Found uncolourable graph while doing chromatic index comparison"
                    );
                    return false;
                }
                throw_meaningless_graph();
            }
            if (comp == "<=") {
                return is_edge_colourable_sat(solver, G, target, true);
            }
            if (comp == "<") {
                if (target <= 0) {
                    return false;
                }
                return is_edge_colourable_sat(solver, G, target - 1, true);
            }
            if (comp == ">=") {
                if (target <= 0) {
                    return true;
                }
                return !is_edge_colourable_sat(solver, G, target - 1, true);
            }
            if (comp == ">") {
                return !is_edge_colourable_sat(solver, G, target, true);
            }
            throw std::logic_error(
                "Invalid comparator for chromatic_index (SAT): " + std::string(comp)
            );
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_index criterion. Supported: BASIC, "
                "SAT."
            );
    }
}

// ============================================================================
// Chromatic Number Computation Functions
// ============================================================================

inline int compute_chromatic_number(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return chromatic_number_basic(G);

        case ComputationMethod::SAT:
            return chromatic_number_sat(require_sat_solver(ctx, "chromatic_number"), G);

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_number. Supported: BASIC, SAT."
            );
    }
}

inline bool check_chromatic_number_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target(
        "chromatic_number", target, UNCOLOURABLE, "UNCOLOURABLE"
    );
    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for UNCOLOURABLE target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for uncolourable graph"
        );
    };

    switch (method) {
        case ComputationMethod::BASIC: {
            int chn_val = chromatic_number_basic(G);
            if (comp == "==") {
                if (chn_val == UNCOLOURABLE && target != UNCOLOURABLE) {
                    warn_once(
                        WarningId::ChromaticNumberUncolourable,
                        "Found uncolourable graph using chromatic number comparison"
                    );
                }
                return chn_val == target;
            }
            if (comp == "!=") {
                if (chn_val == UNCOLOURABLE && target != UNCOLOURABLE) {
                    warn_once(
                        WarningId::ChromaticNumberUncolourableNeq,
                        "Found uncolourable graph using chromatic number comparison"
                    );
                }
                return chn_val != target;
            }
            if (target == UNCOLOURABLE) {
                throw_meaningless_target();
            }
            if (chn_val == UNCOLOURABLE) {
                if (comp == "<=" || comp == "<") {
                    warn_once(
                        WarningId::ChromaticNumberUncolourableOrdering,
                        "Found uncolourable graph using chromatic number comparison"
                    );
                    return false;
                }
                throw_meaningless_graph();
            }
            return compareValue(chn_val, target, comp);
        }

        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "chromatic_number criterion");
            bool uncolourable = has_loop(G);
            if (comp == "==") {
                if (target == UNCOLOURABLE) {
                    return uncolourable;
                }
                if (uncolourable) {
                    warn_once(
                        WarningId::ChromaticNumberUncolourable,
                        "Found uncolourable graph while doing chromatic number comparison"
                    );
                    return false;
                }
                if (target == 0) {
                    return is_colourable_sat(solver, G, 0);
                }
                return is_colourable_sat(solver, G, target) &&
                       !is_colourable_sat(solver, G, target - 1);
            }
            if (comp == "!=") {
                if (target == UNCOLOURABLE) {
                    return !uncolourable;
                }
                if (uncolourable) {
                    warn_once(
                        WarningId::ChromaticNumberUncolourableNeq,
                        "Found uncolourable graph while doing chromatic number comparison"
                    );
                    return true;
                }
                if (target == 0) {
                    return !is_colourable_sat(solver, G, 0);
                }
                return !is_colourable_sat(solver, G, target) ||
                       is_colourable_sat(solver, G, target - 1);
            }
            if (target == UNCOLOURABLE) {
                throw_meaningless_target();
            }
            if (uncolourable) {
                if (comp == "<=" || comp == "<") {
                    warn_once(
                        WarningId::ChromaticNumberUncolourableOrdering,
                        "Found uncolourable graph using chromatic number comparison"
                    );
                    return false;
                }
                throw_meaningless_graph();
            }
            if (comp == "<=") {
                return is_colourable_sat(solver, G, target);
            }
            if (comp == "<") {
                if (target <= 0) {
                    return false;
                }
                return is_colourable_sat(solver, G, target - 1);
            }
            if (comp == ">=") {
                if (target <= 0) {
                    return true;
                }
                return !is_colourable_sat(solver, G, target - 1);
            }
            if (comp == ">") {
                return !is_colourable_sat(solver, G, target);
            }
            throw std::logic_error(
                "Invalid comparator for chromatic_number (SAT): " + std::string(comp)
            );
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for chromatic_number criterion. Supported: BASIC, "
                "SAT."
            );
    }
}

// ============================================================================
// Circumference Computation Functions
// ============================================================================

inline int compute_circumference(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::BASIC:
            return circumference(G);

        case ComputationMethod::SAT: {
            return circumference_sat(require_sat_solver(ctx, "circumference"), G);
        }

        default:
            throw UnsupportedComputationMethod(
                "Unsupported computation method for circumference. Supported: BASIC, SAT."
            );
    }
}

inline bool check_circumference_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target = criterion.numerator;
    validate_nonnegative_or_sentinel_target(
        "circumference", target, NO_CYCLE_FOUND, "NO_CYCLE_FOUND"
    );
    int c = compute_circumference(G, method, ctx);

    auto throw_meaningless_target = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) + "' not meaningful for NO_CYCLE_FOUND target"
        );
    };
    auto throw_meaningless_graph = [&]() {
        throw std::runtime_error(
            "Comparison '" + std::string(comp) +
            "' not meaningful for acyclic graph (no circumference)"
        );
    };

    if (comp == "==") {
        return c == target;
    }
    if (comp == "!=") {
        return c != target;
    }
    if (target == NO_CYCLE_FOUND) {
        throw_meaningless_target();
    }
    if (c == NO_CYCLE_FOUND) {
        throw_meaningless_graph();
    }
    if (comp == "<=") {
        return c <= target;
    }
    if (comp == "<") {
        return c < target;
    }
    if (comp == ">=") {
        return c >= target;
    }
    if (comp == ">") {
        return c > target;
    }

    throw std::logic_error(
        "Invalid comparator for circumference (" + std::string(computation_method_to_name(method)) +
        "): " + std::string(comp)
    );
}

// ============================================================================
// Circular Chromatic Index Computation Functions (SAT-only)
// ============================================================================

inline std::optional<std::pair<int, int>> compute_circular_chromatic_index(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return circular_chromatic_index_sat(
                require_sat_solver(ctx, "circular_chromatic_index"), G
            );

        case ComputationMethod::CPSAT: {
            return with_cpsat_bound_sat_solver(
                ctx, "circular_chromatic_index",
                [&](SatSolver& solver) { return circular_chromatic_index_cpsat(solver, G); }
            );
        }

        default:
            throw std::runtime_error(
                "Circular chromatic index computation requires SAT or CPSAT algorithm - use "
                "--computation-method sat or --computation-method cpsat"
            );
    }
}

inline bool check_circular_chromatic_index_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target_num = criterion.numerator;
    int target_den = criterion.denominator;

    switch (method) {
        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "circular_chromatic_index criterion");
            // Optimization: For <= comparison, use the direct colourability test.
            if (comp == "<=") {
                bool colourable =
                    is_circularly_edge_colourable_sat(solver, G, target_num, target_den);
                if (!colourable && has_loop(G)) {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableSat,
                        "Found uncolourable graph using circular chromatic index comparison"
                    );
                }
                return colourable;
            }
            // For other comparisons, compute the actual circular chromatic index
            auto cchi_opt = circular_chromatic_index_sat(solver, G);

            if (!cchi_opt.has_value()) {
                if (comp == "==") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableSat,
                        "Found uncolourable graph using circular chromatic index comparison"
                    );
                    return false;
                }
                if (comp == "!=") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableSat,
                        "Found uncolourable graph using circular chromatic index comparison"
                    );
                    return true;
                }
                if (comp == "<") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableSat,
                        "Found uncolourable graph using circular chromatic index comparison"
                    );
                    return false;
                }
                if (comp == ">=" || comp == ">") {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for uncolourable graph"
                    );
                }
                throw std::logic_error(
                    "Invalid comparator for circular chromatic index (SAT): " + std::string(comp)
                );
            }
            auto [actual_num, actual_den] = cchi_opt.value();

            // Compare fractions using cross multiplication: a/b comp c/d ⟺ a*d comp c*b
            long long left = static_cast<long long>(actual_num) * target_den;
            long long right = static_cast<long long>(target_num) * actual_den;

            if (comp == "<") {
                return left < right;
            } else if (comp == ">=") {
                return left >= right;
            } else if (comp == ">") {
                return left > right;
            } else if (comp == "==") {
                return left == right;
            } else if (comp == "!=") {
                return left != right;
            }
            throw std::logic_error(
                "Invalid comparator for circular chromatic index (SAT): " + std::string(comp)
            );
        }

        case ComputationMethod::CPSAT: {
            if (comp == "<=") {
                bool colourable = is_circularly_edge_colourable_cpsat(G, target_num, target_den);
                if (!colourable && has_loop(G)) {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic index comparison "
                        "(CPSAT)"
                    );
                }
                return colourable;
            }
            auto cchi_opt = with_cpsat_bound_sat_solver(
                ctx, "circular_chromatic_index criterion",
                [&](SatSolver& solver) { return circular_chromatic_index_cpsat(solver, G); }
            );

            if (!cchi_opt.has_value()) {
                if (comp == "==") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic index comparison "
                        "(CPSAT)"
                    );
                    return false;
                }
                if (comp == "!=") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic index comparison "
                        "(CPSAT)"
                    );
                    return true;
                }
                if (comp == "<") {
                    warn_once(
                        WarningId::CircularChromaticIndexUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic index comparison "
                        "(CPSAT)"
                    );
                    return false;
                }
                if (comp == ">=" || comp == ">") {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for uncolourable graph"
                    );
                }
                throw std::logic_error(
                    "Invalid comparator for circular chromatic index (CPSAT): " + std::string(comp)
                );
            }
            auto [actual_num, actual_den] = cchi_opt.value();

            long long left = static_cast<long long>(actual_num) * target_den;
            long long right = static_cast<long long>(target_num) * actual_den;

            if (comp == "<") {
                return left < right;
            } else if (comp == ">=") {
                return left >= right;
            } else if (comp == ">") {
                return left > right;
            } else if (comp == "==") {
                return left == right;
            } else if (comp == "!=") {
                return left != right;
            }
            throw std::logic_error(
                "Invalid comparator for circular chromatic index (CPSAT): " + std::string(comp)
            );
        }

        default:
            throw std::runtime_error(
                "Circular chromatic index computation requires SAT or CPSAT algorithm - use "
                "--computation-method sat or --computation-method cpsat"
            );
    }
}

// ============================================================================
// Circular Chromatic Number Computation Functions (SAT-only)
// ============================================================================

inline std::optional<std::pair<int, int>> compute_circular_chromatic_number(
    const Graph& G, ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (method) {
        case ComputationMethod::SAT:
            return circular_chromatic_number_sat(
                require_sat_solver(ctx, "circular_chromatic_number"), G
            );

        case ComputationMethod::CPSAT: {
            return with_cpsat_bound_sat_solver(
                ctx, "circular_chromatic_number",
                [&](SatSolver& solver) { return circular_chromatic_number_cpsat(solver, G); }
            );
        }

        default:
            throw std::runtime_error(
                "Circular chromatic number computation requires SAT or CPSAT algorithm - use "
                "--computation-method sat or --computation-method cpsat"
            );
    }
}

inline bool check_circular_chromatic_number_criterion(
    const Graph& G, const ComparisonCriterion& criterion, ComputationMethod method,
    const ComputationContext& ctx = {}
) {
    std::string_view comp = criterion.comparator;
    int target_num = criterion.numerator;
    int target_den = criterion.denominator;

    switch (method) {
        case ComputationMethod::SAT: {
            SatSolver& solver = require_sat_solver(ctx, "circular_chromatic_number criterion");
            // Optimization: For <= comparison, use the direct colourability test.
            if (comp == "<=") {
                bool colourable = is_circularly_colourable_sat(solver, G, target_num, target_den);
                if (!colourable && has_loop(G)) {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableSat,
                        "Found uncolourable graph using circular chromatic number comparison"
                    );
                }
                return colourable;
            }
            // For other comparisons, compute the actual circular chromatic number
            auto cchn_opt = circular_chromatic_number_sat(solver, G);

            if (!cchn_opt.has_value()) {
                if (comp == "==") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableSat,
                        "Found uncolourable graph using circular chromatic number comparison"
                    );
                    return false;
                }
                if (comp == "!=") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableSat,
                        "Found uncolourable graph using circular chromatic number comparison"
                    );
                    return true;
                }
                if (comp == "<") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableSat,
                        "Found uncolourable graph using circular chromatic number comparison"
                    );
                    return false;
                }
                if (comp == ">=" || comp == ">") {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for uncolourable graph"
                    );
                }
                throw std::logic_error(
                    "Invalid comparator for circular chromatic number (SAT): " + std::string(comp)
                );
            }
            auto [actual_num, actual_den] = cchn_opt.value();

            // Compare fractions using cross multiplication: a/b comp c/d ⟺ a*d comp c*b
            long long left = static_cast<long long>(actual_num) * target_den;
            long long right = static_cast<long long>(target_num) * actual_den;

            if (comp == "<") {
                return left < right;
            } else if (comp == ">=") {
                return left >= right;
            } else if (comp == ">") {
                return left > right;
            } else if (comp == "==") {
                return left == right;
            } else if (comp == "!=") {
                return left != right;
            }
            throw std::logic_error(
                "Invalid comparator for circular chromatic number (SAT): " + std::string(comp)
            );
        }

        case ComputationMethod::CPSAT: {
            if (comp == "<=") {
                bool colourable = is_circularly_colourable_cpsat(G, target_num, target_den);
                if (!colourable && has_loop(G)) {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic number comparison "
                        "(CPSAT)"
                    );
                }
                return colourable;
            }
            auto cchn_opt = with_cpsat_bound_sat_solver(
                ctx, "circular_chromatic_number criterion",
                [&](SatSolver& solver) { return circular_chromatic_number_cpsat(solver, G); }
            );

            if (!cchn_opt.has_value()) {
                if (comp == "==") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic number comparison "
                        "(CPSAT)"
                    );
                    return false;
                }
                if (comp == "!=") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic number comparison "
                        "(CPSAT)"
                    );
                    return true;
                }
                if (comp == "<") {
                    warn_once(
                        WarningId::CircularChromaticNumberUncolourableCpsat,
                        "Found uncolourable graph using circular chromatic number comparison "
                        "(CPSAT)"
                    );
                    return false;
                }
                if (comp == ">=" || comp == ">") {
                    throw std::runtime_error(
                        "Comparison '" + std::string(comp) +
                        "' not meaningful for uncolourable graph"
                    );
                }
                throw std::logic_error(
                    "Invalid comparator for circular chromatic number (CPSAT): " + std::string(comp)
                );
            }
            auto [actual_num, actual_den] = cchn_opt.value();

            long long left = static_cast<long long>(actual_num) * target_den;
            long long right = static_cast<long long>(target_num) * actual_den;

            if (comp == "<") {
                return left < right;
            } else if (comp == ">=") {
                return left >= right;
            } else if (comp == ">") {
                return left > right;
            } else if (comp == "==") {
                return left == right;
            } else if (comp == "!=") {
                return left != right;
            }
            throw std::logic_error(
                "Invalid comparator for circular chromatic number (CPSAT): " + std::string(comp)
            );
        }

        default:
            throw std::runtime_error(
                "Circular chromatic number computation requires SAT or CPSAT algorithm - use "
                "--computation-method sat or --computation-method cpsat"
            );
    }
}

// ============================================================================
//    Other
// ============================================================================

inline bool check_invariant_criterion(
    const Graph& G, InvariantId inv_id, const ComparisonCriterion& criterion,
    ComputationMethod method, const ComputationContext& ctx = {}
) {
    switch (inv_id) {
        case InvariantId::ORDER:
            return check_order_criterion(G, criterion, method, ctx);
        case InvariantId::SIZE:
            return check_size_criterion(G, criterion, method, ctx);
        case InvariantId::MAX_DEG:
            return check_max_deg_criterion(G, criterion, method, ctx);
        case InvariantId::MIN_DEG:
            return check_min_deg_criterion(G, criterion, method, ctx);
        case InvariantId::GIRTH:
            return check_girth_criterion(G, criterion, method, ctx);
        case InvariantId::VERTEX_CONNECTIVITY:
            return check_vertex_connectivity_criterion(G, criterion, method, ctx);
        case InvariantId::EDGE_CONNECTIVITY:
            return check_edge_connectivity_criterion(G, criterion, method, ctx);
        case InvariantId::CYCLIC_CONNECTIVITY:
            return check_cyclic_connectivity_criterion(G, criterion, method, ctx);
        case InvariantId::CUT_VERTICES:
            return check_cut_vertices_criterion(G, criterion, method, ctx);
        case InvariantId::CUT_EDGES:
            return check_cut_edges_criterion(G, criterion, method, ctx);
        case InvariantId::LOOPS:
            return check_loops_criterion(G, criterion, method, ctx);
        case InvariantId::PARALLEL_EDGES:
            return check_parallel_edges_criterion(G, criterion, method, ctx);
        case InvariantId::CHROMATIC_INDEX:
            return check_chromatic_index_criterion(G, criterion, method, ctx);
        case InvariantId::CHROMATIC_NUMBER:
            return check_chromatic_number_criterion(G, criterion, method, ctx);
        case InvariantId::ECD_SIZE:
            return check_ecd_size_criterion(G, criterion, method, ctx);
        case InvariantId::PERFECT_MATCHING_INDEX:
            return check_perfect_matching_index_criterion(G, criterion, method, ctx);
        case InvariantId::CIRCUMFERENCE:
            return check_circumference_criterion(G, criterion, method, ctx);
        case InvariantId::CIRCULAR_CHROMATIC_INDEX:
            return check_circular_chromatic_index_criterion(G, criterion, method, ctx);
        case InvariantId::CIRCULAR_CHROMATIC_NUMBER:
            return check_circular_chromatic_number_criterion(G, criterion, method, ctx);
        case InvariantId::COLOURING_DEFECT:
            return check_colouring_defect_criterion(G, criterion, method, ctx);
        case InvariantId::RESISTANCE:
            return check_resistance_criterion(G, criterion, method, ctx);
        case InvariantId::ODDNESS:
            return check_oddness_criterion(G, criterion, method, ctx);
        case InvariantId::WEAK_ODDNESS:
            return check_weak_oddness_criterion(G, criterion, method, ctx);
        default:
            throw std::runtime_error(
                "Criterion checking not supported for invariant '" +
                std::string(invariant_id_to_name(inv_id)) + "'"
            );
    }
}

}  // namespace ba_graph

#endif  // BA_GRAPH_INVARIANTS_INVARIANT_UTILS_CORE_HPP
