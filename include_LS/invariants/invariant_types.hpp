#ifndef BA_GRAPH_INVARIANTS_INVARIANT_TYPES_HPP
#define BA_GRAPH_INVARIANTS_INVARIANT_TYPES_HPP

#include <array>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>

namespace ba_graph {

class Graph;
class SatSolver;

enum class ComputationMethod {
    BASIC,
    SAT,
    CPSAT,
};

inline std::optional<ComputationMethod> parse_computation_method(const std::string& str) {
    if (str == "basic") {
        return ComputationMethod::BASIC;
    }
    if (str == "sat") {
        return ComputationMethod::SAT;
    }
    if (str == "cpsat") {
        return ComputationMethod::CPSAT;
    }
    return std::nullopt;
}

inline std::string_view computation_method_to_name(ComputationMethod method) {
    switch (method) {
        case ComputationMethod::BASIC:
            return "basic";
        case ComputationMethod::SAT:
            return "sat";
        case ComputationMethod::CPSAT:
            return "cpsat";
    }
    throw std::logic_error("Unhandled ComputationMethod in computation_method_to_name");
}

struct ComputationContext {
    SatSolver* sat_solver = nullptr;
    // Cache of pre-parsed H-graphs for H-colourability checks.
    // Key: full custom invariant name (e.g. "hcolourable-P" or "hcolourable-s6-...").
    // filter_graphs uses this cache from a single-threaded filtering path; it is not synchronized.
    mutable std::unordered_map<std::string, std::shared_ptr<Graph>> h_graph_cache;

    ComputationContext() = default;
    explicit ComputationContext(SatSolver* solver)
        : sat_solver(solver) {}
};

class UnsupportedComputationMethod : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};

enum class ComparisonValueType { Integer, Fraction };

struct ComparisonCriterion {
    std::string_view comparator;
    int numerator;
    int denominator;
    ComparisonValueType type;

    ComparisonCriterion() = default;

    ComparisonCriterion(std::string_view comp, int val)
        : comparator(comp),
          numerator(val),
          denominator(1),
          type(ComparisonValueType::Integer) {}

    ComparisonCriterion(std::string_view comp, int num, int den)
        : comparator(comp),
          numerator(num),
          denominator(den),
          type(den == 1 ? ComparisonValueType::Integer : ComparisonValueType::Fraction) {}
};

inline bool compareValue(int graphValue, int argValue, std::string_view comparator) {
    if (comparator == "<") {
        return graphValue < argValue;
    } else if (comparator == "<=") {
        return graphValue <= argValue;
    } else if (comparator == "==") {
        return graphValue == argValue;
    } else if (comparator == ">=") {
        return graphValue >= argValue;
    } else if (comparator == ">") {
        return graphValue > argValue;
    } else if (comparator == "!=") {
        return graphValue != argValue;
    } else {
        throw std::invalid_argument("Invalid comparator: " + std::string(comparator));
    }
}

inline void validate_nonnegative_or_sentinel_target(
    std::string_view invariant_name, int target, int sentinel, std::string_view sentinel_name
) {
    if (target < 0 && target != sentinel) {
        throw std::invalid_argument(
            std::string(invariant_name) + " criterion target must be non-negative or " +
            std::string(sentinel_name)
        );
    }
}

struct InvariantNames {
    static constexpr const char* ORDER = "order";
    static constexpr const char* SIZE = "size";
    static constexpr const char* MAX_DEG = "max-deg";
    static constexpr const char* MIN_DEG = "min-deg";
    static constexpr const char* GIRTH = "girth";
    static constexpr const char* VERTEX_CONNECTIVITY = "vertex-connectivity";
    static constexpr const char* EDGE_CONNECTIVITY = "edge-connectivity";
    static constexpr const char* CYCLIC_CONNECTIVITY = "cyclic-connectivity";
    static constexpr const char* CUT_VERTICES = "cut-vertices";
    static constexpr const char* CUT_EDGES = "cut-edges";
    static constexpr const char* LOOPS = "loops";
    static constexpr const char* PARALLEL_EDGES = "parallel-edges";
    static constexpr const char* CHROMATIC_INDEX = "chromatic-index";
    static constexpr const char* CHROMATIC_NUMBER = "chromatic-number";
    static constexpr const char* ECD_SIZE = "ecd-size";
    static constexpr const char* PERFECT_MATCHING_INDEX = "perfect-matching-index";
    static constexpr const char* CIRCUMFERENCE = "circumference";
    static constexpr const char* CIRCULAR_CHROMATIC_NUMBER = "circular-chromatic-number";
    static constexpr const char* CIRCULAR_CHROMATIC_INDEX = "circular-chromatic-index";

    static constexpr const char* HAMILTONIAN = "hamiltonian";
    static constexpr const char* HYPOHAMILTONIAN = "hypohamiltonian";
    static constexpr const char* SIMPLE = "simple";
    static constexpr const char* ACYCLIC = "acyclic";
    static constexpr const char* CLAW_FREE = "claw-free";
    static constexpr const char* BIPARTITE = "bipartite";
    static constexpr const char* QUASI_LINE_GRAPH = "quasi-line-graph";
    static constexpr const char* PERMUTATION_GRAPH = "permutation-graph";
    static constexpr const char* CHROMATIC_NUMBER_VERTEX_CRITICAL =
        "chromatic-number-vertex-critical";
    static constexpr const char* CHROMATIC_NUMBER_EDGE_CRITICAL = "chromatic-number-edge-critical";
    static constexpr const char* CHROMATIC_INDEX_VERTEX_CRITICAL =
        "chromatic-index-vertex-critical";
    static constexpr const char* CHROMATIC_INDEX_EDGE_CRITICAL = "chromatic-index-edge-critical";
    static constexpr const char* CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL =
        "circular-chromatic-number-vertex-critical";
    static constexpr const char* CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL =
        "circular-chromatic-number-edge-critical";
    static constexpr const char* CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL =
        "circular-chromatic-index-vertex-critical";
    static constexpr const char* CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL =
        "circular-chromatic-index-edge-critical";
    static constexpr const char* CRITICAL_SNARK = "critical-snark";
    static constexpr const char* EULERIAN = "eulerian";
    static constexpr const char* IRREDUCIBLE_SNARK = "irreducible-snark";
    static constexpr const char* COLOURING_DEFECT = "snark-colouring-defect";
    static constexpr const char* RESISTANCE = "resistance";
    static constexpr const char* ODDNESS = "oddness";
    static constexpr const char* WEAK_ODDNESS = "weak-oddness";
};

enum class InvariantId {
    ORDER,
    SIZE,
    MAX_DEG,
    MIN_DEG,
    GIRTH,
    VERTEX_CONNECTIVITY,
    EDGE_CONNECTIVITY,
    CYCLIC_CONNECTIVITY,
    CUT_VERTICES,
    CUT_EDGES,
    LOOPS,
    PARALLEL_EDGES,
    CHROMATIC_INDEX,
    CHROMATIC_NUMBER,
    ECD_SIZE,
    PERFECT_MATCHING_INDEX,
    CIRCUMFERENCE,
    CIRCULAR_CHROMATIC_NUMBER,
    CIRCULAR_CHROMATIC_INDEX,
    HAMILTONIAN,
    HYPOHAMILTONIAN,
    SIMPLE,
    ACYCLIC,
    CLAW_FREE,
    BIPARTITE,
    QUASI_LINE_GRAPH,
    PERMUTATION_GRAPH,
    CHROMATIC_NUMBER_VERTEX_CRITICAL,
    CHROMATIC_NUMBER_EDGE_CRITICAL,
    CHROMATIC_INDEX_VERTEX_CRITICAL,
    CHROMATIC_INDEX_EDGE_CRITICAL,
    CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL,
    CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL,
    CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL,
    CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL,
    CRITICAL_SNARK,
    EULERIAN,
    IRREDUCIBLE_SNARK,
    COLOURING_DEFECT,
    RESISTANCE,
    ODDNESS,
    WEAK_ODDNESS,
};

inline std::string_view invariant_id_to_name(InvariantId id) {
    switch (id) {
        case InvariantId::ORDER:
            return InvariantNames::ORDER;
        case InvariantId::SIZE:
            return InvariantNames::SIZE;
        case InvariantId::MAX_DEG:
            return InvariantNames::MAX_DEG;
        case InvariantId::MIN_DEG:
            return InvariantNames::MIN_DEG;
        case InvariantId::GIRTH:
            return InvariantNames::GIRTH;
        case InvariantId::VERTEX_CONNECTIVITY:
            return InvariantNames::VERTEX_CONNECTIVITY;
        case InvariantId::EDGE_CONNECTIVITY:
            return InvariantNames::EDGE_CONNECTIVITY;
        case InvariantId::CYCLIC_CONNECTIVITY:
            return InvariantNames::CYCLIC_CONNECTIVITY;
        case InvariantId::CUT_VERTICES:
            return InvariantNames::CUT_VERTICES;
        case InvariantId::CUT_EDGES:
            return InvariantNames::CUT_EDGES;
        case InvariantId::LOOPS:
            return InvariantNames::LOOPS;
        case InvariantId::PARALLEL_EDGES:
            return InvariantNames::PARALLEL_EDGES;
        case InvariantId::CHROMATIC_INDEX:
            return InvariantNames::CHROMATIC_INDEX;
        case InvariantId::CHROMATIC_NUMBER:
            return InvariantNames::CHROMATIC_NUMBER;
        case InvariantId::ECD_SIZE:
            return InvariantNames::ECD_SIZE;
        case InvariantId::PERFECT_MATCHING_INDEX:
            return InvariantNames::PERFECT_MATCHING_INDEX;
        case InvariantId::CIRCUMFERENCE:
            return InvariantNames::CIRCUMFERENCE;
        case InvariantId::CIRCULAR_CHROMATIC_NUMBER:
            return InvariantNames::CIRCULAR_CHROMATIC_NUMBER;
        case InvariantId::CIRCULAR_CHROMATIC_INDEX:
            return InvariantNames::CIRCULAR_CHROMATIC_INDEX;
        case InvariantId::HAMILTONIAN:
            return InvariantNames::HAMILTONIAN;
        case InvariantId::HYPOHAMILTONIAN:
            return InvariantNames::HYPOHAMILTONIAN;
        case InvariantId::SIMPLE:
            return InvariantNames::SIMPLE;
        case InvariantId::ACYCLIC:
            return InvariantNames::ACYCLIC;
        case InvariantId::CLAW_FREE:
            return InvariantNames::CLAW_FREE;
        case InvariantId::BIPARTITE:
            return InvariantNames::BIPARTITE;
        case InvariantId::QUASI_LINE_GRAPH:
            return InvariantNames::QUASI_LINE_GRAPH;
        case InvariantId::PERMUTATION_GRAPH:
            return InvariantNames::PERMUTATION_GRAPH;
        case InvariantId::CHROMATIC_NUMBER_VERTEX_CRITICAL:
            return InvariantNames::CHROMATIC_NUMBER_VERTEX_CRITICAL;
        case InvariantId::CHROMATIC_NUMBER_EDGE_CRITICAL:
            return InvariantNames::CHROMATIC_NUMBER_EDGE_CRITICAL;
        case InvariantId::CHROMATIC_INDEX_VERTEX_CRITICAL:
            return InvariantNames::CHROMATIC_INDEX_VERTEX_CRITICAL;
        case InvariantId::CHROMATIC_INDEX_EDGE_CRITICAL:
            return InvariantNames::CHROMATIC_INDEX_EDGE_CRITICAL;
        case InvariantId::CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL:
            return InvariantNames::CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL;
        case InvariantId::CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL:
            return InvariantNames::CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL;
        case InvariantId::CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL:
            return InvariantNames::CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL;
        case InvariantId::CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL:
            return InvariantNames::CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL;
        case InvariantId::CRITICAL_SNARK:
            return InvariantNames::CRITICAL_SNARK;
        case InvariantId::EULERIAN:
            return InvariantNames::EULERIAN;
        case InvariantId::IRREDUCIBLE_SNARK:
            return InvariantNames::IRREDUCIBLE_SNARK;
        case InvariantId::COLOURING_DEFECT:
            return InvariantNames::COLOURING_DEFECT;
        case InvariantId::RESISTANCE:
            return InvariantNames::RESISTANCE;
        case InvariantId::ODDNESS:
            return InvariantNames::ODDNESS;
        case InvariantId::WEAK_ODDNESS:
            return InvariantNames::WEAK_ODDNESS;
    }
    throw std::logic_error("Unhandled InvariantId in invariant_id_to_name");
}

inline std::optional<InvariantId> try_parse_invariant_id(std::string_view name) {
    if (name == InvariantNames::ORDER) {
        return InvariantId::ORDER;
    }
    if (name == InvariantNames::SIZE) {
        return InvariantId::SIZE;
    }
    if (name == InvariantNames::MAX_DEG) {
        return InvariantId::MAX_DEG;
    }
    if (name == InvariantNames::MIN_DEG) {
        return InvariantId::MIN_DEG;
    }
    if (name == InvariantNames::GIRTH) {
        return InvariantId::GIRTH;
    }
    if (name == InvariantNames::VERTEX_CONNECTIVITY) {
        return InvariantId::VERTEX_CONNECTIVITY;
    }
    if (name == InvariantNames::EDGE_CONNECTIVITY) {
        return InvariantId::EDGE_CONNECTIVITY;
    }
    if (name == InvariantNames::CYCLIC_CONNECTIVITY) {
        return InvariantId::CYCLIC_CONNECTIVITY;
    }
    if (name == InvariantNames::CUT_VERTICES) {
        return InvariantId::CUT_VERTICES;
    }
    if (name == InvariantNames::CUT_EDGES) {
        return InvariantId::CUT_EDGES;
    }
    if (name == InvariantNames::LOOPS) {
        return InvariantId::LOOPS;
    }
    if (name == InvariantNames::PARALLEL_EDGES) {
        return InvariantId::PARALLEL_EDGES;
    }
    if (name == InvariantNames::CHROMATIC_INDEX) {
        return InvariantId::CHROMATIC_INDEX;
    }
    if (name == InvariantNames::CHROMATIC_NUMBER) {
        return InvariantId::CHROMATIC_NUMBER;
    }
    if (name == InvariantNames::ECD_SIZE) {
        return InvariantId::ECD_SIZE;
    }
    if (name == InvariantNames::PERFECT_MATCHING_INDEX) {
        return InvariantId::PERFECT_MATCHING_INDEX;
    }
    if (name == InvariantNames::CIRCUMFERENCE) {
        return InvariantId::CIRCUMFERENCE;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_NUMBER) {
        return InvariantId::CIRCULAR_CHROMATIC_NUMBER;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_INDEX) {
        return InvariantId::CIRCULAR_CHROMATIC_INDEX;
    }
    if (name == InvariantNames::HAMILTONIAN) {
        return InvariantId::HAMILTONIAN;
    }
    if (name == InvariantNames::HYPOHAMILTONIAN) {
        return InvariantId::HYPOHAMILTONIAN;
    }
    if (name == InvariantNames::SIMPLE) {
        return InvariantId::SIMPLE;
    }
    if (name == InvariantNames::ACYCLIC) {
        return InvariantId::ACYCLIC;
    }
    if (name == InvariantNames::CLAW_FREE) {
        return InvariantId::CLAW_FREE;
    }
    if (name == InvariantNames::BIPARTITE) {
        return InvariantId::BIPARTITE;
    }
    if (name == InvariantNames::QUASI_LINE_GRAPH) {
        return InvariantId::QUASI_LINE_GRAPH;
    }
    if (name == InvariantNames::PERMUTATION_GRAPH) {
        return InvariantId::PERMUTATION_GRAPH;
    }
    if (name == InvariantNames::CHROMATIC_NUMBER_VERTEX_CRITICAL) {
        return InvariantId::CHROMATIC_NUMBER_VERTEX_CRITICAL;
    }
    if (name == InvariantNames::CHROMATIC_NUMBER_EDGE_CRITICAL) {
        return InvariantId::CHROMATIC_NUMBER_EDGE_CRITICAL;
    }
    if (name == InvariantNames::CHROMATIC_INDEX_VERTEX_CRITICAL) {
        return InvariantId::CHROMATIC_INDEX_VERTEX_CRITICAL;
    }
    if (name == InvariantNames::CHROMATIC_INDEX_EDGE_CRITICAL) {
        return InvariantId::CHROMATIC_INDEX_EDGE_CRITICAL;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL) {
        return InvariantId::CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL) {
        return InvariantId::CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL) {
        return InvariantId::CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL;
    }
    if (name == InvariantNames::CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL) {
        return InvariantId::CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL;
    }
    if (name == InvariantNames::CRITICAL_SNARK) {
        return InvariantId::CRITICAL_SNARK;
    }
    if (name == InvariantNames::EULERIAN) {
        return InvariantId::EULERIAN;
    }
    if (name == InvariantNames::IRREDUCIBLE_SNARK) {
        return InvariantId::IRREDUCIBLE_SNARK;
    }
    if (name == InvariantNames::COLOURING_DEFECT) {
        return InvariantId::COLOURING_DEFECT;
    }
    if (name == InvariantNames::RESISTANCE) {
        return InvariantId::RESISTANCE;
    }
    if (name == InvariantNames::ODDNESS) {
        return InvariantId::ODDNESS;
    }
    if (name == InvariantNames::WEAK_ODDNESS) {
        return InvariantId::WEAK_ODDNESS;
    }
    return std::nullopt;
}

inline InvariantId parse_invariant_id(std::string_view name) {
    auto id = try_parse_invariant_id(name);
    if (!id.has_value()) {
        throw std::invalid_argument("Unknown invariant name: " + std::string(name));
    }
    return id.value();
}

inline constexpr std::array<std::string_view, 42> ALL_INVARIANT_NAMES = {
    InvariantNames::ORDER,
    InvariantNames::SIZE,
    InvariantNames::MAX_DEG,
    InvariantNames::MIN_DEG,
    InvariantNames::GIRTH,
    InvariantNames::VERTEX_CONNECTIVITY,
    InvariantNames::EDGE_CONNECTIVITY,
    InvariantNames::CYCLIC_CONNECTIVITY,
    InvariantNames::CUT_VERTICES,
    InvariantNames::CUT_EDGES,
    InvariantNames::LOOPS,
    InvariantNames::PARALLEL_EDGES,
    InvariantNames::CHROMATIC_INDEX,
    InvariantNames::CHROMATIC_NUMBER,
    InvariantNames::ECD_SIZE,
    InvariantNames::PERFECT_MATCHING_INDEX,
    InvariantNames::CIRCUMFERENCE,
    InvariantNames::CIRCULAR_CHROMATIC_NUMBER,
    InvariantNames::CIRCULAR_CHROMATIC_INDEX,
    InvariantNames::HAMILTONIAN,
    InvariantNames::HYPOHAMILTONIAN,
    InvariantNames::SIMPLE,
    InvariantNames::ACYCLIC,
    InvariantNames::CLAW_FREE,
    InvariantNames::BIPARTITE,
    InvariantNames::QUASI_LINE_GRAPH,
    InvariantNames::PERMUTATION_GRAPH,
    InvariantNames::CHROMATIC_NUMBER_VERTEX_CRITICAL,
    InvariantNames::CHROMATIC_NUMBER_EDGE_CRITICAL,
    InvariantNames::CHROMATIC_INDEX_VERTEX_CRITICAL,
    InvariantNames::CHROMATIC_INDEX_EDGE_CRITICAL,
    InvariantNames::CIRCULAR_CHROMATIC_NUMBER_VERTEX_CRITICAL,
    InvariantNames::CIRCULAR_CHROMATIC_NUMBER_EDGE_CRITICAL,
    InvariantNames::CIRCULAR_CHROMATIC_INDEX_VERTEX_CRITICAL,
    InvariantNames::CIRCULAR_CHROMATIC_INDEX_EDGE_CRITICAL,
    InvariantNames::CRITICAL_SNARK,
    InvariantNames::EULERIAN,
    InvariantNames::IRREDUCIBLE_SNARK,
    InvariantNames::COLOURING_DEFECT,
    InvariantNames::RESISTANCE,
    InvariantNames::ODDNESS,
    InvariantNames::WEAK_ODDNESS
};

}  // namespace ba_graph

#endif  // BA_GRAPH_INVARIANTS_INVARIANT_TYPES_HPP
