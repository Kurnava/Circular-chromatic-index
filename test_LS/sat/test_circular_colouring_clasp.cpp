// clang-format off
#include "implementation.h"

#include <functional>
#include <map>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
#include <sat/solver_clasp.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_CLASP_SUPPORT

class CircularColouringClaspFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Clasp support not compiled in"; }
};

TEST_F(CircularColouringClaspFastTest, Skipped) {}

#else

Graph single_edge_graph() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    return G;
}

Graph path_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i + 1 < n; ++i) {
        addE(G, Location(i, i + 1));
    }
    return G;
}

Graph cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

Graph two_incident_edges_graph() {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    return G;
}

bool is_valid_edge_circular_colouring(
    const Graph &G, const sat_model::EdgeColouring &colouring, int p, int q
) {
    if (colouring.size() != static_cast<std::size_t>(G.size())) {
        return false;
    }
    return is_valid_circular_edge_colouring(G, p, q, colouring);
}

class CircularColouringClaspFastTest : public ::testing::Test {};

// ===== AllSat tests (clasp-native) =====

namespace {
struct AllSatCount {
    int n;
};
bool allsat_count_cb(std::vector<bool> &, void *d) {
    ++static_cast<AllSatCount *>(d)->n;
    return true;
}
}  // namespace

TEST_F(CircularColouringClaspFastTest, AllSatReturnsFalseForUnsatisfiableFormula) {
    ClaspAllSatSolver s;
    CNF cnf(1, {Clause{Lit(0, false)}, Clause{Lit(0, true)}});
    AllSatCount c{0};
    EXPECT_FALSE(s.enumerate(cnf, allsat_count_cb, &c));
    EXPECT_EQ(c.n, 0);
}

TEST_F(CircularColouringClaspFastTest, AllSatReturnsTrueForSatisfiableFormula) {
    ClaspAllSatSolver s;
    CNF cnf(2, std::vector({Clause{Lit(0, false)}, Clause{Lit(1, false)}}));
    AllSatCount c{0};
    EXPECT_TRUE(s.enumerate(cnf, allsat_count_cb, &c));
    EXPECT_EQ(c.n, 1);
}

TEST_F(CircularColouringClaspFastTest, AllSatEnumeratesEmptySatisfiableFormula) {
    ClaspAllSatSolver s;
    CNF cnf(0, {});
    AllSatCount c{0};
    EXPECT_TRUE(s.enumerate(cnf, allsat_count_cb, &c));
    EXPECT_EQ(c.n, 1);
}

TEST_F(CircularColouringClaspFastTest, AllSatEnumeratesAllModelsForSimpleCNF) {
    ClaspAllSatSolver s;
    CNF cnf = CNF(
        3, std::vector({Clause{Lit(0, false), Lit(1, true)}, Clause{Lit(1, false), Lit(2, true)}})
    );
    AllSatCount c{0};
    EXPECT_TRUE(s.enumerate(cnf, allsat_count_cb, &c));
    EXPECT_EQ(c.n, 4);
}

TEST_F(CircularColouringClaspFastTest, AllSatRespectsMaxSolutionsOne) {
    ClaspAllSatSolver s;
    CNF cnf(3, {});
    AllSatCount c{0};
    EXPECT_TRUE(s.enumerate(cnf, allsat_count_cb, &c, 1));
    EXPECT_EQ(c.n, 1);
}

TEST_F(CircularColouringClaspFastTest, AllSatEnumeratesPartialFormula) {
    ClaspAllSatSolver s;
    CNF cnf = CNF(
        3, std::vector({Clause{Lit(0, false), Lit(1, true)}, Clause{Lit(1, false), Lit(2, true)}})
    );
    AllSatCount c{0};
    EXPECT_TRUE(s.enumerate(cnf, allsat_count_cb, &c));
    EXPECT_EQ(c.n, 4);
}

// ===== Cross-validation clasp vs kissat =====

#if BA_GRAPH_HAS_KISSAT_SUPPORT

TEST_F(CircularColouringClaspFastTest, VertexClaspAgreesWithSatOnSelectedSmallCases) {
    KissatSolver solver;
    struct Case {
        std::function<Graph()> factory;
        int p;
        int q;
    };
    const std::vector<Case> cases = {
        {[] { return single_edge_graph(); }, 2, 1},
        {[] { return single_edge_graph(); }, 1, 1},
        {[] { return cycle_graph(5); }, 5, 2},
        {[] { return cycle_graph(5); }, 2, 1},
        {[] { return create_complete_graph(4); }, 4, 1},
        {[] { return create_complete_graph(4); }, 3, 1},
    };

    for (const auto &test : cases) {
        Graph G = test.factory();
        EXPECT_EQ(
            is_circularly_colourable_sat(ClaspSatSolver(1), G, test.p, test.q),
            is_circularly_colourable_sat(solver, G, test.p, test.q)
        );
    }
}

TEST_F(CircularColouringClaspFastTest, EdgeClaspAgreesWithSatOnSelectedSmallCases) {
    KissatSolver solver;
    struct Case {
        std::function<Graph()> factory;
        int p;
        int q;
    };
    const std::vector<Case> cases = {
        {[] { return single_edge_graph(); }, 1, 1},
        {[] { return two_incident_edges_graph(); }, 1, 1},
        {[] { return cycle_graph(3); }, 3, 1},
        {[] { return cycle_graph(3); }, 2, 1},
        {[] { return create_complete_graph(4); }, 3, 1},
        {[] { return create_complete_graph(4); }, 2, 1},
    };

    for (const auto &test : cases) {
        Graph G = test.factory();
        EXPECT_EQ(
            is_circularly_edge_colourable_sat(ClaspSatSolver(1), G, test.p, test.q),
            is_circularly_edge_colourable_sat(solver, G, test.p, test.q)
        );
    }
}

#endif

#endif
