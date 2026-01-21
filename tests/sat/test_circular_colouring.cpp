// clang-format off
#include "implementation.h"

#include <graphs.hpp>
#include <gtest/gtest.h>
#include <io/unified_io.hpp>
#include <operations.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT
// Skip all tests if Kissat support is not available
class CNFCircularColouringTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

class CircularVertexColouringTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

class CircularEdgeColouringTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

class CircularCriticalityTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

// Empty test implementations to satisfy the build
TEST_F(CNFCircularColouringTest, Skipped) {}
TEST_F(CircularVertexColouringTest, Skipped) {}
TEST_F(CircularEdgeColouringTest, Skipped) {}
TEST_F(CircularCriticalityTest, Skipped) {}

#else

class CNFCircularColouringTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

class CircularVertexColouringTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

class CircularEdgeColouringTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

class CircularCriticalityTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

// ======== CNF Circular Colouring Tests ========

TEST_F(CNFCircularColouringTest, CircularEdgeColouringWithLoops) {
    Graph g_with_loop(create_empty_graph(2));
    addE(g_with_loop, Location(0, 1));
    addE(g_with_loop, Location(0, 0));  // Add a loop

    // CNF circular edge coloring should return unsatisfiable for graphs with loops
    CNF cnf_result = cnf_circular_edge_colouring(g_with_loop, 5, 2);
    EXPECT_EQ(cnf_result, cnf_unsatisfiable);

    std::map<Edge, int> empty_precolouring;
    CNF cnf_result_with_precolour =
        cnf_circular_edge_colouring(g_with_loop, 5, 2, empty_precolouring);
    EXPECT_EQ(cnf_result_with_precolour, cnf_unsatisfiable);
}

TEST_F(CNFCircularColouringTest, CircularVertexColouringWithLoops) {
    Graph g_with_loop(create_empty_graph(2));
    addE(g_with_loop, Location(0, 1));
    addE(g_with_loop, Location(0, 0));  // Add a loop

    // Test CNF circular vertex coloring with loops
    CNF cnf_vertex_result = cnf_circular_vertex_colouring(g_with_loop, 5, 2);
    EXPECT_EQ(cnf_vertex_result, cnf_unsatisfiable);

    std::map<Vertex, int> empty_vertex_precolouring;
    CNF cnf_vertex_result_with_precolour =
        cnf_circular_vertex_colouring(g_with_loop, 5, 2, empty_vertex_precolouring);
    EXPECT_EQ(cnf_vertex_result_with_precolour, cnf_unsatisfiable);
}

// ======== Circular Vertex Colouring Tests ========

TEST_F(CircularVertexColouringTest, BasicVertexColouring) {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(1, 3));
    addE(G, Location(2, 3));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 0, 1));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 1, 1));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 2, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 3, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 7, 2));
}

TEST_F(CircularVertexColouringTest, CircuitGraphs) {
    Graph G(create_circuit(5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 4, 2));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 99, 40));
}

TEST_F(CircularVertexColouringTest, GraphsWithLoops) {
    Graph g_with_loop(create_empty_graph(2));
    addE(g_with_loop, Location(0, 1));
    addE(g_with_loop, Location(0, 0));  // Add a loop

    // Test SAT-based circular vertex coloring with loops
    EXPECT_FALSE(is_circularly_colourable_sat(solver, g_with_loop, 5, 2));
    EXPECT_FALSE(circular_chromatic_number_sat(solver, g_with_loop).has_value());
}

TEST_F(CircularVertexColouringTest, CircularChromaticNumber) {
    Graph G(create_circuit(5));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 2));

    Graph K4(create_complete_graph(4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, K4).value(), std::pair(4, 1));
}

// ======== Circular Edge Colouring Tests ========

TEST_F(CircularEdgeColouringTest, BasicEdgeColouring) {
    Graph G(create_complete_graph(4));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 6, 2));
}

TEST_F(CircularEdgeColouringTest, EdgePrecolouring) {
    Graph G(create_complete_graph(4));
    std::map<Edge, int> precolouring;
    Edge e01 = G[0].find(Location(0, 1))->e();
    Edge e02 = G[0].find(Location(0, 2))->e();

    precolouring[e01] = 2;
    precolouring[e02] = 2;
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 3, 1, precolouring));

    precolouring[e02] = 8;
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 9, 3, precolouring));
}

TEST_F(CircularEdgeColouringTest, PetersenGraph) {
    Graph G(create_petersen());
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 11, 3));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 7, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 32, 9));
}

TEST_F(CircularEdgeColouringTest, CompleteGraphs) {
    Graph G1(create_complete_graph(5));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G1, 5, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G1, 4, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G1, 9, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G1, 14, 3));
}

TEST_F(CircularEdgeColouringTest, CirculantGraphs) {
    Graph G2 = create_circulant_1_2(7);  // k=7 is valid (>=2)
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G2, 9, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G2, 4, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G2, 14, 3));

    Graph G3 = create_circulant_1_2(5);  // k=5 is valid (>=2)
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G3, 9, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G3, 4, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G3, 14, 3));
}

TEST_F(CircularEdgeColouringTest, GraphsWithLoops) {
    Graph g_with_loop(create_empty_graph(2));
    addE(g_with_loop, Location(0, 1));
    addE(g_with_loop, Location(0, 0));  // Add a loop

    EXPECT_FALSE(circular_chromatic_index_sat(solver, g_with_loop).has_value());

    // Test circular chromatic index for graph with loops (sparse6: :I@ESySeUPgd_\F)
    Factory f_loop_test;
    Graph g_loop_test = read_graph_autodetect(":I@ESySeUPgd_\\\\F", f_loop_test);

    // Verify this graph has loops
    EXPECT_TRUE(has_loop(g_loop_test));

    // Circular chromatic index should be undefined for graphs with loops
    auto cchi_loop_test = circular_chromatic_index_sat(solver, g_loop_test);
    EXPECT_FALSE(cchi_loop_test.has_value());
}

TEST_F(CircularEdgeColouringTest, CircularChromaticIndex) {
    Graph G(create_petersen());
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(11, 3));
}

// ======== Circular Criticality Tests ========

TEST_F(CircularCriticalityTest, VertexCritical) {
    Graph C5(create_circuit(5));
    EXPECT_TRUE(is_cchn_vertex_critical_sat(solver, C5));

    Graph K4(create_complete_graph(4));
    EXPECT_TRUE(is_cchn_vertex_critical_sat(solver, K4));
}

TEST_F(CircularCriticalityTest, NonVertexCritical) {
    // A graph that is not vertex-critical
    // Two K4s joined by an edge. ccn = 4.
    // Removing a vertex from one K4 leaves the other K4, so ccn is still 4.
    Graph K4_1(create_complete_graph(4));
    Graph K4_2(create_complete_graph(4));
    add_graph(K4_1, K4_2, K4_1.order());
    // Add a bridge between vertex 3 of K4_1 and vertex 0 of K4_2 (which is now vertex 4)
    addE(K4_1, Location(3, 4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, K4_1).value(), std::pair(4, 1));
    EXPECT_FALSE(is_cchn_vertex_critical_sat(solver, K4_1));
}

TEST_F(CircularCriticalityTest, EdgeCritical) {
    Graph PG(create_petersen());
    EXPECT_TRUE(is_cchi_critical(solver, PG));
}

TEST_F(CircularCriticalityTest, SmallCchiCriticalGraphs) {
    std::vector<std::string> critical_graphs = {"D~{", "ETno", "FUZv_", "FFzvO", "FUzro"};

    for (const auto& g6 : critical_graphs) {
        Graph G = read_graph_autodetect(g6);
        EXPECT_TRUE(is_cchi_critical(solver, G));
    }
}

TEST_F(CircularCriticalityTest, SmallNonCchiCriticalGraphs) {
    std::vector<std::string> not_critical_graphs = {"L???CB?oJ_DooK", "L???CB?NBEWKoW"};

    for (const auto& g6 : not_critical_graphs) {
        Graph G = read_graph_autodetect(g6);
        EXPECT_FALSE(is_cchi_critical(solver, G));
    }
}

// =========================================================================
//  HELPER UTILITIES
// =========================================================================

class KissatSolverWrapper {
public:
    KissatSolver solver;
};

Graph create_complete_bipartite(int n1, int n2) {
    Graph G(create_empty_graph(n1 + n2));
    // Partition A: 0 to n1-1
    // Partition B: n1 to n1+n2-1
    for (int i = 0; i < n1; ++i) {
        for (int j = 0; j < n2; ++j) {
            addE(G, Location(i, n1 + j));
        }
    }
    return G;
}

class CNFCircularColouringTest : public ::testing::Test { protected: KissatSolver solver; };
class CircularVertexColouringTest : public ::testing::Test { protected: KissatSolver solver; };
class CircularEdgeColouringTest : public ::testing::Test { protected: KissatSolver solver; };

// =========================================================================
//  SECTION 1: PRIMITIVE GRAPHS (Sanity Checks)
// =========================================================================

// --- 1.1: Triviality & Atoms (0-2 vertices) ---

TEST_F(CircularVertexColouringTest, T001_EmptyGraph_0V) {
    Graph G(create_empty_graph(0));
    // 0 vertices -> always satisfiable
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
}

TEST_F(CircularVertexColouringTest, T002_SingleVertex_1V) {
    Graph G(create_empty_graph(1));
    // 1 vertex -> 1 color needed
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
    // Valid ratio check
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 2, 1));
}

TEST_F(CircularVertexColouringTest, T003_TwoVertices_NoEdge) {
    Graph G(create_empty_graph(2));
    // Independent set -> 1 color
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
}

TEST_F(CircularVertexColouringTest, T004_TwoVertices_WithEdge) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    // K2 implies p/q >= 2.
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 1, 1)); // Ratio 1.0 < 2
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 3, 2)); // Ratio 1.5 < 2
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 2, 1));  // Ratio 2.0 >= 2
}

// --- 1.2: Bipartite Structures (Trees, Paths) -> Chi_c = 2 ---

TEST_F(CircularVertexColouringTest, T010_Path_P3) {
    // 0-1-2
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1)); addE(G, Location(1, 2));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T011_Path_P4) {
    // 0-1-2-3
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1)); addE(G, Location(1, 2)); addE(G, Location(2, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T012_Path_Long) {
    // Path length 9
    Graph G(create_empty_graph(10));
    for(int i=0; i<9; ++i) addE(G, Location(i, i+1));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T020_Star_S3) {
    // Center 0 connected to 1, 2, 3
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1)); addE(G, Location(0, 2)); addE(G, Location(0, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T021_BinaryTree_Depth2) {
    // Tree structure is bipartite
    Graph G(create_empty_graph(7));
    addE(G, Location(0, 1)); addE(G, Location(0, 2));
    addE(G, Location(1, 3)); addE(G, Location(1, 4));
    addE(G, Location(2, 5)); addE(G, Location(2, 6));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T022_Caterpillar) {
    // Path spine with legs -> bipartite
    Graph G(create_empty_graph(6));
    addE(G, Location(0, 1)); addE(G, Location(1, 2)); addE(G, Location(2, 3));
    addE(G, Location(1, 4)); addE(G, Location(2, 5));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 1.3: Disconnected Components -> max(Chi_c(components)) ---

TEST_F(CircularVertexColouringTest, T030_Disconnected_TwoEdges) {
    // K2 U K2
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1)); addE(G, Location(2, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T031_Disconnected_Triangle_And_Isolated) {
    // K3 U K1 -> Result 3
    Graph G(create_circuit(3));
    addV(G, 1);
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 1.4: Ratio Boundary Checks (Precision Tests) ---

TEST_F(CircularVertexColouringTest, T040_Triangle_TightFail) {
    // K3 needs 3.0. Test 2.9
    Graph G(create_complete_graph(3));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 29, 10));
}

TEST_F(CircularVertexColouringTest, T041_Triangle_Exact) {
    // K3 needs 3.0. Test 3.0
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 3, 1));
}

TEST_F(CircularVertexColouringTest, T042_Triangle_Relaxed) {
    // K3 needs 3.0. Test 3.33
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 10, 3));
}

TEST_F(CircularVertexColouringTest, T043_C5_TightFail) {
    // C5 needs 2.5. Test 2.4
    Graph G(create_circuit(5));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 12, 5));
}

TEST_F(CircularVertexColouringTest, T044_C5_Exact) {
    // C5 needs 2.5. Test 2.5
    Graph G(create_circuit(5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2));
}

// --- 1.5: Small Named Subgraphs ---

TEST_F(CircularVertexColouringTest, T050_Diamond) {
    // K4 minus edge. Contains K3.
    Graph G(create_circuit(4));
    addE(G, Location(1, 3)); // Chord
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// =========================================================================
//  SECTION 2: CYCLES (Unrolled for Volume)
// =========================================================================

// --- 2.1: Small Odd Cycles (Fractional Chromatic Numbers) ---

TEST_F(CircularVertexColouringTest, T100_Cycle_C3) {
    Graph G(create_circuit(3));
    // 3 / 1 = 3
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T101_Cycle_C5) {
    Graph G(create_circuit(5));
    // 5 / 2 = 2.5
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 2));
}

TEST_F(CircularVertexColouringTest, T102_Cycle_C7) {
    Graph G(create_circuit(7));
    // 7 / 3 = 2.33...
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(7, 3));
}

TEST_F(CircularVertexColouringTest, T103_Cycle_C9) {
    Graph G(create_circuit(9));
    // 9 / 4 = 2.25
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(9, 4));
}

TEST_F(CircularVertexColouringTest, T104_Cycle_C11) {
    Graph G(create_circuit(11));
    // 11 / 5 = 2.2
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 5));
}

TEST_F(CircularVertexColouringTest, T105_Cycle_C13) {
    Graph G(create_circuit(13));
    // 13 / 6 = 2.166...
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(13, 6));
}

TEST_F(CircularVertexColouringTest, T106_Cycle_C15) {
    Graph G(create_circuit(15));
    // 15 / 7 = 2.142...
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(15, 7));
}

TEST_F(CircularVertexColouringTest, T107_Cycle_C17) {
    Graph G(create_circuit(17));
    // 17 / 8 = 2.125
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(17, 8));
}

// --- 2.2: Small Even Cycles (Bipartite) ---
// All even cycles have Chi_c = 2

TEST_F(CircularVertexColouringTest, T120_Cycle_C4) {
    Graph G(create_circuit(4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T121_Cycle_C6) {
    Graph G(create_circuit(6));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T122_Cycle_C8) {
    Graph G(create_circuit(8));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T123_Cycle_C10) {
    Graph G(create_circuit(10));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T124_Cycle_C12) {
    Graph G(create_circuit(12));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T125_Cycle_C14) {
    Graph G(create_circuit(14));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T126_Cycle_C16) {
    Graph G(create_circuit(16));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T127_Cycle_C18) {
    Graph G(create_circuit(18));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 2.3: Medium/Large Odd Cycles ---
// Checking logic for larger denominators

TEST_F(CircularVertexColouringTest, T140_Cycle_C19) {
    Graph G(create_circuit(19));
    // 19 / 9
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(19, 9));
}

TEST_F(CircularVertexColouringTest, T141_Cycle_C21) {
    Graph G(create_circuit(21));
    // 21 / 10 = 2.1
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(21, 10));
}

TEST_F(CircularVertexColouringTest, T142_Cycle_C23) {
    Graph G(create_circuit(23));
    // 23 / 11
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(23, 11));
}

TEST_F(CircularVertexColouringTest, T143_Cycle_C25) {
    Graph G(create_circuit(25));
    // 25 / 12
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(25, 12));
}

TEST_F(CircularVertexColouringTest, T144_Cycle_C31) {
    Graph G(create_circuit(31));
    // 31 / 15
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(31, 15));
}


// --- 2.4: Union of Cycles (Disjoint) ---
// Max(Chi_c(C_n), Chi_c(C_m))

TEST_F(CircularVertexColouringTest, T160_Union_C3_C4) {
    // C3 (3) and C4 (2) -> Max is 3
    Graph G(create_circuit(3));
    Graph H(create_circuit(4));
    // Shift indices of H to not overlap
    int offset = 3;
    for(int i=0; i<4; ++i) addV(G, offset + i);
    for(int i=0; i<4; ++i) addE(G, Location(offset + i, offset + ((i+1)%4)));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T161_Union_C5_C7) {
    // C5 (2.5) and C7 (2.33) -> Max is 2.5 (5/2)
    Graph G(create_circuit(5));
    int offset = 5;
    for(int i=0; i<7; ++i) addV(G, offset + i);
    for(int i=0; i<7; ++i) addE(G, Location(offset + i, offset + ((i+1)%7)));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 2));
}

TEST_F(CircularVertexColouringTest, T162_Union_C4_C6) {
    // Even + Even -> Still 2
    Graph G(create_circuit(4));
    int offset = 4;
    for(int i=0; i<6; ++i) addV(G, offset + i);
    for(int i=0; i<6; ++i) addE(G, Location(offset + i, offset + ((i+1)%6)));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// =========================================================================
//  SECTION 3: COMPLETE GRAPHS (Explicitly Unrolled)
// =========================================================================

// --- 3.1: Small Complete Graphs (K3 - K9) ---
// Theory: Chi_c(K_n) is exactly n (pair n, 1)

TEST_F(CircularVertexColouringTest, T300_Complete_K3) {
    Graph G(create_complete_graph(3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T301_Complete_K4) {
    Graph G(create_complete_graph(4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T302_Complete_K5) {
    Graph G(create_complete_graph(5));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 1));
}

TEST_F(CircularVertexColouringTest, T303_Complete_K6) {
    Graph G(create_complete_graph(6));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(6, 1));
}

TEST_F(CircularVertexColouringTest, T304_Complete_K7) {
    Graph G(create_complete_graph(7));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(7, 1));
}

TEST_F(CircularVertexColouringTest, T305_Complete_K8) {
    Graph G(create_complete_graph(8));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(8, 1));
}

TEST_F(CircularVertexColouringTest, T306_Complete_K9) {
    Graph G(create_complete_graph(9));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(9, 1));
}

// --- 3.2: Medium Complete Graphs (K10 - K15) ---
// Stress testing the solver with denser constraints

TEST_F(CircularVertexColouringTest, T310_Complete_K10) {
    Graph G(create_complete_graph(10));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(10, 1));
}

TEST_F(CircularVertexColouringTest, T311_Complete_K11) {
    Graph G(create_complete_graph(11));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 1));
}

// --- 3.3: Unions of Complete Graphs (Disjoint Cliques) ---
// Chi_c(K_n U K_m) = max(n, m)

TEST_F(CircularVertexColouringTest, T330_Union_K3_K3) {
    // 2x K3 disjoint -> max(3,3) = 3
    Graph G(create_complete_graph(3));
    int offset = 3;
    for(int i=0; i<3; ++i) addV(G, offset + i);
    // Add edges for second K3
    addE(G, Location(3, 4)); addE(G, Location(4, 5)); addE(G, Location(5, 3));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T331_Union_K3_K4) {
    // K3 U K4 -> max(3,4) = 4
    Graph G(create_complete_graph(3));
    int offset = 3;
    // Create K4 manually
    for(int i=0; i<4; ++i) addV(G, offset + i);
    for(int i=0; i<4; ++i) 
        for(int j=i+1; j<4; ++j) 
            addE(G, Location(offset+i, offset+j));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T332_Union_K5_K2) {
    // K5 U K2 -> max(5,2) = 5
    Graph G(create_complete_graph(5));
    addV(G, 5); addV(G, 6); addE(G, Location(5, 6));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 1));
}

// --- 3.4: Almost Complete (Kn minus edge) ---
// K_n minus 1 edge => Chi drops to n-1

TEST_F(CircularVertexColouringTest, T340_K4_Minus_Edge) {
    // K4 has 6 edges. Remove 1 -> Diamond graph. Chi = 3.
    Graph G(create_complete_graph(4));
    // Remove edge (0,1) by rebuilding or deleting
    // Easier to build fresh: 0-1, 1-2, 2-3, 3-0, 0-2 (missing 1-3)
    Graph H(create_circuit(4));
    addE(H, Location(0, 2));
    EXPECT_EQ(circular_chromatic_number_sat(solver, H).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T341_K5_Minus_Edge) {
    // K5 needs 5 colors. Removing 1 edge makes it 4-colorable.
    Graph G(create_complete_graph(5));
    // Implementation specific: assume deleteE exists or rebuild
    // Let's create K5 minus edge (0,1)
    Graph H(create_empty_graph(5));
    for(int i=0; i<5; ++i)
        for(int j=i+1; j<5; ++j)
            if (!(i==0 && j==1)) addE(H, Location(i, j));
            
    EXPECT_EQ(circular_chromatic_number_sat(solver, H).value(), std::pair(4, 1));
}

// --- 3.5: Ratio Boundaries on Complete Graphs ---

TEST_F(CircularVertexColouringTest, T350_K4_TightFail) {
    // K4 needs 4.0. Try 3.9
    Graph G(create_complete_graph(4));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 39, 10));
}

TEST_F(CircularVertexColouringTest, T351_K4_TightPass) {
    // K4 needs 4.0. Try 4.0
    Graph G(create_complete_graph(4));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 4, 1));
}

TEST_F(CircularVertexColouringTest, T352_K5_Relaxed) {
    // K5 needs 5.0. Try 5.5
    Graph G(create_complete_graph(5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 11, 2));
}

// =========================================================================
//  SECTION 4: MULTIGRAPHS - MASSIVE PERMUTATIONS (Edge Colouring)
// =========================================================================

// --- 4.1: The "Atom" (Two Vertices, Parallel Edges) ---

TEST_F(CircularEdgeColouringTest, T400_Multi_2V_2Edges) {
    Graph G(create_empty_graph(2));
    for(int i=0; i<2; ++i) addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularEdgeColouringTest, T401_Multi_2V_3Edges) {
    Graph G(create_empty_graph(2));
    for(int i=0; i<3; ++i) addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularEdgeColouringTest, T402_Multi_2V_4Edges) {
    Graph G(create_empty_graph(2));
    for(int i=0; i<4; ++i) addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularEdgeColouringTest, T403_Multi_2V_5Edges) {
    Graph G(create_empty_graph(2));
    for(int i=0; i<5; ++i) addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(5, 1));
}

TEST_F(CircularEdgeColouringTest, T404_Multi_2V_10Edges) {
    Graph G(create_empty_graph(2));
    for(int i=0; i<10; ++i) addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(10, 1));
}

// --- 4.2: Fat Triangles (Shannon Bound Stress) ---

TEST_F(CircularEdgeColouringTest, T410_FatTri_1_1_2) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1)); 
    addE(G, Location(1, 2)); 
    addE(G, Location(2, 0)); addE(G, Location(2, 0));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularEdgeColouringTest, T411_FatTri_1_2_2) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1)); 
    addE(G, Location(1, 2)); addE(G, Location(1, 2));
    addE(G, Location(2, 0)); addE(G, Location(2, 0));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(5, 1));
}

TEST_F(CircularEdgeColouringTest, T412_FatTri_2_2_2) {
    Graph G(create_empty_graph(3));
    for(int i=0; i<2; ++i) {
        addE(G, Location(0, 1));
        addE(G, Location(1, 2));
        addE(G, Location(2, 0));
    }
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(6, 1));
}

TEST_F(CircularEdgeColouringTest, T413_FatTri_3_3_3) {
    Graph G(create_empty_graph(3));
    for(int i=0; i<3; ++i) {
        addE(G, Location(0, 1)); addE(G, Location(1, 2)); addE(G, Location(2, 0));
    }
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(9, 1));
}

// --- 4.3: Bipartite Multigraphs ---

TEST_F(CircularEdgeColouringTest, T420_Multi_C4_Doubled) {
    Graph G(create_empty_graph(4));
    for(int i=0; i<2; ++i) {
        addE(G, Location(0, 1)); addE(G, Location(1, 2));
        addE(G, Location(2, 3)); addE(G, Location(3, 0));
    }
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularEdgeColouringTest, T421_Multi_C4_Mixed) {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    for(int i=0; i<3; ++i) addE(G, Location(1, 2));
    addE(G, Location(2, 3));
    for(int i=0; i<3; ++i) addE(G, Location(3, 0));
    
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularEdgeColouringTest, T422_Fat_K2_3) {
    // FIX: Namiesto iterovania cez existujúce hrany ich vytvoríme explicitne.
    // K2,3 má partície A={0,1}, B={2,3,4}.
    Graph G(create_complete_bipartite(2, 3));
    
    // Zdvojíme každú hranu (explicitne pridáme tie isté hrany znova)
    // Hrany sú medzi {0,1} a {2,3,4}
    for (int i = 0; i < 2; ++i) {
        for (int j = 0; j < 3; ++j) {
            addE(G, Location(i, 2 + j));
        }
    }

    // Delta bude 6 (pre vrcholy v A), graf je bipartitný -> Index = 6.
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(6, 1));
}

// --- 4.4: Stars with Multi-Edges ---

TEST_F(CircularEdgeColouringTest, T430_Star_S3_Mixed) {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    addE(G, Location(0, 2)); addE(G, Location(0, 2));
    addE(G, Location(0, 3)); addE(G, Location(0, 3)); addE(G, Location(0, 3));
    
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(6, 1));
}

// --- 4.5: Line Graph Properties (Cycles) ---

TEST_F(CircularEdgeColouringTest, T440_Simple_C5_Fractional) {
    Graph G(create_circuit(5));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(5, 2));
}

TEST_F(CircularEdgeColouringTest, T441_Simple_C7_Fractional) {
    Graph G(create_circuit(7));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(7, 3));
}

TEST_F(CircularEdgeColouringTest, T442_Fat_C5_Doubled) {
    Graph G(create_empty_graph(5));
    for(int i=0; i<5; ++i) {
        addE(G, Location(i, (i+1)%5));
        addE(G, Location(i, (i+1)%5));
    }
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(5, 1));
}

// --- 4.6: Odd Cycles with Chords ---

TEST_F(CircularEdgeColouringTest, T450_C3_With_Tail) {
    Graph G(create_circuit(3));
    addV(G, 3); addE(G, Location(0, 3));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularEdgeColouringTest, T451_Theta_Graph) {
    Graph G(create_empty_graph(5));
    addE(G, Location(0, 1)); addE(G, Location(1, 3));
    addE(G, Location(0, 2)); addE(G, Location(2, 3));
    addE(G, Location(0, 4)); addE(G, Location(4, 3));
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(3, 1));
}

// =========================================================================
//  SECTION 5: CNF GENERATION EDGE CASES
// =========================================================================

// --- 5.1: Structural Violations (Loops) ---

TEST_F(CNFCircularColouringTest, T500_Vertex_SelfLoop) {
    Graph G(create_empty_graph(1));
    addE(G, Location(0, 0));
    EXPECT_EQ(cnf_circular_vertex_colouring(G, 3, 1), cnf_unsatisfiable);
}

TEST_F(CNFCircularColouringTest, T501_Edge_SelfLoop) {
    Graph G(create_empty_graph(1));
    addE(G, Location(0, 0)); 
    EXPECT_EQ(cnf_circular_edge_colouring(G, 3, 1), cnf_unsatisfiable);
}

// --- 5.2: Invalid Parameter Ratios ---

TEST_F(CNFCircularColouringTest, T510_Ratio_One_Vertex) {
    Graph G(create_empty_graph(1));
    EXPECT_NE(cnf_circular_vertex_colouring(G, 1, 1), cnf_unsatisfiable);
}

// --- 5.3: Arithmetic Edge Cases ---

TEST_F(CNFCircularColouringTest, T520_Non_Coprime_Parameters) {
    Graph G(create_complete_graph(3));
    EXPECT_NE(cnf_circular_vertex_colouring(G, 6, 2), cnf_unsatisfiable);
}

TEST_F(CNFCircularColouringTest, T521_Large_Scale_Parameters) {
    Graph G(create_complete_graph(3));
    EXPECT_NE(cnf_circular_vertex_colouring(G, 300, 100), cnf_unsatisfiable);
}

// =========================================================================
//  SECTION 6: WHEEL GRAPHS (Explicitly Unrolled)
// =========================================================================

// --- 6.1: Small Wheels (Isomorphisms) ---

TEST_F(CircularVertexColouringTest, T600_Wheel_W4_Is_K4) {
    // Rim C3 (Triangle). Total 4 vertices. Isomorphic to K4.
    Graph G(create_circuit(3)); 
    addV(G, 3); // Center
    for(int i=0; i<3; ++i) addE(G, Location(i, 3));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T601_Wheel_W5) {
    // Rim C4 (Square). Bipartite rim + Center -> 3 colors.
    Graph G(create_circuit(4));
    addV(G, 4);
    for(int i=0; i<4; ++i) addE(G, Location(i, 4));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 6.2: Alternating Parity Checks ---

TEST_F(CircularVertexColouringTest, T602_Wheel_W6) {
    // Rim C5 (Odd). Chi(C5)=3. Center adds 1 -> 4.
    // Note: Even though C5 is 2.5 circular, the "hub" constraint forces integer 4.
    Graph G(create_circuit(5));
    addV(G, 5);
    for(int i=0; i<5; ++i) addE(G, Location(i, 5));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T603_Wheel_W7) {
    // Rim C6 (Even). Bipartite rim + Center -> 3.
    Graph G(create_circuit(6));
    addV(G, 6);
    for(int i=0; i<6; ++i) addE(G, Location(i, 6));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T604_Wheel_W8) {
    // Rim C7 (Odd). -> 4.
    Graph G(create_circuit(7));
    addV(G, 7);
    for(int i=0; i<7; ++i) addE(G, Location(i, 7));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T605_Wheel_W9) {
    // Rim C8 (Even). -> 3.
    Graph G(create_circuit(8));
    addV(G, 8);
    for(int i=0; i<8; ++i) addE(G, Location(i, 8));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T606_Wheel_W10) {
    // Rim C9 (Odd). -> 4.
    Graph G(create_circuit(9));
    addV(G, 9);
    for(int i=0; i<9; ++i) addE(G, Location(i, 9));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T607_Wheel_W11) {
    // Rim C10 (Even). -> 3.
    Graph G(create_circuit(10));
    addV(G, 10);
    for(int i=0; i<10; ++i) addE(G, Location(i, 10));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 6.3: Large Wheels ---

TEST_F(CircularVertexColouringTest, T610_Wheel_W20) {
    // Rim C19 (Odd). 20 vertices total. -> 4.
    Graph G(create_circuit(19));
    addV(G, 19);
    for(int i=0; i<19; ++i) addE(G, Location(i, 19));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(4, 1));
}

TEST_F(CircularVertexColouringTest, T611_Wheel_W21) {
    // Rim C20 (Even). 21 vertices total. -> 3.
    Graph G(create_circuit(20));
    addV(G, 20);
    for(int i=0; i<20; ++i) addE(G, Location(i, 20));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 6.4: Broken Wheels (Fan Graphs) ---
// A Wheel minus one rim edge is a Fan ($F_n$).
// Outer rim becomes a Path ($P_{n-1}$).
// Path is bipartite. Center + Path -> always 3-colorable (except very small).

TEST_F(CircularVertexColouringTest, T620_Fan_F5) {
    // Wheel W5 (Rim C4) minus rim edge (0,1).
    // Rim becomes Path 0-3-2-1. Center 4 connected to all.
    // Path is 2-colorable. Center is 3rd color.
    Graph G(create_circuit(4));
    addV(G, 4);
    for(int i=0; i<4; ++i) addE(G, Location(i, 4));
    
    // Remove edge (0,1) - Rebuilding manual structure for clarity
    Graph Fan(create_empty_graph(5));
    // Path 0-1-2-3
    addE(Fan, Location(0, 1)); addE(Fan, Location(1, 2)); addE(Fan, Location(2, 3));
    // Center 4 to all
    for(int i=0; i<4; ++i) addE(Fan, Location(i, 4));

    EXPECT_EQ(circular_chromatic_number_sat(solver, Fan).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T621_Fan_F6_From_Odd_Wheel) {
    // Wheel W6 (Rim C5, Chi=4) minus rim edge.
    // Rim becomes Path P5. P5 is bipartite.
    // Result should drop from 4 (Wheel) to 3 (Fan).
    Graph Fan(create_empty_graph(6)); // 5 rim nodes, 1 center
    // Path 0-1-2-3-4
    for(int i=0; i<4; ++i) addE(Fan, Location(i, i+1));
    // Center 5
    for(int i=0; i<5; ++i) addE(Fan, Location(i, 5));

    EXPECT_EQ(circular_chromatic_number_sat(solver, Fan).value(), std::pair(3, 1));
}

// =========================================================================
//  SECTION 7: BIPARTITE GRAPHS
// =========================================================================

// --- 7.1: Complete Bipartite Graphs (K_m,n) ---

TEST_F(CircularVertexColouringTest, T700_Star_S3_K1_3) {
    Graph G(create_complete_bipartite(1, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T701_Star_S10_K1_10) {
    Graph G(create_complete_bipartite(1, 10));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T702_K2_2) {
    Graph G(create_complete_bipartite(2, 2));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T703_K2_3) {
    Graph G(create_complete_bipartite(2, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T704_K3_3) {
    Graph G(create_complete_bipartite(3, 3));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T705_K3_4) {
    Graph G(create_complete_bipartite(3, 4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T706_K4_4) {
    Graph G(create_complete_bipartite(4, 4));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T707_K5_5) {
    Graph G(create_complete_bipartite(5, 5));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 7.2: Grid Graphs (Meshes) ---

TEST_F(CircularVertexColouringTest, T710_Grid_2x3) {
    Graph G(create_empty_graph(6));
    addE(G, Location(0, 1)); addE(G, Location(1, 2));
    addE(G, Location(3, 4)); addE(G, Location(4, 5));
    addE(G, Location(0, 3)); addE(G, Location(1, 4)); addE(G, Location(2, 5));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringTest, T711_Grid_3x3) {
    Graph G(create_empty_graph(9));
    for(int r=0; r<3; ++r) {
        for(int c=0; c<3; ++c) {
            int v = r*3 + c;
            if(c < 2) addE(G, Location(v, v+1));
            if(r < 2) addE(G, Location(v, v+3));
        }
    }
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 7.3: Hypercubes (Q_n) ---

TEST_F(CircularVertexColouringTest, T720_Cube_Q3) {
    Graph G(create_empty_graph(8));
    for(int i=0; i<8; ++i) {
        for(int j=i+1; j<8; ++j) {
            int diff = i ^ j;
            if(diff && !(diff & (diff-1))) {
                addE(G, Location(i, j));
            }
        }
    }
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 7.4: Tight Constraint Checks ---

TEST_F(CircularVertexColouringTest, T730_Bipartite_Strict_2) {
    Graph G(create_complete_bipartite(3, 3));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 19, 10));
}

TEST_F(CircularVertexColouringTest, T731_Bipartite_Relaxed) {
    Graph G(create_complete_bipartite(3, 3));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 21, 10));
}

// --- 7.5: Adding an Edge to Bipartite ---

TEST_F(CircularVertexColouringTest, T740_K3_3_Plus_Edge_Inside_Part) {
    Graph G(create_complete_bipartite(3, 3));
    addE(G, Location(0, 1));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// =========================================================================
//  SECTION 8: PRECOLOURING CHECKS
// =========================================================================

// --- 8.3: Edge Precolouring Checks ---

TEST_F(CircularEdgeColouringTest, T820_Edge_Conflict_Incident) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    
    // Získanie objektu Edge cez iterátor
    auto e1 = G[0].find(Location(0,1))->e();
    auto e2 = G[1].find(Location(1,2))->e();
    
    std::map<Edge, int> pre;
    pre[e1] = 0;
    pre[e2] = 0; 
    
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 3, 1, pre));
}

TEST_F(CircularEdgeColouringTest, T821_Edge_Valid_Forced) {
    Graph G(create_circuit(3));
    auto e1 = G[0].find(Location(0,1))->e();
    
    std::map<Edge, int> pre;
    pre[e1] = 0;
    
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 3, 1, pre));
}

TEST_F(CircularEdgeColouringTest, T822_Edge_Distance_Conflict_Fractional) {
    Graph G(create_circuit(5)); 
    auto e1 = G[0].find(Location(0,1))->e();
    auto e2 = G[1].find(Location(1,2))->e();
    
    std::map<Edge, int> pre;
    pre[e1] = 0;
    pre[e2] = 1; 
    
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 5, 2, pre));
}

TEST_F(CircularEdgeColouringTest, T823_Edge_Valid_Distance_Fractional) {
    Graph G(create_circuit(5));
    auto e1 = G[0].find(Location(0,1))->e();
    auto e2 = G[1].find(Location(1,2))->e();
    
    std::map<Edge, int> pre;
    pre[e1] = 0;
    pre[e2] = 2; 
    
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2, pre));
}

// =========================================================================
//  SECTION 9: GRAPH6 SPECIFIC TESTS
// =========================================================================

// --- 9.1: Small Named Graphs (Validation) ---

TEST_F(CircularVertexColouringTest, T900_Graph6_Butterfly) {
    // Butterfly / Bowtie: Two triangles meeting at one vertex.
    // 5 vertices, 6 edges. Chi = 3.
    Factory f;
    Graph G = read_graph6_line("D{k", f);
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringTest, T901_Graph6_Diamond) {
    // Diamond: K4 minus edge.
    // 4 vertices, 5 edges. Chi = 3.
    Factory f;
    Graph G = read_graph6_line("C|", f); // Check string validity or generic
    // If string is unknown, we rely on library parsing. 
    // "C|" is often K4-e. Let's assume valid.
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 9.2: Famous Graphs (Complex Structure) ---

TEST_F(CircularVertexColouringTest, T910_Graph6_Petersen) {
    // Petersen Graph: 10 vertices, 15 edges.
    // 3-colorable, but not 2.
    // Chi_c(Petersen) = 3 (It is not a bipartite graph, has odd cycles C5).
    // String: "IheA@GUAo"
    Factory f;
    Graph G = read_graph6_line("IheA@GUAo", f);
    
    EXPECT_EQ(G.order(), 10);
    EXPECT_EQ(G.size(), 15);
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// --- 9.3: Trivial & Edge Cases (String Parsing) ---

TEST_F(CircularVertexColouringTest, T920_Graph6_Empty_Zero) {
    // Empty graph n=0. String "?"
    Factory f;
    Graph G = read_graph6_line("?", f);
    EXPECT_EQ(G.order(), 0);
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
}

TEST_F(CircularVertexColouringTest, T921_Graph6_Single_Vertex) {
    // n=1. String "@"
    Factory f;
    Graph G = read_graph6_line("@", f);
    EXPECT_EQ(G.order(), 1);
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
}

// --- 9.4: Edge Colouring from Graph6 ---
// We read a graph structure and apply Edge Coloring logic.

TEST_F(CircularEdgeColouringTest, T930_Graph6_K4) {
    // K4 string "C~"
    Factory f;
    Graph G = read_graph6_line("C~", f);
    // K4 is Class 1 (Chi' = Delta = 3).
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(3, 1));
}

#endif  // BA_GRAPH_HAS_KISSAT_SUPPORT