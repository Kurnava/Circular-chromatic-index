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
class CircularVertexColouringTestSlow : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

class CircularEdgeColouringTestSlow : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

class CircularCriticalityTestSlow : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

// Empty test implementations to satisfy the build
TEST_F(CircularVertexColouringTestSlow, Skipped) {}
TEST_F(CircularEdgeColouringTestSlow, Skipped) {}
TEST_F(CircularCriticalityTestSlow, Skipped) {}

#else

class CircularVertexColouringTestSlow : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

class CircularEdgeColouringTestSlow : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

class CircularCriticalityTestSlow : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }

    KissatSolver solver;
};

// ======== Circular Vertex Colouring Tests ========

TEST_F(CircularVertexColouringTestSlow, CircularChromaticNumber) {
    Graph G(create_circuit(35));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(35, 17));
}

// ======== Circular Edge Colouring Tests ========

TEST_F(CircularEdgeColouringTestSlow, CircularChromaticIndex) {
    Graph G2 = create_circulant_1_2(7);
    EXPECT_EQ(circular_chromatic_index_sat(solver, G2).value(), std::pair(9, 2));

    Graph G3 = create_circulant_1_2(5);
    EXPECT_EQ(circular_chromatic_index_sat(solver, G3).value(), std::pair(14, 3));
}

// ======== Circular Criticality Tests ========

TEST_F(CircularCriticalityTestSlow, SmallCchiCriticalGraphs) {
    std::vector<std::string> critical_graphs = {"D~{",     "ETno",    "FUZv_",  "FFzvO",  "FUzro",
                                                "GCZvf_",  "GCZnfO",  "GCxvVG", "GEhttW", "H?`fNbc",
                                                "HCOffbo", "HCpvbqk", "HEhbtjK"};

    for (const auto& g6 : critical_graphs) {
        Graph G = read_graph_autodetect(g6);
        EXPECT_TRUE(is_cchi_critical(solver, G));
    }
}

TEST_F(CircularCriticalityTestSlow, SmallNonCchiCriticalGraphs) {
    std::vector<std::string> not_critical_graphs = {"L???CB?oJ_DooK", "L???CB?NBEWKoW",
                                                    "L???CB?oJ_@woK", "L???C@_cUAHo_U",
                                                    "L???C@_cUADo_U", "L???C@_cUABo_U",
                                                    "L???C@_cUA@s_U", "L???C@_cSQIo_U"};

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

// FIX: Anonymný namespace zabezpečí, že tieto funkcie sú viditeľné iba v tomto súbore.
// Tým predídeme chybe "multiple definition" pri linkovaní s test_circular_colouring.cpp.
namespace {

    Graph create_complete_bipartite(int n1, int n2) {
        Graph G(create_empty_graph(n1 + n2));
        for (int i = 0; i < n1; ++i) {
            for (int j = 0; j < n2; ++j) {
                addE(G, Location(i, n1 + j));
            }
        }
        return G;
    }

    // Helper: Create Grotzsch Graph (Mycielskian of C5)
    // 11 vertices. Triangle-free, Chi = 4.
    Graph create_grotzsch_graph() {
        Graph G(create_empty_graph(11));
        // 1. C5 on v0..v4
        for(int i=0; i<5; ++i) addE(G, Location(i, (i+1)%5));
        
        // 2. Add shadow vertices v5..v9 connected to neighbors of v0..v4
        // v_{5+i} connects to neighbors of v_i
        for(int i=0; i<5; ++i) {
            int left = (i + 4) % 5;
            int right = (i + 1) % 5;
            addE(G, Location(5+i, left));
            addE(G, Location(5+i, right));
        }
        
        // 3. Hub vertex v10 connects to all shadow vertices
        for(int i=5; i<10; ++i) addE(G, Location(10, i));
        
        return G;
    }

} // end anonymous namespace

class CircularVertexColouringSlowTest : public ::testing::Test { protected: KissatSolver solver; };
class CircularEdgeColouringSlowTest : public ::testing::Test { protected: KissatSolver solver; };

// =========================================================================
//  SECTION 1: LARGE COMPLETE GRAPHS (Optimized for <60s)
// =========================================================================

// --- 1.1: Exact Chromatic Number (K10 - K14) ---
// Tieto by mali zbehnúť do pár sekúnd.

TEST_F(CircularVertexColouringSlowTest, T100_Complete_K11) {
    Graph G(create_complete_graph(11));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 1));
}

TEST_F(CircularVertexColouringSlowTest, T101_Complete_K12) {
    Graph G(create_complete_graph(12));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(12, 1));
}

TEST_F(CircularVertexColouringSlowTest, T102_Complete_K13) {
    Graph G(create_complete_graph(13));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(13, 1));
}

TEST_F(CircularVertexColouringSlowTest, T103_Complete_K14) {
    Graph G(create_complete_graph(14));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(14, 1));
}

// --- 1.2: Disjoint Unions (Check correctness of max clique detection) ---
// Tieto grafy sú veľké počtom vrcholov, ale chromatické číslo je malé.
// Solver by to mal zvládnuť veľmi rýchlo.

TEST_F(CircularVertexColouringSlowTest, T104_Union_K5_K5_K5) {
    // 3x K5. Total 15 vertices. Chi = 5.
    Graph G(create_complete_graph(5));
    for(int k=1; k<3; ++k) {
        int offset = k * 5;
        for(int i=0; i<5; ++i) addV(G, offset + i);
        for(int i=0; i<5; ++i)
            for(int j=i+1; j<5; ++j)
                addE(G, Location(offset+i, offset+j));
    }
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(5, 1));
}

TEST_F(CircularVertexColouringSlowTest, T105_Union_K10_K5) {
    // K10 U K5. Chi = 10.
    Graph G(create_complete_graph(10));
    int offset = 10;
    for(int i=0; i<5; ++i) addV(G, offset + i);
    for(int i=0; i<5; ++i)
        for(int j=i+1; j<5; ++j)
            addE(G, Location(offset+i, offset+j));
            
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(10, 1));
}

TEST_F(CircularVertexColouringSlowTest, T106_Union_K8_K8) {
    // K8 U K8. Chi = 8.
    Graph G(create_complete_graph(8));
    int offset = 8;
    for(int i=0; i<8; ++i) addV(G, offset + i);
    for(int i=0; i<8; ++i)
        for(int j=i+1; j<8; ++j)
            addE(G, Location(offset+i, offset+j));

    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(8, 1));
}

// --- 1.3: Almost Complete Graphs (High Density) ---

TEST_F(CircularVertexColouringSlowTest, T120_K12_Minus_Edge) {
    // K12 minus 1 edge -> Chi = 11.
    Graph G(create_empty_graph(12));
    for(int i=0; i<12; ++i) {
        for(int j=i+1; j<12; ++j) {
            if(i==0 && j==1) continue;
            addE(G, Location(i, j));
        }
    }
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 1));
}

// --- 1.4: Split Graphs (Clique + Independent Set) ---
// G = K_n + I_m (Every node in I_m connected to every node in K_n)
// Chi = n + 1 (if m > 0)

TEST_F(CircularVertexColouringSlowTest, T130_Split_K10_I5) {
    // Clique K10 (0..9) + Independent Set I5 (10..14).
    // All I5 connected to all K10.
    // Chi = 10 + 1 = 11.
    Graph G(create_complete_graph(10));
    int offset = 10;
    for(int i=0; i<5; ++i) addV(G, offset + i); // Add I5 vertices
    
    // Connect I5 to K10
    for(int i=0; i<5; ++i) {     // For each Independent node
        for(int k=0; k<10; ++k) { // For each Clique node
            addE(G, Location(offset + i, k));
        }
    }
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 1));
}

// --- 1.5: Crown Graphs (Dense Bipartite) ---
// K_n,n minus a perfect matching.
// Very dense, but still Bipartite (Chi=2). Good sanity check for over-constraint.

TEST_F(CircularVertexColouringSlowTest, T140_Crown_Graph_10_10) {
    // K_10,10 minus matching (i, i+10).
    // Total 20 vertices.
    Graph G(create_empty_graph(20));
    for(int i=0; i<10; ++i) {
        for(int j=0; j<10; ++j) {
            // Skip "matching" edges (i, i+10) where j==i
            if (i == j) continue;
            addE(G, Location(i, 10 + j));
        }
    }
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// =========================================================================
//  SECTION 2: LARGE CYCLES (Extended)
//  Testing precision of rational handling and solver limits on path-like structures
// =========================================================================

// --- 2.1: Large Odd Cycles (Fractional Chi_c) ---

TEST_F(CircularVertexColouringSlowTest, T200_Cycle_C47) {
    // Prime number. 47 is odd.
    // Chi_c = 47 / 23 = 2.0434...
    Graph G(create_circuit(47));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(47, 23));
}

TEST_F(CircularVertexColouringSlowTest, T201_Cycle_C51) {
    // 51 = 3 * 17. Not prime, but odd.
    // Chi_c = 51 / 25 = 2.04
    Graph G(create_circuit(51));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(51, 25));
}

TEST_F(CircularVertexColouringSlowTest, T202_Cycle_C53) {
    // Prime.
    // Chi_c = 53 / 26 = 2.038...
    Graph G(create_circuit(53));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(53, 26));
}

TEST_F(CircularVertexColouringSlowTest, T203_Cycle_C99) {
    // 99 is odd.
    // Chi_c = 99 / 49 = 2.0204...
    Graph G(create_circuit(99));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(99, 49));
}

TEST_F(CircularVertexColouringSlowTest, T204_Cycle_C101) {
    // Prime 101.
    // Chi_c = 101 / 50 = 2.02
    Graph G(create_circuit(101));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(101, 50));
}

// --- 2.2: Large Even Cycles (Bipartite Checks) ---

TEST_F(CircularVertexColouringSlowTest, T210_Cycle_C50) {
    Graph G(create_circuit(50));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

TEST_F(CircularVertexColouringSlowTest, T211_Cycle_C100) {
    Graph G(create_circuit(100));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(2, 1));
}

// --- 2.3: Unions of Large Cycles ---
// Checks if solver handles multiple components correctly (max of ratios)

TEST_F(CircularVertexColouringSlowTest, T220_Union_C51_C101) {
    // C51 (2.04) U C101 (2.02).
    // Max is 2.04 (51/25).
    Graph G(create_circuit(51));
    int offset = 51;
    for(int i=0; i<101; ++i) addV(G, offset + i);
    for(int i=0; i<101; ++i) addE(G, Location(offset + i, offset + ((i+1)%101)));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(51, 25));
}

TEST_F(CircularVertexColouringSlowTest, T221_Union_C50_C51) {
    // C50 (2.0) U C51 (2.04).
    // Max is 2.04.
    Graph G(create_circuit(50));
    int offset = 50;
    for(int i=0; i<51; ++i) addV(G, offset + i);
    for(int i=0; i<51; ++i) addE(G, Location(offset + i, offset + ((i+1)%51)));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(51, 25));
}

// --- 2.4: Cycles with One Chord (Perturbed Cycles) ---

TEST_F(CircularVertexColouringSlowTest, T230_C50_With_Chord_Making_Triangle) {
    // C50 is bipartite. Adding chord (0,2) creates triangle 0-1-2.
    // Chi jumps from 2 to 3.
    Graph G(create_circuit(50));
    addE(G, Location(0, 2));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringSlowTest, T231_C51_With_Chord_Halving) {
    // C51 is 2.04. Adding chord (0, 25) roughly splits it into two C26s (bipartite).
    // But vertices are shared.
    // Actually, adding edges can only INCREASE Chi.
    // C51 contains odd cycle.
    // If we add a chord that creates a smaller odd cycle (e.g. 0 to 3 -> C3), Chi becomes 3.
    // If we add chord 0-10, we get C11 (chi=2.2) and C42. Max is 2.2.
    Graph G(create_circuit(51));
    addE(G, Location(0, 10)); // Creates 0-1-...-10-0 (Cycle 11)
    
    // We expect 11/5 (2.2) because C11 is the "hottest" subgraph.
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 5));
}

// --- 2.5: Additional Odd Cycles (Composite & Extreme) ---

TEST_F(CircularVertexColouringSlowTest, T205_Cycle_C35) {
    // 35 is composite (5*7).
    // Chi_c = 35 / 17 = 2.0588...
    Graph G(create_circuit(35));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(35, 17));
}

// Very large cycles - check satisfiability only to keep runtime < 60s
TEST_F(CircularVertexColouringSlowTest, T212_Cycle_C201_Sat) {
    // 201 is odd. Target 201/100 = 2.01.
    Graph G(create_circuit(201));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 201, 100));
}

TEST_F(CircularVertexColouringSlowTest, T213_Cycle_C301_Sat) {
    // 301 is odd. Target 301/150.
    Graph G(create_circuit(301));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 301, 150));
}

// --- 2.6: Cycles with Chords (Perturbed) ---

TEST_F(CircularVertexColouringSlowTest, T240_C50_With_Chord_Triangle) {
    // C50 is bipartite (Chi=2). Adding chord (0,2) creates triangle 0-1-2.
    // Chi jumps to 3.
    Graph G(create_circuit(50));
    addE(G, Location(0, 2));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

TEST_F(CircularVertexColouringSlowTest, T241_C51_With_Chord_C11) {
    // C51 (Chi=2.04). Adding chord (0,10) creates a smaller odd cycle C11 (0..10..0).
    // Chi(C11) = 11/5 = 2.2.
    // Result should be determined by the "hottest" loop C11.
    Graph G(create_circuit(51));
    addE(G, Location(0, 10));
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(11, 5));
}

// --- 2.7: Squared Cycles (Distance-2 Graphs) ---
// Edges (i, i+1) and (i, i+2).
// If n is multiple of 3, Chi=3. Otherwise Chi=4.

TEST_F(CircularVertexColouringSlowTest, T250_Square_C30_Divisible3) {
    // C30^2. 30 is multiple of 3.
    // Can be colored with 3 colors: 0,1,2,0,1,2...
    Graph G(create_circuit(30));
    for(int i=0; i<30; ++i) addE(G, Location(i, (i+2)%30));
    
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::pair(3, 1));
}

// =========================================================================
//  SECTION 3: SNARKS & CLASS 2 GRAPHS (Edge Colouring Hardness)
// =========================================================================

TEST_F(CircularEdgeColouringSlowTest, T300_Complete_K7_Edge) {
    // K7: Delta=6.
    // Edges = 7*6/2 = 21. Max Matching = 3.
    // Colors needed = 21/3 = 7.
    // Chi' = 7.
    Graph G(create_complete_graph(7));
    
    // Check Delta=6 fails
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 6, 1));
    // Check 7 works
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 7, 1));
}

TEST_F(CircularEdgeColouringSlowTest, T310_Large_Cycle_C51_Edge) {
    // C51 edge coloring. Delta=2.
    // Needs 3 colors (Class 2 relative to Delta=2).
    // Specifically, circular index is 51/25 = 2.04.
    Graph G(create_circuit(51));
    
    EXPECT_EQ(circular_chromatic_index_sat(solver, G).value(), std::pair(51, 25));
}

// =========================================================================
//  SECTION 4: TIGHT CONSTRAINTS & PRECISION
//  Stress-testing the solver with large denominators and tight ratios.
// =========================================================================

// --- 4.1: High Precision Failures (Just below Chi_c) ---

TEST_F(CircularVertexColouringSlowTest, T400_K6_Tight_Fail) {
    // K6 requires exactly 6.0.
    // Test Ratio 5.99 (599/100).
    // The solver must prove UNSAT.
    Graph G(create_complete_graph(6));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 599, 100));
}

TEST_F(CircularVertexColouringSlowTest, T401_K7_Tight_Fail) {
    // K7 requires 7.0.
    // Test Ratio 6.99 (699/100).
    Graph G(create_complete_graph(7));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 699, 100));
}

TEST_F(CircularVertexColouringSlowTest, T402_Grotzsch_Tight_Fail) {
    // Grotzsch graph is 4-chromatic.
    // Test Ratio 3.9 (39/10).
    // Using the helper defined in the anonymous namespace above.
    Graph G = create_grotzsch_graph();
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 39, 10));
}

// --- 4.2: High Precision Success (Exact or Just above) ---

TEST_F(CircularVertexColouringSlowTest, T410_K6_Exact_High_P) {
    // K6 requires 6.0.
    // Test Ratio 6.0 expressed as (600, 100).
    // Ensures solver handles large inputs correctly even if reducible.
    Graph G(create_complete_graph(6));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 600, 100));
}

TEST_F(CircularVertexColouringSlowTest, T411_Cycle_C101_Precision) {
    // C101 is a large odd cycle.
    // Exact Chi_c = 101 / 50 = 2.02.
    Graph G(create_circuit(101));

    // 1. Test Just Below: 2.01 (201/100) -> Should Fail
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 201, 100));

    // 2. Test Exact: 2.02 (101/50) -> Should Pass
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 101, 50));
    
    // 3. Test Just Above: 2.03 (203/100) -> Should Pass
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 203, 100));
}

// --- 4.3: Large Denominator Edge Cases ---

TEST_F(CircularVertexColouringSlowTest, T420_Odd_Cycle_C15_Rational) {
    // C15. Chi_c = 15/7 = 2.142857...
    Graph G(create_circuit(15));
    
    // Try a close rational approximation 2.14 (107/50) -> 2.14 < 2.1428...
    // Should FAIL.
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 107, 50));

    // Try slightly higher 2.15 (43/20) -> 2.15 > 2.1428...
    // Should PASS.
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 43, 20));
}

#endif  // BA_GRAPH_HAS_KISSAT_SUPPORT