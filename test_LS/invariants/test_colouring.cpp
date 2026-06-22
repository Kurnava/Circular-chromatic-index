#include <cassert>
#include <iomanip>
#include <random>
#include <sstream>
#include <string>
#include <vector>

// clang-format off
#include "implementation.h"

#include <graphs/basic.hpp>
#include <graphs/bipartite.hpp>
#include <graphs/cubic.hpp>
#include <gtest/gtest.h>
#include <invariants/colouring.hpp>
#include <invariants/degree.hpp>
#include <io/unified_io.hpp>
#include <sat/exec_colouring.hpp>
#include <sat/solution_types.hpp>
#include <operations/add_graph.hpp> // For add_disjoint
// clang-format on

#include <invariants/invariant_types.hpp>
#include <invariants/invariant_utils_core.hpp>
#include <sat/solver_kissat.hpp>

#include "../test_resources.hpp"

using namespace ba_graph;

// Helper functions for counting colorings
bool countColourings(std::map<Vertex, int>, int *c) {
    ++*c;
    return true;
}

bool countEdgeColourings(std::map<Edge, int>, int *c) {
    ++*c;
    return true;
}

bool countColouringsStop(std::map<Vertex, int>, int *c) {
    ++*c;
    return false;
}

class ColourTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class ChromaticNumberTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class ChromaticIndexTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class CVDHeuristicTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class EdgeColoringValidationTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class VertexColoringValidationTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class ChromaticNumberBoundsTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

class ChromaticIndexBoundsTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

// Test vertex coloring validation
TEST_F(VertexColoringValidationTest, BasicVertexValidation) {
    Factory f;

    // Test empty graph with 0 colours (should succeed)
    Graph empty_graph = create_empty_graph(0, f);
    EXPECT_TRUE(is_k_vertex_colourable(empty_graph, 0));

    // Test non-empty graph with 0 colours (should fail)
    Graph single_vertex = create_empty_graph(1, f);
    EXPECT_FALSE(is_k_vertex_colourable(single_vertex, 0));

    // Test negative colours (should throw)
    EXPECT_THROW({ is_k_vertex_colourable(empty_graph, -1); }, std::invalid_argument);
}

// Test edge coloring validation
TEST_F(EdgeColoringValidationTest, BasicEdgeValidation) {
    Factory f;

    // Test empty graph with 0 colours (should succeed)
    Graph empty_graph = create_empty_graph(0, f);
    EXPECT_TRUE(is_k_edge_colourable(empty_graph, 0));

    // Test non-empty graph with 0 colours - single vertex case
    Graph single_vertex = create_empty_graph(1, f);
    EXPECT_TRUE(is_k_edge_colourable(single_vertex, 0));  // No edges, so 0 colours OK

    // Test negative colours (should throw)
    EXPECT_THROW({ is_k_edge_colourable(empty_graph, -1); }, std::invalid_argument);
}

// Test removal functionality
TEST_F(EdgeColoringValidationTest, RemovalTest) {
    Graph G(read_graph_autodetect(":]dBgEfGdeIf`KiehoaGfJQknP_MoUcSnWdVmPYlXsT["));
    std::map<Edge, int> precolouring;
    for (auto &e : G.list(RP::all(), IP::primary(), IT::e())) {
        precolouring[e] = NO_COLOUR;
    }

    for (auto &v : G) {
        if (v.degree() == 1) {
            precolouring[v.find(IP::all())->e()] = 0;
        }
    }
    EXPECT_FALSE(is_edge_colourable_basic(G, 3, precolouring));

    bool isColourableAfterRemoval = false;
    for (auto &v : G) {
        if (v.degree() == 1) {
            continue;
        }
        Factory f;
        auto [H, m] = copy_other_factory<EdgeMapper>(G, f);
        std::map<Edge, int> prec2;
        for (auto &e : G.list(RP::all(), IP::primary(), IT::e())) {
            prec2[m.get(e)] = precolouring[e];
        }
        deleteV(H, v.n(), f);
        if (is_edge_colourable_basic(H, 3, prec2)) {
            isColourableAfterRemoval = true;
        }
    }
    EXPECT_TRUE(isColourableAfterRemoval);
}

// Test vertex coloring enumeration
TEST_F(ColourTest, EnumerateVertexColourings) {
    Graph g0(create_empty_graph(0));
    int c0 = 0;
    enumerate_colourings_basic(g0, 3, countColourings, &c0);
    EXPECT_EQ(c0, 1);

    Graph g2_enum(create_empty_graph(4));
    int c2 = 0;
    enumerate_colourings_basic(g2_enum, 3, countColourings, &c2);
    EXPECT_EQ(c2, 81);

    Graph a11(create_circuit(5));
    std::map<Vertex, int> precolouring11;
    int ca11 = 0;
    EXPECT_TRUE(enumerate_colourings_basic(a11, 3, countColourings, &ca11, precolouring11));
    EXPECT_EQ(ca11, 30);

    precolouring11[a11[1].v()] = 1;
    ca11 = 0;
    EXPECT_TRUE(enumerate_colourings_basic(a11, 3, countColourings, &ca11, precolouring11));
    EXPECT_EQ(ca11, 10);

    precolouring11[a11[2].v()] = 2;
    ca11 = 0;
    EXPECT_TRUE(enumerate_colourings_basic(a11, 3, countColourings, &ca11, precolouring11));
    EXPECT_EQ(ca11, 5);
}

// Test chromatic number calculations
TEST_F(ChromaticNumberTest, BasicChromaticNumber) {
    Graph g1(create_empty_graph(11));
    EXPECT_TRUE(is_colourable_basic(g1, 5));
    EXPECT_FALSE(is_colourable_basic(g1, 0));
    EXPECT_EQ(chromatic_number_basic(g1), 1);

    Graph g2_cn(create_empty_graph(4));
    addE(g2_cn, Location(0, 1));
    addE(g2_cn, Location(0, 2));
    addE(g2_cn, Location(0, 3));
    addE(g2_cn, Location(1, 2));
    EXPECT_EQ(chromatic_number_basic(g2_cn), 3);

    Factory f_g2lg;
    Graph g2lg(line_graph(g2_cn, f_g2lg));
    EXPECT_EQ(chromatic_number_basic(simplify(g2lg, f_g2lg)), max_deg(g2_cn));

    Graph g3(create_petersen());
    EXPECT_EQ(chromatic_number_basic(g3), 3);
    Factory f_g3lg;
    Graph g3lg(line_graph(g3, f_g3lg));
    EXPECT_EQ(chromatic_number_basic(simplify(g3lg, f_g3lg)), 4);

    Graph g4_cn(create_complete_bipartite_graph(4, 7));
    EXPECT_EQ(chromatic_number_basic(g4_cn), 2);

    Graph g5_cn(create_complete_graph(7));
    EXPECT_EQ(chromatic_number_basic(g5_cn), 7);

    Graph g6_cn(create_petersen());
    Graph g3_for_g6(create_petersen());
    Graph g4_for_g6(create_complete_bipartite_graph(4, 7));
    add_disjoint(g6_cn, g3_for_g6, 10);
    EXPECT_EQ(chromatic_number_basic(g6_cn), 3);
    add_disjoint(g6_cn, g4_for_g6, 20);
    EXPECT_EQ(chromatic_number_basic(g6_cn), 3);
}

// Test chromatic index calculations
TEST_F(ChromaticIndexTest, BasicChromaticIndex) {
    Graph g4_ci(create_complete_bipartite_graph(4, 7));
    EXPECT_EQ(chromatic_index_basic(g4_ci), 7);

    Graph g5_ci(create_complete_graph(7));
    EXPECT_EQ(chromatic_index_basic(g5_ci), 7);

    Graph g6_ci(create_petersen());
    Graph g3_for_g6_ci(create_petersen());
    Graph g4_for_g6_ci(create_complete_bipartite_graph(4, 7));
    add_disjoint(g6_ci, g3_for_g6_ci, 10);
    EXPECT_EQ(chromatic_index_basic(g6_ci), 4);
    add_disjoint(g6_ci, g4_for_g6_ci, 20);
    EXPECT_EQ(chromatic_index_basic(g6_ci), 7);

    Graph a1_ci(create_complete_graph(4));
    EXPECT_TRUE(is_edge_colourable_basic(a1_ci, 3));

    Graph a2(create_petersen());
    EXPECT_FALSE(is_edge_colourable_basic(a2, 3));
    EXPECT_EQ(chromatic_index_basic(a2), 4);

    Graph a3 = create_empty_graph(2);
    addE(a3, Location(0, 1));
    addE(a3, Location(0, 1));
    addE(a3, Location(0, 1));
    addE(a3, Location(0, 1));
    addE(a3, Location(0, 1));
    EXPECT_EQ(chromatic_index_basic(a3), 5);
    EXPECT_TRUE(is_edge_colourable_basic(a3, 5));
    EXPECT_FALSE(is_edge_colourable_basic(a3, 4));

    addE(a3, Location(0, 0));
    EXPECT_EQ(chromatic_index_basic(a3), UNCOLOURABLE);
    EXPECT_FALSE(is_edge_colourable_basic(a3, 5));
    EXPECT_FALSE(is_edge_colourable_basic(a3, 20));
}

// Test edge coloring enumeration
TEST_F(ColourTest, EnumerateEdgeColourings) {
    Graph a1_ee(create_complete_graph(4));
    std::map<Edge, int> precolouring;
    Edge e01 = a1_ee[0].find(Location(0, 1))->e();
    Edge e02 = a1_ee[0].find(Location(0, 2))->e();
    precolouring[e01] = 2;
    precolouring[e02] = 2;
    EXPECT_FALSE(is_edge_colourable_basic(a1_ee, 3, precolouring));

    precolouring[e02] = 0;
    EXPECT_TRUE(is_edge_colourable_basic(a1_ee, 3, precolouring));
    int ca1 = 0;
    EXPECT_TRUE(enumerate_edge_colourings_basic(a1_ee, 3, countEdgeColourings, &ca1, precolouring));
    EXPECT_EQ(ca1, 1);

    Graph a12(create_circuit(5));
    std::map<Edge, int> precolouring12;
    int ca12 = 0;
    EXPECT_TRUE(enumerate_edge_colourings_basic(a12, 3, countEdgeColourings, &ca12, precolouring12)
    );
    EXPECT_EQ(ca12, 30);

    precolouring12[a12[2].find(Location(2, 1))->e()] = 1;
    ca12 = 0;
    EXPECT_TRUE(enumerate_edge_colourings_basic(a12, 3, countEdgeColourings, &ca12, precolouring12)
    );
    EXPECT_EQ(ca12, 10);

    precolouring12[a12[2].find(Location(2, 3))->e()] = 2;
    ca12 = 0;
    EXPECT_TRUE(enumerate_edge_colourings_basic(a12, 3, countEdgeColourings, &ca12, precolouring12)
    );
    EXPECT_EQ(ca12, 5);
}

// Test CVD heuristic on snarks
TEST_F(CVDHeuristicTest, CVDHeuristicOnSnarks) {
    Factory factory;

    std::vector<std::string> snark_orders = {"10", "18"};
    std::string base_path_template =
        test::resources_graphs_dir() + "/snarks/d03-g04-cc04-chi04/d03-g04-cc04-chi04.";

    for (const std::string &order : snark_orders) {
        std::string filename = base_path_template + order + ".s6";
        std::vector<Graph> graphs_in_file = read_all_graphs_autodetect(filename, factory);

        for (size_t i = 0; i < graphs_in_file.size(); ++i) {
            Graph &g = graphs_in_file[i];

            bool is_colourable_by_cvd = has_cvd_edge_colouring_general(g, -1, -1, 42);
            EXPECT_FALSE(is_colourable_by_cvd);

            is_colourable_by_cvd = has_cvd_edge_colouring_3regular(g, -1, -1);
            EXPECT_FALSE(is_colourable_by_cvd);
        }
    }
}

TEST_F(CVDHeuristicTest, LegacyPrecolorTouchesEachEdgeOnce) {
    std::mt19937 rng(1);
    legacy::cvd::graph g = legacy::cvd::graph_init(4);
    legacy::cvd::add_edge(&g, 0, 1);
    legacy::cvd::add_edge(&g, 0, 2);
    legacy::cvd::add_edge(&g, 0, 3);
    legacy::cvd::add_edge(&g, 1, 2);
    legacy::cvd::add_edge(&g, 1, 3);
    legacy::cvd::add_edge(&g, 2, 3);

    legacy::cvd::precolor(&g, rng);

    for (int u = 0; u < g.size; ++u) {
        EXPECT_EQ(legacy::cvd::used_colors(&g, u), legacy::cvd::LEGACY_CVD_ALL_COLORS);
        EXPECT_EQ(legacy::cvd::conflicting_colors(&g, u), 0U);
        for (int vi = 0; vi < g.deg[u]; ++vi) {
            int v = g.nei[u][vi];
            EXPECT_EQ(legacy::cvd::edge_color(&g, u, v), legacy::cvd::edge_color(&g, v, u));
        }
    }

    legacy::cvd::graph_free(&g);
}

// Test CVD on cubic graphs
TEST_F(CVDHeuristicTest, CVDOnCubicCC01G03) {
    const std::string correctAnswer = R"(
1
11
11111
0111111111111111110
)";

    std::stringstream output_ss;
    output_ss << std::endl;  // Match the initial newline in correctAnswer
    Factory factory;

    for (int i = 4; i <= 10; i += 2) {
        std::stringstream ss;
        ss << test::resources_graphs_dir() << "/d03-g03-cc01/d03-g03-cc01." << std::setw(2)
           << std::setfill('0') << i << ".s6";
        std::string filename = ss.str();
        std::vector<Graph> graphs = read_all_graphs_autodetect(filename, factory);
        for (Graph &G : graphs) {
            bool colourable = is_edge_colourable_basic(G, 3);
            bool colourable_cvd = has_cvd_edge_colouring_general(G, -1, -1, 42);
            bool colourable_cvd_3reg = has_cvd_edge_colouring_3regular(G);
            int chi = chromatic_index_basic(G);

            EXPECT_EQ(colourable, colourable_cvd);
            EXPECT_EQ(colourable, colourable_cvd_3reg);
            EXPECT_EQ(colourable, (chi == 3));

            output_ss << colourable;
        }
        output_ss << std::endl;
    }
    EXPECT_EQ(output_ss.str(), correctAnswer);
}

// Test CVD 4-regular individual cases
TEST_F(CVDHeuristicTest, CVD4RegularIndividualCases) {
    Factory factory;

    // Test K5 (4-regular, chi'=5, Class 2)
    Graph k5 = create_complete_graph(5);
    int k5_chi_prime = chromatic_index_basic(k5);
    EXPECT_EQ(k5_chi_prime, 5);  // K5 is Class 2
    EXPECT_FALSE(has_cvd_edge_colouring_general(k5, -1, -1, 42));
    EXPECT_FALSE(has_cvd_edge_colouring_4regular(k5, -1, -1, 42));

    // Test Octahedron graph (L(K4), 4-regular, chi'=4, Class 1)
    Factory f_octahedron;
    Graph octahedron = line_graph(create_complete_graph(4), f_octahedron);
    int octa_chi_prime = chromatic_index_basic(octahedron);
    EXPECT_EQ(octa_chi_prime, 4);  // Octahedron is Class 1
    EXPECT_TRUE(has_cvd_edge_colouring_general(octahedron, -1, -1, 42));
    EXPECT_TRUE(has_cvd_edge_colouring_4regular(octahedron, -1, -1, 42));
}

TEST_F(CVDHeuristicTest, HeuristicsColouriserHandlesNonCubicGraph) {
    Graph k5 = create_complete_graph(5);
    HeuristicsColouriser colouriser;

    // K5 is non-cubic and not 3-edge-colourable; this must be handled safely.
    EXPECT_FALSE(colouriser.isColourable(k5));
}

// FIXME TODO takes too long
// Test CVD 4-regular class 2 files
/*TEST_F(CVDHeuristicTest, CVD4RegularClass2Files) {
    Factory factory;
    std::string base_4reg_path = "../../resources/graphs/d04-g03-class2/";

    std::vector<std::string> class2_graph_files = {
        "d04-g03-class2.05.g6",
        "d04-g03-class2.06.g6",
        "d04-g03-class2.07.g6",
        "d04-g03-class2.08.g6",
        "d04-g03-class2.09.g6",
        "d04-g03-class2.10.g6",
        "d04-g03-class2.11.g6",
        "d04-g03-class2.12.g6",
    };
    for (const std::string& rel_filename : class2_graph_files) {
        std::string full_filename = base_4reg_path + rel_filename;
        std::vector<Graph> graphs_in_file = read_all_graphs_autodetect(full_filename, factory);
        for (Graph& g : graphs_in_file) {
            EXPECT_FALSE(has_cvd_edge_colouring_general(g, -1, -1, 42));
            EXPECT_FALSE(has_cvd_edge_colouring_4regular(g, -1, -1, 42));
        }
    }
}*/

// FIXME TODO takes too long
// Test CVD 4-regular general files
/*TEST_F(CVDHeuristicTest, CVD4RegularGeneralFiles) {
    Factory factory;
    std::string base_4reg_path = "../../resources/graphs/d04-g03/";

    std::vector<std::string> all_graph_files = {
        "d04-g03.05.g6",
        "d04-g03.06.g6",
        "d04-g03.07.g6",
        "d04-g03.08.g6",
        "d04-g03.09.g6",
        "d04-g03.10.g6",
        "d04-g03.11.g6",
        "d04-g03.12.g6",
        "d04-g03.16.g6",
        "d04-g03.20.g6",
    };
    for (const std::string& rel_filename : all_graph_files) {
        std::string full_filename = base_4reg_path + rel_filename;
        std::vector<Graph> graphs_in_file = read_all_graphs_autodetect(full_filename, factory);
        for (Graph& g : graphs_in_file) {
            bool cvd_4reg_is_4_colourable = has_cvd_edge_colouring_4regular(g, -1, -1, 42);
            bool cvd_general_is_4_colourable = has_cvd_edge_colouring_general(g, -1, -1, 42);

            int actual_chi_prime = chromatic_index_basic(g);
            EXPECT_TRUE((actual_chi_prime == 4 || actual_chi_prime == 5)) << "4-regular graph has
unexpected chromatic index (not 4 or 5).";

            EXPECT_EQ(cvd_4reg_is_4_colourable, (actual_chi_prime == 4));
            EXPECT_EQ(cvd_general_is_4_colourable, (actual_chi_prime == 4));
        }
    }
}*/

// Test vertex coloring with loops
TEST_F(ColourTest, VertexColoringWithLoops) {
    // Test graph with only loops
    Graph g_with_loops(create_empty_graph(3));
    addE(g_with_loops, Location(0, 0));  // Add a loop
    addE(g_with_loops, Location(1, 1));  // Add another loop

    // Vertex coloring should fail for graphs with loops
    EXPECT_FALSE(is_colourable_basic(g_with_loops, 3));
    EXPECT_FALSE(is_colourable_basic(g_with_loops, 10));
    EXPECT_EQ(chromatic_number_basic(g_with_loops), UNCOLOURABLE);

    // Test with precolouring
    std::map<Vertex, int> precolouring;
    precolouring[g_with_loops[2].v()] = 0;  // Precolour vertex without loop
    EXPECT_FALSE(is_colourable_basic(g_with_loops, 3, precolouring));

    // Test mixed graph with loops and regular edges
    Graph g_mixed(create_empty_graph(3));
    addE(g_mixed, Location(0, 1));  // Regular edge
    addE(g_mixed, Location(1, 2));  // Regular edge
    addE(g_mixed, Location(0, 0));  // Loop

    EXPECT_FALSE(is_colourable_basic(g_mixed, 3));
    EXPECT_EQ(chromatic_number_basic(g_mixed), UNCOLOURABLE);
}

// Test chromatic number bounds functions
TEST_F(ChromaticNumberBoundsTest, ChromaticNumberBounds) {
    Factory f;

    // Test 1: Empty graph (chromatic number 0)
    Graph empty = create_empty_graph(0, f);
    EXPECT_TRUE(chromatic_number_at_most(empty, 0));
    EXPECT_THROW({ chromatic_number_at_most(empty, -1); }, std::invalid_argument);
    EXPECT_TRUE(chromatic_number_at_least(empty, 0));
    EXPECT_TRUE(chromatic_number_at_least(empty, -1));
    EXPECT_FALSE(chromatic_number_at_least(empty, 1));

    // Test 2: Single vertex (chromatic number 1)
    Graph single = create_empty_graph(1, f);
    EXPECT_TRUE(chromatic_number_at_most(single, 1));
    EXPECT_FALSE(chromatic_number_at_most(single, 0));
    EXPECT_TRUE(chromatic_number_at_least(single, 1));
    EXPECT_FALSE(chromatic_number_at_least(single, 2));

    // Test 3: Complete graph K_3 (chromatic number 3)
    Graph K3 = create_complete_graph(3, f);
    EXPECT_TRUE(chromatic_number_at_most(K3, 3));
    EXPECT_FALSE(chromatic_number_at_most(K3, 2));
    EXPECT_TRUE(chromatic_number_at_least(K3, 3));
    EXPECT_FALSE(chromatic_number_at_least(K3, 4));

    // Test 4: Cycle C_4 (even cycle - chromatic number 2)
    Graph C4 = create_cycle(4, f);
    EXPECT_TRUE(chromatic_number_at_most(C4, 2));
    EXPECT_FALSE(chromatic_number_at_most(C4, 1));
    EXPECT_TRUE(chromatic_number_at_least(C4, 2));
    EXPECT_FALSE(chromatic_number_at_least(C4, 3));

    // Test 5: Cycle C_5 (odd cycle - chromatic number 3)
    Graph C5 = create_cycle(5, f);
    EXPECT_TRUE(chromatic_number_at_most(C5, 3));
    EXPECT_FALSE(chromatic_number_at_most(C5, 2));
    EXPECT_TRUE(chromatic_number_at_least(C5, 3));
    EXPECT_FALSE(chromatic_number_at_least(C5, 4));

    // Test 6: Graph with loops (should be uncolourable)
    Graph loop_graph = create_empty_graph(2, f);
    addE(loop_graph, Location(0, 0), f);  // Self-loop
    addE(loop_graph, Location(0, 1), f);  // Regular edge
    EXPECT_FALSE(chromatic_number_at_most(loop_graph, 1000));
    EXPECT_THROW(chromatic_number_at_least(loop_graph, 0), std::invalid_argument);
    EXPECT_THROW(chromatic_number_at_least(loop_graph, 1000), std::invalid_argument);

    // Test vertex coloring wrapper function
    EXPECT_TRUE(is_k_vertex_colourable(K3, 3));
    EXPECT_FALSE(is_k_vertex_colourable(K3, 2));

    // Consistency tests: verify against exact computations for small complete graphs
    for (int n = 1; n <= 4; ++n) {
        Graph Kn = create_complete_graph(n, f);
        int exact_chn = chromatic_number_basic(Kn);

        // Test that optimized functions are consistent
        EXPECT_TRUE(chromatic_number_at_most(Kn, exact_chn));
        if (exact_chn > 0) {
            EXPECT_FALSE(chromatic_number_at_most(Kn, exact_chn - 1));
        }
        EXPECT_TRUE(chromatic_number_at_least(Kn, exact_chn));
        EXPECT_FALSE(chromatic_number_at_least(Kn, exact_chn + 1));
    }
}

// Test chromatic index bounds functions
TEST_F(ChromaticIndexBoundsTest, ChromaticIndexBounds) {
    Factory f;

    // Test 1: Empty graph (chromatic index 0)
    Graph empty = create_empty_graph(0, f);
    EXPECT_TRUE(chromatic_index_at_most(empty, 0));
    EXPECT_THROW({ chromatic_index_at_most(empty, -1); }, std::invalid_argument);
    EXPECT_TRUE(chromatic_index_at_least(empty, 0));
    EXPECT_FALSE(chromatic_index_at_least(empty, 1));

    // Test 2: Single vertex (chromatic index 0)
    Graph single = create_empty_graph(1, f);
    EXPECT_TRUE(chromatic_index_at_most(single, 0));
    EXPECT_TRUE(chromatic_index_at_least(single, 0));
    EXPECT_FALSE(chromatic_index_at_least(single, 1));

    // Test 3: Complete graph K_3 (chromatic index 3)
    Graph K3 = create_complete_graph(3, f);
    EXPECT_TRUE(chromatic_index_at_most(K3, 3));
    EXPECT_FALSE(chromatic_index_at_most(K3, 2));
    EXPECT_TRUE(chromatic_index_at_least(K3, 3));
    EXPECT_FALSE(chromatic_index_at_least(K3, 4));

    // Test 4: Cycle C_4 (chromatic index 2)
    Graph C4 = create_cycle(4, f);
    EXPECT_TRUE(chromatic_index_at_most(C4, 2));
    EXPECT_FALSE(chromatic_index_at_most(C4, 1));
    EXPECT_TRUE(chromatic_index_at_least(C4, 2));
    EXPECT_FALSE(chromatic_index_at_least(C4, 3));

    // Test 5: Cycle C_5 (chromatic index 3)
    Graph C5 = create_cycle(5, f);
    EXPECT_TRUE(chromatic_index_at_most(C5, 3));
    EXPECT_FALSE(chromatic_index_at_most(C5, 2));
    EXPECT_TRUE(chromatic_index_at_least(C5, 3));
    EXPECT_FALSE(chromatic_index_at_least(C5, 4));

    // Test 6: Graph with loops (should be uncolourable)
    Graph loop_graph = create_empty_graph(2, f);
    addE(loop_graph, Location(0, 0), f);  // Self-loop
    addE(loop_graph, Location(0, 1), f);  // Regular edge
    EXPECT_FALSE(chromatic_index_at_most(loop_graph, 1000));
    EXPECT_TRUE(chromatic_index_at_least(loop_graph, 1000));

    // Test edge coloring wrapper function
    EXPECT_TRUE(is_k_edge_colourable(K3, 3));
    EXPECT_FALSE(is_k_edge_colourable(K3, 2));

    // Consistency tests: verify against exact computations for small complete graphs
    for (int n = 1; n <= 4; ++n) {
        Graph Kn = create_complete_graph(n, f);
        int exact_chi = chromatic_index_basic(Kn);

        // Test that optimized functions are consistent
        EXPECT_TRUE(chromatic_index_at_most(Kn, exact_chi));
        if (exact_chi > 0) {
            EXPECT_FALSE(chromatic_index_at_most(Kn, exact_chi - 1));
        }
        EXPECT_TRUE(chromatic_index_at_least(Kn, exact_chi));
        EXPECT_FALSE(chromatic_index_at_least(Kn, exact_chi + 1));
    }
}

TEST_F(ColourTest, BasicChromaticNumberCriticality) {
    Factory f;
    Graph C5 = create_cycle(5, f);
    Graph C6 = create_cycle(6, f);

    EXPECT_TRUE(is_chromatic_number_vertex_critical_basic(C5));
    EXPECT_TRUE(is_k_chromatic_number_vertex_critical_basic(C5, 3));
    EXPECT_FALSE(is_k_chromatic_number_vertex_critical_basic(C5, 2));
    EXPECT_FALSE(is_chromatic_number_vertex_critical_basic(C6));

    EXPECT_TRUE(is_chromatic_number_edge_critical_basic(C5));
    EXPECT_TRUE(is_k_chromatic_number_edge_critical_basic(C5, 3));
    EXPECT_FALSE(is_k_chromatic_number_edge_critical_basic(C5, 2));
    EXPECT_FALSE(is_chromatic_number_edge_critical_basic(C6));
}

TEST_F(ColourTest, BasicChromaticIndexCriticality) {
    Factory f;
    Graph C5 = create_cycle(5, f);
    Graph C6 = create_cycle(6, f);

    EXPECT_TRUE(is_chromatic_index_vertex_critical_basic(C5));
    EXPECT_TRUE(is_k_chromatic_index_vertex_critical_basic(C5, 3));
    EXPECT_FALSE(is_k_chromatic_index_vertex_critical_basic(C5, 2));
    EXPECT_FALSE(is_chromatic_index_vertex_critical_basic(C6));

    EXPECT_TRUE(is_chromatic_index_edge_critical_basic(C5));
    EXPECT_TRUE(is_k_chromatic_index_edge_critical_basic(C5, 3));
    EXPECT_FALSE(is_k_chromatic_index_edge_critical_basic(C5, 2));
    EXPECT_FALSE(is_chromatic_index_edge_critical_basic(C6));
}

TEST_F(ColourTest, VertexColouringEnumeratorThrowsOnNegativeK) {
    Graph g(create_circuit(3));
    int dummy = 0;
    EXPECT_THROW(enumerate_colourings_basic(g, -1, countColourings, &dummy), std::invalid_argument);
}

TEST_F(ColourTest, EdgeColouringWithNegKThrows) {
    Graph g(create_circuit(4));
    EXPECT_THROW(is_edge_colourable_basic(g, -1), std::invalid_argument);
}

TEST_F(ColourTest, EdgeColouringPrecolourInconsistent) {
    Graph g(create_circuit(4));
    std::map<Edge, int> prec;
    Edge e = g[0].find(Location(0, 3))->e();
    prec[e] = 0;
    EXPECT_TRUE(is_edge_colourable_basic(g, 3, prec));
}

TEST_F(ColourTest, VertexColouringPrecolourInconsistent) {
    Graph g(create_circuit(4));
    std::map<Vertex, int> prec;
    prec[g[0].v()] = 0;
    prec[g[1].v()] = 0;
    EXPECT_FALSE(is_colourable_basic(g, 2, prec));
}

TEST_F(ColourTest, VertexEnumerateWithZeroColours) {
    Graph empty(create_empty_graph(0));
    int count = 0;
    EXPECT_TRUE(enumerate_colourings_basic(empty, 0, countColourings, &count));
    EXPECT_EQ(count, 1);
}

TEST_F(ColourTest, EdgeColourableWithPrecolourColour0) {
    Graph g(create_circuit(3));
    std::map<Edge, int> prec;
    for (auto &e : g.list(RP::all(), IP::primary(), IT::e())) {
        prec[e] = NO_COLOUR;
    }
    EXPECT_TRUE(is_edge_colourable_basic(g, 3, prec));
}

TEST_F(ColourTest, VertexColourableBasicK0EmptyGraph) {
    Graph empty(create_empty_graph(0));
    EXPECT_TRUE(is_colourable_basic(empty, 0));
}

TEST_F(ColourTest, VertexColourableBasicK0NonEmpty) {
    Graph g(create_empty_graph(1));
    EXPECT_FALSE(is_colourable_basic(g, 0));
}

TEST_F(ColourTest, VertexPrecolourWithZeroColours) {
    Graph g(create_empty_graph(2));
    std::map<Vertex, int> prec;
    EXPECT_FALSE(is_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, ColouringEnumeratorDoContinueFalse) {
    Graph g(create_circuit(3));
    int count = 0;
    enumerate_colourings_basic(g, 3, countColouringsStop, &count);
    EXPECT_EQ(count, 1);
}

TEST_F(ColourTest, EdgeColourablePrecolourZeroK) {
    Graph empty(create_empty_graph(0));
    std::map<Edge, int> prec;
    EXPECT_TRUE(is_edge_colourable_basic(empty, 0, prec));
}

TEST_F(ColourTest, EdgeColourableK0NonEmpty) {
    Graph g(create_empty_graph(3));
    addE(g, Location(0, 1));
    EXPECT_FALSE(is_edge_colourable_basic(g, 0));
}

TEST_F(ColourTest, EdgeColourablePrecolourK0NonEmpty) {
    Graph g(create_empty_graph(3));
    addE(g, Location(0, 1));
    std::map<Edge, int> prec;
    Edge e = g[0].find(Location(0, 1))->e();
    prec[e] = 0;
    EXPECT_FALSE(is_edge_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, IsValidEdgeColouringOutOfRange) {
    Graph g(create_circuit(3));
    sat_model::EdgeColouring colouring;
    for (auto &loc : g.list(RP::all(), IP::primary(), IT::l())) {
        colouring[loc] = 0;
    }
    ASSERT_FALSE(colouring.empty());
    colouring.begin()->second = 3;
    EXPECT_FALSE(is_valid_edge_colouring(g, 3, colouring));
}

TEST_F(ColourTest, IsColourableBasicNegK) {
    Graph g(create_circuit(3));
    EXPECT_THROW(is_colourable_basic(g, -1), std::invalid_argument);
}

TEST_F(ColourTest, IsEdgeColourableBasicNegK) {
    Graph g(create_circuit(3));
    EXPECT_THROW(is_edge_colourable_basic(g, -1), std::invalid_argument);
}

TEST_F(ColourTest, IsEdgeColourableBasicWithPrecolourNegK) {
    Graph g(create_circuit(3));
    std::map<Edge, int> prec;
    EXPECT_THROW(is_edge_colourable_basic(g, -1, prec), std::invalid_argument);
}

TEST_F(ColourTest, ChromaticIndexBasicRegularPath) {
    Graph g(create_path_edges(3));
    EXPECT_EQ(chromatic_index_basic(g), 2);
}

TEST_F(ColourTest, ChromaticNumberBasicEmptyReturns0) {
    Graph g(create_empty_graph(0));
    EXPECT_EQ(chromatic_number_basic(g), 0);
}

TEST_F(ColourTest, ChromaticNumberBasicNoEdgesReturns1) {
    Graph g(create_empty_graph(5));
    EXPECT_EQ(chromatic_number_basic(g), 1);
}

TEST_F(ColourTest, ChromaticNumberBasicReturnsUncolourable) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 0));
    EXPECT_EQ(chromatic_number_basic(g), UNCOLOURABLE);
}

TEST_F(ColourTest, ChromaticIndexBasicReturnsUncolourable) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 0));
    EXPECT_EQ(chromatic_index_basic(g), UNCOLOURABLE);
}

TEST_F(ColourTest, VertexCriticalityValidationThrowsOnKLessThan2) {
    Graph g(create_circuit(3));
    EXPECT_THROW(
        validate_basic_vertex_deletion_criticality_input(g, 1, "test"), std::invalid_argument
    );
    EXPECT_THROW(
        validate_basic_edge_deletion_criticality_input(g, 1, "test"), std::invalid_argument
    );
}

TEST_F(ColourTest, VertexCriticalityValidationThrowsOnNoEdges) {
    Graph g(create_empty_graph(5));
    EXPECT_THROW(
        validate_basic_vertex_deletion_criticality_input(g, 3, "test"), std::invalid_argument
    );
    EXPECT_THROW(
        validate_basic_edge_deletion_criticality_input(g, 3, "test"), std::invalid_argument
    );
}

TEST_F(ColourTest, EdgeColourableBasicK0NonEmptyWithPrecolour) {
    Graph g(create_empty_graph(3));
    addE(g, Location(0, 1));
    std::map<Edge, int> prec;
    EXPECT_FALSE(is_edge_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, EdgeColourableBasicLoopWithPrecolour) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 0));
    std::map<Edge, int> prec;
    EXPECT_FALSE(is_edge_colourable_basic(g, 3, prec));
}

TEST_F(ColourTest, EdgeColourableBasicNegKWithPrecolour) {
    Graph g(create_circuit(3));
    std::map<Edge, int> prec;
    EXPECT_THROW(is_edge_colourable_basic(g, -1, prec), std::invalid_argument);
}

TEST_F(ColourTest, ColouringEnumeratorNegativeK) {
    Graph g(create_circuit(3));
    EXPECT_THROW((internal::ColouringEnumerator<>(g, -1)), std::invalid_argument);
}

TEST_F(ColourTest, EnumerateColouringsNegativeMaxK) {
    Graph g(create_circuit(3));
    internal::ColouringEnumerator<> ce(g, 3);
    std::map<Vertex, int> prec;
    EXPECT_THROW(ce.enumerateColourings(nullptr, nullptr, prec, -2), std::invalid_argument);
}

TEST_F(ColourTest, IsEdgeColourableBasicWithPrecolourK0) {
    Graph g(create_empty_graph(0));
    std::map<Edge, int> prec;
    EXPECT_TRUE(is_edge_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, VertexColouringBasicPrecolourInvalidColour) {
    Graph g(create_circuit(3));
    std::map<Vertex, int> prec;
    prec[g[0].v()] = 5;  // colour >= k
    EXPECT_THROW(is_colourable_basic(g, 3, prec), std::invalid_argument);
}

TEST_F(ColourTest, VertexColouringBasicK0WithPrecolour) {
    Graph g(create_empty_graph(5));
    std::map<Vertex, int> prec;
    EXPECT_FALSE(is_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, ChromaticNumberAtLeastLoopThrows) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 0));
    EXPECT_THROW(chromatic_number_at_least(g, 1), std::invalid_argument);
}

TEST_F(ColourTest, ChromaticNumberAtLeastK0) {
    Graph g(create_circuit(3));
    EXPECT_TRUE(chromatic_number_at_least(g, 0));
    EXPECT_TRUE(chromatic_number_at_least(g, -1));
}

TEST_F(ColourTest, ChromaticIndexAtLeastK0) {
    Graph g(create_circuit(3));
    EXPECT_TRUE(chromatic_index_at_least(g, 0));
    EXPECT_TRUE(chromatic_index_at_least(g, -1));
}

TEST_F(ColourTest, IsColourableBasicNegKWithPrecolour) {
    Graph g(create_circuit(3));
    std::map<Vertex, int> prec;
    EXPECT_THROW(is_colourable_basic(g, -1, prec), std::invalid_argument);
}

TEST_F(ColourTest, IsColourableBasicK0NonEmptyWithPrecolour) {
    Graph g(create_empty_graph(1));
    std::map<Vertex, int> prec;
    EXPECT_FALSE(is_colourable_basic(g, 0, prec));
}

TEST_F(ColourTest, VertexCriticalityAutoDetectNoEdgesThrows) {
    Graph g(create_empty_graph(5));
    EXPECT_THROW(is_chromatic_number_vertex_critical_basic(g), std::invalid_argument);
    EXPECT_THROW(is_chromatic_number_edge_critical_basic(g), std::invalid_argument);
    EXPECT_THROW(is_chromatic_index_vertex_critical_basic(g), std::invalid_argument);
    EXPECT_THROW(is_chromatic_index_edge_critical_basic(g), std::invalid_argument);
}

TEST_F(ColourTest, EdgeColourableBasicLoopInPrecolourBranch) {
    // path through is_edge_colourable_basic(G, k, bool) break_symmetry branch with loop
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 0));
    EXPECT_FALSE(is_edge_colourable_basic(g, 3, true));
}

TEST_F(ColourTest, VertexCriticalityAutoDetectLoopThrows) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 1));
    addE(g, Location(0, 0));  // loop makes chromatic_number = UNCOLOURABLE
    EXPECT_THROW(is_chromatic_number_vertex_critical_basic(g), std::invalid_argument);
    EXPECT_THROW(is_chromatic_number_edge_critical_basic(g), std::invalid_argument);
}

TEST_F(ColourTest, IndexCriticalityAutoDetectLoopThrows) {
    Graph g(create_empty_graph(2));
    addE(g, Location(0, 1));
    addE(g, Location(0, 0));
    EXPECT_THROW(is_chromatic_index_vertex_critical_basic(g), std::invalid_argument);
    EXPECT_THROW(is_chromatic_index_edge_critical_basic(g), std::invalid_argument);
}

#if BA_GRAPH_HAS_KISSAT_SUPPORT
TEST_F(ColourTest, SatChromaticCriticality) {
    Factory f;
    Graph C5 = create_cycle(5, f);
    KissatSolver solver;
    ComputationContext ctx(&solver);
    EXPECT_TRUE(compute_is_chromatic_number_edge_critical(C5, ComputationMethod::SAT, ctx));
    EXPECT_TRUE(compute_is_chromatic_index_vertex_critical(C5, ComputationMethod::SAT, ctx));
    EXPECT_TRUE(compute_is_chromatic_index_edge_critical(C5, ComputationMethod::SAT, ctx));
}
#else
TEST_F(ColourTest, SatChromaticCriticality) { GTEST_SKIP() << "Kissat support not compiled in"; }
#endif

TEST_F(CVDHeuristicTest, OptimizedColouriserEarlyCVDSuccess) {
    // K4 is 3-regular and 3-edge-colourable; CVD finds coloring quickly,
    // so OptimizedColouriser returns true from the early CVD check.
    OptimizedColouriser colouriser;
    EXPECT_TRUE(colouriser.isColourable(create_complete_graph(4)));
}

TEST_F(CVDHeuristicTest, CVDEdgeColouringOnEdgelessGraphs) {
    // Empty graph (0 vertices): vacuously 4-regular, no edges to colour
    Graph empty = create_empty_graph(0);
    EXPECT_TRUE(has_cvd_edge_colouring_4regular(empty));
    EXPECT_TRUE(has_cvd_edge_colouring_general(empty));

    // Edgeless graph with vertices but no edges
    Graph no_edges = create_empty_graph(5);
    EXPECT_TRUE(has_cvd_edge_colouring_general(no_edges));
}
