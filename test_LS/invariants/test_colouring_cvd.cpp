// clang-format off
#include "implementation.h"

#include <graphs/basic.hpp>
#include <graphs/cubic.hpp>
#include <invariants/colouring_cvd.hpp>
#include <invariants/degree.hpp>
#include <operations/add_graph.hpp>
#include <operations/line_graph.hpp>
// clang-format on

#include "gtest/gtest.h"

using namespace ba_graph;

// ---- Empty / trivial graphs ----

TEST(CVDEdgeColouring, EmptyGraph) {
    Graph G = create_empty_graph(0);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 10, 10, 42));
}

TEST(CVDEdgeColouring, IsolatedVertices) {
    Graph G = create_empty_graph(5);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 10, 10, 42));
}

TEST(CVDEdgeColouring, SingleEdge) {
    // Path with 1 edge: K2; trivially 1-edge-colourable (class 1)
    Graph G = create_path_edges(1);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 10, 10, 42));
}

// ---- Bipartite graphs (class 1 by König) ----

TEST(CVDEdgeColouring, EvenCycleC4) {
    Graph G = create_cycle(4);  // 2-regular, class 1
    EXPECT_TRUE(has_cvd_edge_colouring(G, 20, 10, 42));
}

TEST(CVDEdgeColouring, EvenCycleC6) {
    Graph G = create_cycle(6);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 20, 10, 42));
}

// ---- Class 1 cubic graphs ----

TEST(CVDEdgeColouring, PrismK33) {
    // Prism(3) = K_{3,3}: 3-regular, class 1
    Graph G = create_prism(3);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 50, 20, 42));
}

TEST(CVDEdgeColouring, PrismK4) {
    // Prism(4) = cube graph: 3-regular, class 1
    Graph G = create_prism(4);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 50, 20, 42));
}

// ---- Snark: class 2 cubic graph ----

TEST(CVDEdgeColouring, PetersenIsClass2) {
    // Petersen graph is the canonical snark: NOT 3-edge-colourable.
    // The heuristic should fail (return false) when given enough iterations.
    Graph G = create_petersen();
    // Run many iterations; should consistently return false for a true snark.
    bool result = has_cvd_edge_colouring(G, 200, 50, 42);
    EXPECT_FALSE(result);
}

// ---- General (non-regular) graphs ----

TEST(CVDEdgeColouring, GeneralStar) {
    // Star K_{1,4}: Delta=4, 4-edge-colourable
    Graph G = create_empty_graph(5);
    Factory &f = static_factory;
    for (int i = 1; i <= 4; ++i) {
        f.aE(G, Location(0, i));
    }
    EXPECT_TRUE(has_cvd_edge_colouring_general(G, 20, 10, 42));
}

TEST(CVDEdgeColouring, GeneralPath) {
    // Path P_5: Delta=2, class 1
    Graph G = create_path_vertices(5);
    EXPECT_TRUE(has_cvd_edge_colouring_general(G, 20, 10, 42));
}

// ---- Dispatch: has_cvd_edge_colouring selects correct variant ----

TEST(CVDEdgeColouring, DispatchOn3Regular) {
    Graph G = create_prism(4);  // 3-regular
    EXPECT_TRUE(is_d_regular(G, 3));
    EXPECT_TRUE(has_cvd_edge_colouring(G, 50, 20, 42));
}

TEST(CVDEdgeColouring, DispatchOnNonRegular) {
    // Mix of degrees: just a path
    Graph G = create_path_vertices(4);
    EXPECT_FALSE(is_d_regular(G, 3));
    EXPECT_TRUE(has_cvd_edge_colouring(G, 20, 10, 42));
}

// ---- Regression: fixed seed produces consistent result ----

TEST(CVDEdgeColouring, FixedSeedRepeatability) {
    Graph G = create_prism(4);
    bool r1 = has_cvd_edge_colouring(G, 30, 10, 123);
    bool r2 = has_cvd_edge_colouring(G, 30, 10, 123);
    EXPECT_EQ(r1, r2);
}

// ---- Loop handling ----

TEST(CVDEdgeColouring, GraphWithLoopReturnFalse) {
    // 3-regular variant: has_loop(H) check returns false.
    // Create prism (3-regular) and add a loop.
    Graph G = create_prism(3);
    addE(G, Location(0, 0));
    // The dispatch sees 3-regular -> calls 3regular variant which checks has_loop.
    EXPECT_FALSE(has_cvd_edge_colouring(G, 10, 5, 42));
}

// ---- Non-regular input for 3-regular variant ----

TEST(CVDEdgeColouring, NonRegularInputFor3RegularVariant) {
    // Call the 3-regular variant directly with a non-3-regular graph.
    // The function itself doesn't check regularity; it just processes the graph.
    Graph G = create_path_vertices(5);
    EXPECT_NO_THROW(has_cvd_edge_colouring_3regular(G, 10, 5));
}

TEST(CVDEdgeColouring, ThreeRegularVariantIgnoresDisconnectedTripleEdgeComponent) {
    Factory f;

    Graph colourable(create_triple_edge(f));
    Graph k4(create_complete_graph(4, f));
    add_graph(colourable, k4, 2, f);
    EXPECT_TRUE(has_cvd_edge_colouring_3regular(colourable, 50, 20));

    Graph uncolourable(create_triple_edge(f));
    Graph petersen(create_petersen(f));
    add_graph(uncolourable, petersen, 2, f);
    EXPECT_FALSE(has_cvd_edge_colouring_3regular(uncolourable, 200, 50));
}

TEST(CVDEdgeColouring, GeneralMaxDegreeThrows) {
    Factory f;
    Graph G = create_empty_graph(2, f);
    // Add 64 parallel edges from 0 to 1 to create max_degree 64
    for (int i = 0; i < 64; ++i) {
        addE(G, Location(0, 1), f);
    }
    EXPECT_THROW(has_cvd_edge_colouring_general(G, 10, 10, 42), std::runtime_error);
}

TEST(CVDEdgeColouring, GeneralMaxDegreeZeroWithEdges) {
    // Graph with isolated vertices only (max_deg == 0, but size() == 0)
    Graph G = create_empty_graph(5);
    EXPECT_TRUE(has_cvd_edge_colouring_general(G, 10, 10, 42));
}

TEST(CVDEdgeColouring, DispatchOn4Regular) {
    // Octahedron graph is 4-regular and class 1
    Factory f;
    Graph octahedron = line_graph(create_complete_graph(4), f);
    EXPECT_TRUE(is_d_regular(octahedron, 4));
    EXPECT_TRUE(has_cvd_edge_colouring(octahedron, -1, -1, 42));
}

TEST(CVDEdgeColouring, GeneralNonRegularColourableDispatch) {
    // has_cvd_edge_colouring dispatch to general variant
    Graph G(create_path_vertices(4));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 3));
    EXPECT_TRUE(is_d_regular(G, 3) == false);
    EXPECT_TRUE(has_cvd_edge_colouring(G, 20, 10, 42));
}

TEST(CVDEdgeColouring, ThreeRegularDigonReductionToEmpty) {
    // Create a graph that reduces to empty via digon reduction
    // This hits the H.order() == 0 path in has_cvd_edge_colouring_3regular
    Factory f;
    Graph G = create_empty_graph(2);
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    EXPECT_TRUE(has_cvd_edge_colouring_3regular(G, 10, 5, 42));
}

TEST(CVDEdgeColouring, GeneralExplicitLimits) {
    Graph G(create_prism(4));
    EXPECT_TRUE(has_cvd_edge_colouring_general(G, 1, 0, 42));
}

TEST(CVDEdgeColouring, GeneralDefaultRepetitionLimitForEmptyGraph) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    EXPECT_TRUE(has_cvd_edge_colouring_general(G, -1, -1, 42));
}

TEST(CVDEdgeColouring, FourRegularNot4RegularThrows) {
    Graph G(create_path_vertices(5));
    EXPECT_THROW(has_cvd_edge_colouring_4regular(G, 10, 5, 42), std::invalid_argument);
}

TEST(CVDEdgeColouring, FourRegularEmptyGraph) {
    Graph G = create_empty_graph(0);
    EXPECT_TRUE(has_cvd_edge_colouring_4regular(G, -1, -1, -1));
}

TEST(CVDEdgeColouring, FourRegularDefaultSeed) {
    Factory factory;
    Graph octahedron(line_graph(create_complete_graph(4), factory));
    EXPECT_TRUE(has_cvd_edge_colouring_4regular(octahedron, -1, -1, -1));
}

TEST(CVDEdgeColouring, ThreeRegularEmptyGraph) {
    // order 0 after digon reduction -> return true
    Graph G = create_empty_graph(0);
    EXPECT_TRUE(has_cvd_edge_colouring_3regular(G));
}

TEST(CVDEdgeColouring, ThreeRegularGraphWithLoop) {
    // has_loop(H) after digon reduction -> return false
    // max_deg=3: vertex 0 has loop (+2) + edge to 1 (+1) = 3
    Graph G = create_empty_graph(2);
    addE(G, Location(0, 0));
    addE(G, Location(0, 1));
    EXPECT_FALSE(has_cvd_edge_colouring_3regular(G));
}
