// clang-format off
#include "implementation.h"

#include <optional>
#include <sstream>
#include <string>
#include <utility>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT
class CircularIndexTightCyclesFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularIndexTightCyclesFastTest, Skipped) {}

#else

namespace {

Graph make_path_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i + 1 < n; ++i) {
        addE(G, Location(i, i + 1));
    }
    return G;
}

Graph make_cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

Graph make_complete_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            addE(G, Location(i, j));
        }
    }
    return G;
}

Graph make_complete_bipartite_graph(int left, int right) {
    Graph G(create_empty_graph(left + right));
    for (int i = 0; i < left; ++i) {
        for (int j = 0; j < right; ++j) {
            addE(G, Location(i, left + j));
        }
    }
    return G;
}

Graph make_star_graph(int leaves) {
    Graph G(create_empty_graph(leaves + 1));
    for (int i = 1; i <= leaves; ++i) {
        addE(G, Location(0, i));
    }
    return G;
}

Graph make_parallel_edges_graph(int multiplicity) {
    Graph G(create_empty_graph(2));
    for (int i = 0; i < multiplicity; ++i) {
        addE(G, Location(0, 1));
    }
    return G;
}

Graph make_loop_graph(int n) {
    Graph G(create_empty_graph(n));
    if (n > 1) {
        addE(G, Location(0, 1));
    }
    addE(G, Location(0, 0));
    return G;
}

Graph make_two_disjoint_edges() {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    addE(G, Location(2, 3));
    return G;
}

Graph make_cycle_plus_isolated_vertex(int n) {
    Graph G(create_empty_graph(n + 1));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

Graph make_two_disjoint_triangles() {
    Graph G(create_empty_graph(6));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 0));
    addE(G, Location(3, 4));
    addE(G, Location(4, 5));
    addE(G, Location(5, 3));
    return G;
}

Graph make_triangle_plus_square() {
    Graph G(create_empty_graph(7));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 0));
    addE(G, Location(3, 4));
    addE(G, Location(4, 5));
    addE(G, Location(5, 6));
    addE(G, Location(6, 3));
    return G;
}

Graph make_fat_triangle(int multiplicity) {
    Graph G(create_empty_graph(3));
    for (int i = 0; i < multiplicity; ++i) {
        addE(G, Location(0, 1));
        addE(G, Location(1, 2));
        addE(G, Location(2, 0));
    }
    return G;
}

void expect_value(
    const std::optional<std::pair<int, int> > &result, const std::pair<int, int> &expected
) {
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, expected);
}

}  // namespace

class CircularIndexTightCyclesFastTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularIndexTightCyclesFastTest, VertexLoopReturnsNulloptOnLoopOnlyGraph) {
    EXPECT_FALSE(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_loop_graph(1)).has_value()
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexLoopReturnsNulloptOnGraphWithLoopAndEdge) {
    EXPECT_FALSE(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_loop_graph(3)).has_value()
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexEmptyGraphReturnsZeroOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, create_empty_graph(0)), {0, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexAnotherEmptyGraphCallReturnsZeroOverOne) {
    Graph empty(create_empty_graph(0));
    expect_value(circular_chromatic_number_tight_cycles_method_sat(solver, empty), {0, 1});
}

TEST_F(CircularIndexTightCyclesFastTest, VertexSingleIsolatedVertexReturnsOneOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, create_empty_graph(1)), {1, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexSeveralIsolatedVerticesReturnOneOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, create_empty_graph(5)), {1, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexSingleEdgeReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_path_graph(2)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexLongerPathReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_path_graph(6)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexEvenCycleC4ReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(4)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexEvenCycleC6ReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(6)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexTriangleReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(3)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexCompleteGraphK3ReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(3)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexOddCycleC5ReturnsFiveOverTwo) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(5)), {5, 2}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexOddCycleC7ReturnsSevenOverThree) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(7)), {7, 3}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexCompleteGraphK4ReturnsFourOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(4)), {4, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexCompleteGraphK5ReturnsFiveOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(5)), {5, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexCompleteBipartiteK23ReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(2, 3)
        ),
        {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexStarReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_star_graph(7)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexCyclePlusIsolatedVertexKeepsCycleValue) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(
            solver, make_cycle_plus_isolated_vertex(5)
        ),
        {5, 2}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexTwoDisjointTrianglesReturnThreeOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_two_disjoint_triangles()),
        {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexTrianglePlusSquareReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_triangle_plus_square()),
        {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexMethodMatchesStandardMethodOnC5) {
    Graph G(make_cycle_graph(5));
    EXPECT_EQ(
        circular_chromatic_number_tight_cycles_method_sat(solver, G),
        circular_chromatic_number_sat(solver, G)
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexMethodMatchesStandardMethodOnK4) {
    Graph G(make_complete_graph(4));
    EXPECT_EQ(
        circular_chromatic_number_tight_cycles_method_sat(solver, G),
        circular_chromatic_number_sat(solver, G)
    );
}

TEST_F(CircularIndexTightCyclesFastTest, VertexProgressStreamIsWrittenForOddCycle) {
    std::ostringstream out;
    auto result =
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(5), &out);
    expect_value(result, {5, 2});
    EXPECT_NE(out.str().find("trying"), std::string::npos);
}

TEST_F(CircularIndexTightCyclesFastTest, VertexProgressStreamIsWrittenForCompleteGraph) {
    std::ostringstream out;
    auto result =
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(4), &out);
    expect_value(result, {4, 1});
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeLoopReturnsNulloptOnLoopOnlyGraph) {
    EXPECT_FALSE(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_loop_graph(1)).has_value()
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeLoopReturnsNulloptOnGraphWithLoopAndEdge) {
    EXPECT_FALSE(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_loop_graph(3)).has_value()
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeEmptyGraphReturnsZeroOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, create_empty_graph(0)), {0, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeNonemptyGraphWithoutEdgesReturnsZeroOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, create_empty_graph(4)), {0, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeSingleEdgeReturnsOneOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_path_graph(2)), {1, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeTwoDisjointEdgesReturnOneOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_two_disjoint_edges()), {1, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgePathOfLengthTwoReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_path_graph(3)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgePathOfLengthFiveReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_path_graph(6)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeStarK14ReturnsFourOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_star_graph(4)), {4, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeStarK17ReturnsSevenOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_star_graph(7)), {7, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeEvenCycleC4ReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(4)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeEvenCycleC6ReturnsTwoOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(6)), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeTriangleReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(3)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeOddCycleC5ReturnsFiveOverTwo) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(5)), {5, 2}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeOddCycleC7ReturnsSevenOverThree) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(7)), {7, 3}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeCompleteGraphK3ReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_complete_graph(3)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeCompleteGraphK4ReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_complete_graph(4)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeCompleteBipartiteK23ReturnsThreeOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(2, 3)
        ),
        {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeCompleteBipartiteK34ReturnsFourOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(3, 4)
        ),
        {4, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeTwoParallelEdgesReturnTwoOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_parallel_edges_graph(2)),
        {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeThreeParallelEdgesReturnThreeOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_parallel_edges_graph(3)),
        {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeFourParallelEdgesReturnFourOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_parallel_edges_graph(4)),
        {4, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeFatTriangleMultiplicityTwoReturnsSixOverOne) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_fat_triangle(2)), {6, 1}
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeMethodMatchesStandardMethodOnC5) {
    Graph G(make_cycle_graph(5));
    EXPECT_EQ(
        circular_chromatic_index_tight_cycles_method_sat(solver, G),
        circular_chromatic_index_sat(solver, G)
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeMethodMatchesStandardMethodOnK4) {
    Graph G(make_complete_graph(4));
    EXPECT_EQ(
        circular_chromatic_index_tight_cycles_method_sat(solver, G),
        circular_chromatic_index_sat(solver, G)
    );
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeProgressStreamIsWrittenForOddCycle) {
    std::ostringstream out;
    auto result =
        circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(5), &out);
    expect_value(result, {5, 2});
    EXPECT_NE(out.str().find("trying"), std::string::npos);
}

TEST_F(CircularIndexTightCyclesFastTest, EdgeProgressStreamStaysEmptyForClassOneEarlyReturn) {
    std::ostringstream out;
    auto result =
        circular_chromatic_index_tight_cycles_method_sat(solver, make_star_graph(5), &out);
    expect_value(result, {5, 1});
    EXPECT_TRUE(out.str().empty());
}

#endif