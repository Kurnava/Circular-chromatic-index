// clang-format off
#include "implementation.h"

#include <optional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT
class CircularIndexTightCyclesSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularIndexTightCyclesSlowTest, Skipped) {}

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

Graph make_grid_graph(int rows, int cols) {
    Graph G(create_empty_graph(rows * cols));
    for (int r = 0; r < rows; ++r) {
        for (int c = 0; c < cols; ++c) {
            int v = r * cols + c;
            if (c + 1 < cols) {
                addE(G, Location(v, r * cols + c + 1));
            }
            if (r + 1 < rows) {
                addE(G, Location(v, (r + 1) * cols + c));
            }
        }
    }
    return G;
}

Graph make_ladder_graph(int length) {
    Graph G(create_empty_graph(2 * length));
    for (int i = 0; i + 1 < length; ++i) {
        addE(G, Location(i, i + 1));
        addE(G, Location(length + i, length + i + 1));
    }
    for (int i = 0; i < length; ++i) {
        addE(G, Location(i, length + i));
    }
    return G;
}

Graph make_cube_graph() {
    Graph G(create_empty_graph(8));
    for (int v = 0; v < 8; ++v) {
        for (int bit = 0; bit < 3; ++bit) {
            int u = v ^ (1 << bit);
            if (v < u) {
                addE(G, Location(v, u));
            }
        }
    }
    return G;
}

Graph make_wheel_graph(int rim_vertices) {
    Graph G(create_empty_graph(rim_vertices + 1));
    int center = rim_vertices;
    for (int i = 0; i < rim_vertices; ++i) {
        addE(G, Location(i, (i + 1) % rim_vertices));
        addE(G, Location(center, i));
    }
    return G;
}

Graph make_fan_graph(int path_vertices) {
    Graph G(create_empty_graph(path_vertices + 1));
    int center = path_vertices;
    for (int i = 0; i + 1 < path_vertices; ++i) {
        addE(G, Location(i, i + 1));
    }
    for (int i = 0; i < path_vertices; ++i) {
        addE(G, Location(center, i));
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

Graph make_doubled_cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
        addE(G, Location(i, (i + 1) % n));
    }
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

Graph make_petersen_graph() {
    Graph G(create_empty_graph(10));
    for (int i = 0; i < 5; ++i) {
        addE(G, Location(i, (i + 1) % 5));
        addE(G, Location(i, i + 5));
    }
    addE(G, Location(5, 7));
    addE(G, Location(7, 9));
    addE(G, Location(9, 6));
    addE(G, Location(6, 8));
    addE(G, Location(8, 5));
    return G;
}

Graph make_two_odd_cycles(int first, int second) {
    Graph G(create_empty_graph(first + second));
    for (int i = 0; i < first; ++i) {
        addE(G, Location(i, (i + 1) % first));
    }
    for (int i = 0; i < second; ++i) {
        addE(G, Location(first + i, first + ((i + 1) % second)));
    }
    return G;
}

void expect_value(
    const std::optional<std::pair<int, int> > &result, const std::pair<int, int> &expected
) {
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, expected);
}

void expect_number_matches_standard(const KissatSolver &solver, const Graph &G) {
    EXPECT_EQ(
        circular_chromatic_number_tight_cycles_method_sat(solver, G),
        circular_chromatic_number_sat(solver, G)
    );
}

void expect_index_matches_standard(const KissatSolver &solver, const Graph &G) {
    EXPECT_EQ(
        circular_chromatic_index_tight_cycles_method_sat(solver, G),
        circular_chromatic_index_sat(solver, G)
    );
}

}  // namespace

class CircularIndexTightCyclesSlowTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularIndexTightCyclesSlowTest, VertexOddCyclesC9ToC17HaveKnownValues) {
    for (int n : {9, 11, 13, 15, 17}) {
        SCOPED_TRACE(n);
        expect_value(
            circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(n)),
            {n, n / 2}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexEvenCyclesC8ToC30HaveValueTwo) {
    for (int n : {8, 10, 12, 14, 16, 20, 24, 30}) {
        SCOPED_TRACE(n);
        expect_value(
            circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(n)), {2, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexCompleteGraphsK6AndK7HaveKnownValues) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(6)), {6, 1}
    );
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_complete_graph(7)), {7, 1}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexCompleteBipartiteFamiliesHaveValueTwo) {
    for (auto parameters : {std::pair<int, int>{2, 5}, {3, 3}, {3, 6}, {4, 5}}) {
        SCOPED_TRACE(std::to_string(parameters.first) + "," + std::to_string(parameters.second));
        expect_value(
            circular_chromatic_number_tight_cycles_method_sat(
                solver, make_complete_bipartite_graph(parameters.first, parameters.second)
            ),
            {2, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexGridGraphsHaveValueTwo) {
    for (auto parameters : {std::pair<int, int>{2, 6}, {3, 4}, {4, 4}}) {
        SCOPED_TRACE(std::to_string(parameters.first) + "," + std::to_string(parameters.second));
        expect_value(
            circular_chromatic_number_tight_cycles_method_sat(
                solver, make_grid_graph(parameters.first, parameters.second)
            ),
            {2, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexLaddersAndCubeHaveValueTwo) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_ladder_graph(8)), {2, 1}
    );
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_cube_graph()), {2, 1}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexTwoOddCyclesTakeMaximumValue) {
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_two_odd_cycles(5, 7)), {5, 2}
    );
    expect_value(
        circular_chromatic_number_tight_cycles_method_sat(solver, make_two_odd_cycles(3, 9)), {3, 1}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexWheelsMatchStandardMethod) {
    for (int n : {4, 5, 6, 7, 8}) {
        SCOPED_TRACE(n);
        expect_number_matches_standard(solver, make_wheel_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexFansMatchStandardMethod) {
    for (int n : {5, 6, 7, 8}) {
        SCOPED_TRACE(n);
        expect_number_matches_standard(solver, make_fan_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexKnownGraphsMatchStandardMethod) {
    expect_number_matches_standard(solver, make_petersen_graph());
    expect_number_matches_standard(solver, make_fat_triangle(2));
}

TEST_F(CircularIndexTightCyclesSlowTest, VertexProgressStreamsForSeveralGraphsAreNonempty) {
    for (int n : {5, 7, 9}) {
        std::ostringstream out;
        auto result =
            circular_chromatic_number_tight_cycles_method_sat(solver, make_cycle_graph(n), &out);
        ASSERT_TRUE(result.has_value());
        EXPECT_FALSE(out.str().empty());
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeOddCyclesC9ToC17HaveKnownValues) {
    for (int n : {9, 11, 13, 15, 17}) {
        SCOPED_TRACE(n);
        expect_value(
            circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(n)),
            {n, n / 2}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeEvenCyclesC8ToC30HaveValueTwo) {
    for (int n : {8, 10, 12, 14, 16, 20, 24, 30}) {
        SCOPED_TRACE(n);
        expect_value(
            circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(n)), {2, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeLongPathsHaveValueTwo) {
    for (int n : {8, 12, 20, 30}) {
        SCOPED_TRACE(n);
        expect_value(
            circular_chromatic_index_tight_cycles_method_sat(solver, make_path_graph(n)), {2, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeLargeStarsHaveExpectedDegreeValue) {
    for (int leaves : {8, 10, 12}) {
        SCOPED_TRACE(leaves);
        expect_value(
            circular_chromatic_index_tight_cycles_method_sat(solver, make_star_graph(leaves)),
            {leaves, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeCompleteBipartiteFamiliesHaveMaximumDegreeValue) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(2, 6)
        ),
        {6, 1}
    );
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(3, 5)
        ),
        {5, 1}
    );
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(
            solver, make_complete_bipartite_graph(4, 4)
        ),
        {4, 1}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeCompleteGraphsHaveKnownValues) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_complete_graph(5)), {5, 1}
    );
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_complete_graph(6)), {5, 1}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeParallelEdgesHaveCliqueValues) {
    for (int multiplicity : {5, 6, 7, 8}) {
        SCOPED_TRACE(multiplicity);
        expect_value(
            circular_chromatic_index_tight_cycles_method_sat(
                solver, make_parallel_edges_graph(multiplicity)
            ),
            {multiplicity, 1}
        );
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeDoubledEvenCyclesMatchStandardMethod) {
    for (int n : {4, 6, 8}) {
        SCOPED_TRACE(n);
        expect_index_matches_standard(solver, make_doubled_cycle_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeDoubledOddCyclesMatchStandardMethod) {
    for (int n : {3, 5, 7}) {
        SCOPED_TRACE(n);
        expect_index_matches_standard(solver, make_doubled_cycle_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeFatTrianglesMatchStandardMethod) {
    for (int multiplicity : {2, 3}) {
        SCOPED_TRACE(multiplicity);
        expect_index_matches_standard(solver, make_fat_triangle(multiplicity));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgePetersenGraphHasElevenOverThree) {
    expect_value(
        circular_chromatic_index_tight_cycles_method_sat(solver, make_petersen_graph()), {11, 3}
    );
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgePetersenGraphMatchesStandardMethod) {
    Graph G(make_petersen_graph());
    expect_index_matches_standard(solver, G);
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeGridGraphsMatchStandardMethod) {
    for (auto parameters : {std::pair<int, int>{2, 5}, {3, 4}, {4, 4}}) {
        SCOPED_TRACE(std::to_string(parameters.first) + "," + std::to_string(parameters.second));
        expect_index_matches_standard(solver, make_grid_graph(parameters.first, parameters.second));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeLaddersAndCubeMatchStandardMethod) {
    expect_index_matches_standard(solver, make_ladder_graph(8));
    expect_index_matches_standard(solver, make_cube_graph());
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeWheelsMatchStandardMethod) {
    for (int n : {4, 5, 6, 7}) {
        SCOPED_TRACE(n);
        expect_index_matches_standard(solver, make_wheel_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeFansMatchStandardMethod) {
    for (int n : {5, 6, 7, 8}) {
        SCOPED_TRACE(n);
        expect_index_matches_standard(solver, make_fan_graph(n));
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeProgressStreamsForSeveralOddCyclesAreNonempty) {
    for (int n : {5, 7, 9}) {
        std::ostringstream out;
        auto result =
            circular_chromatic_index_tight_cycles_method_sat(solver, make_cycle_graph(n), &out);
        ASSERT_TRUE(result.has_value());
        EXPECT_FALSE(out.str().empty());
    }
}

TEST_F(CircularIndexTightCyclesSlowTest, EdgeClassOneProgressStreamsStayEmpty) {
    for (int leaves : {4, 6, 8}) {
        std::ostringstream out;
        auto result =
            circular_chromatic_index_tight_cycles_method_sat(solver, make_star_graph(leaves), &out);
        expect_value(result, {leaves, 1});
        EXPECT_TRUE(out.str().empty());
    }
}

#endif