#ifdef _GLIBCXX_DEBUG
#undef _GLIBCXX_DEBUG
#define BA_GRAPH_CLASP_DISABLED_GLIBCXX_DEBUG
#endif

// clang-format off
#include "implementation.h"

#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_clasp.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_CLASP_SUPPORT

class CircularColouringClaspSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Clasp support not compiled in"; }
};

TEST_F(CircularColouringClaspSlowTest, Skipped) {}

#else

namespace {

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

Graph star_graph(int leaves) {
    Graph G(create_empty_graph(leaves + 1));
    for (int i = 1; i <= leaves; ++i) {
        addE(G, Location(0, i));
    }
    return G;
}

Graph complete_bipartite_graph(int left, int right) {
    Graph G(create_empty_graph(left + right));
    for (int i = 0; i < left; ++i) {
        for (int j = 0; j < right; ++j) {
            addE(G, Location(i, left + j));
        }
    }
    return G;
}

Graph grid_graph(int rows, int cols) {
    Graph G(create_empty_graph(rows * cols));
    auto id = [cols](int r, int c) { return r * cols + c; };
    for (int r = 0; r < rows; ++r) {
        for (int c = 0; c < cols; ++c) {
            if (r + 1 < rows) {
                addE(G, Location(id(r, c), id(r + 1, c)));
            }
            if (c + 1 < cols) {
                addE(G, Location(id(r, c), id(r, c + 1)));
            }
        }
    }
    return G;
}

Graph cube_graph() {
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

Graph wheel_graph(int rim) {
    Graph G(create_empty_graph(rim + 1));
    for (int i = 0; i < rim; ++i) {
        addE(G, Location(i, (i + 1) % rim));
        addE(G, Location(rim, i));
    }
    return G;
}

Graph fan_graph(int path_vertices) {
    Graph G(create_empty_graph(path_vertices + 1));
    for (int i = 0; i + 1 < path_vertices; ++i) {
        addE(G, Location(i, i + 1));
    }
    for (int i = 0; i < path_vertices; ++i) {
        addE(G, Location(path_vertices, i));
    }
    return G;
}

Graph generalized_petersen_graph(int n, int k) {
    Graph G(create_empty_graph(2 * n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
        addE(G, Location(i, n + i));
        addE(G, Location(n + i, n + ((i + k) % n)));
    }
    return G;
}

Graph grotzsch_graph() {
    Graph G(create_empty_graph(11));
    for (int i = 0; i < 5; ++i) {
        addE(G, Location(i, (i + 1) % 5));
    }
    for (int i = 0; i < 5; ++i) {
        addE(G, Location(5 + i, (i + 4) % 5));
        addE(G, Location(5 + i, (i + 1) % 5));
    }
    for (int i = 5; i < 10; ++i) {
        addE(G, Location(10, i));
    }
    return G;
}

Graph matching_graph(int edges_count) {
    Graph G(create_empty_graph(2 * edges_count));
    for (int i = 0; i < edges_count; ++i) {
        addE(G, Location(2 * i, 2 * i + 1));
    }
    return G;
}

Graph fat_triangle_graph(int multiplicity) {
    Graph G(create_empty_graph(3));
    for (int i = 0; i < multiplicity; ++i) {
        addE(G, Location(0, 1));
        addE(G, Location(1, 2));
        addE(G, Location(2, 0));
    }
    return G;
}

Graph doubled_cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

bool are_incident_locations(const Location &a, const Location &b) {
    return a.n1() == b.n1() || a.n1() == b.n2() || a.n2() == b.n1() || a.n2() == b.n2();
}

bool is_valid_vertex_circular_colouring(
    const Graph &G, const sat_model::VertexColouring &colouring, int p, int q
) {
    if (colouring.size() != static_cast<std::size_t>(G.order())) {
        return false;
    }
    for (const auto &r : G) {
        auto it = colouring.find(r.n());
        if (it == colouring.end() || it->second < 0 || it->second >= p) {
            return false;
        }
    }
    for (const auto &r : G) {
        for (const auto &inc : r) {
            if (inc.n2() <= r.n()) {
                continue;
            }
            auto c1 = colouring.find(r.n());
            auto c2 = colouring.find(inc.n2());
            if (c1 == colouring.end() || c2 == colouring.end()) {
                return false;
            }
            if (circular_distance(p, c1->second, c2->second) < q) {
                return false;
            }
        }
    }
    return true;
}

bool is_valid_edge_circular_colouring(
    const Graph &G, const sat_model::EdgeColouring &colouring, int p, int q
) {
    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    if (colouring.size() != edges.size()) {
        return false;
    }
    for (const auto &loc : edges) {
        auto it = colouring.find(loc);
        if (it == colouring.end() || it->second < 0 || it->second >= p) {
            return false;
        }
    }
    for (const auto &e1 : edges) {
        for (const auto &e2 : edges) {
            if (e1 == e2) {
                continue;
            }
            if (are_incident_locations(e1, e2) &&
                circular_distance(p, colouring.at(e1), colouring.at(e2)) < q) {
                return false;
            }
        }
    }
    return true;
}

}  // namespace

class CircularColouringClaspSlowTest : public ::testing::Test {};

TEST_F(CircularColouringClaspSlowTest, OddCyclesHaveExpectedCircularChromaticNumbers) {
    const std::vector<int> ns = {3, 5, 7, 9, 11, 13, 15, 17};
    for (int n : ns) {
        auto result = circular_chromatic_number_sat(ClaspSatSolver(), cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, n / 2)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, EvenCyclesHaveCircularChromaticNumberTwo) {
    for (int n : {4, 6, 8, 10, 12, 16, 20}) {
        auto result = circular_chromatic_number_sat(ClaspSatSolver(), cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, CompleteGraphsHaveExpectedCircularChromaticNumbers) {
    for (int n : {3, 4, 5, 6}) {
        auto result = circular_chromatic_number_sat(ClaspSatSolver(), create_complete_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, CompleteGraphBoundaryDecisionCases) {
    for (int n : {4, 5, 6}) {
        Graph G = create_complete_graph(n);
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, n, 1)) << n;
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, n - 1, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, BipartiteFamiliesHaveCircularChromaticNumberTwo) {
    const std::vector<std::pair<std::string, std::function<Graph()> > > cases = {
        {"path_12", [] { return path_graph(12); }},
        {"star_12", [] { return star_graph(12); }},
        {"K_2_5", [] { return complete_bipartite_graph(2, 5); }},
        {"K_3_4", [] { return complete_bipartite_graph(3, 4); }},
        {"grid_2_6", [] { return grid_graph(2, 6); }},
        {"grid_3_4", [] { return grid_graph(3, 4); }},
        {"cube", [] { return cube_graph(); }},
    };

    for (const auto &[name, factory] : cases) {
        auto result = circular_chromatic_number_sat(ClaspSatSolver(), factory());
        ASSERT_TRUE(result.has_value()) << name;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << name;
    }
}

TEST_F(CircularColouringClaspSlowTest, BipartiteFamiliesDecisionBoundaries) {
    const std::vector<std::function<Graph()> > cases = {
        [] { return path_graph(10); },
        [] { return complete_bipartite_graph(3, 5); },
        [] { return grid_graph(4, 4); },
        [] { return cube_graph(); },
    };

    for (const auto &factory : cases) {
        Graph G = factory();
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, 2, 1));
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 1, 1));
    }
}

TEST_F(CircularColouringClaspSlowTest, WheelsHaveExpectedVertexBehaviour) {
    for (int rim : {4, 6, 8}) {
        Graph G = wheel_graph(rim);
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, 3, 1)) << rim;
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 2, 1)) << rim;
    }
    for (int rim : {3, 5, 7}) {
        Graph G = wheel_graph(rim);
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, 4, 1)) << rim;
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 3, 1)) << rim;
    }
}

TEST_F(CircularColouringClaspSlowTest, FansHaveExpectedVertexBehaviour) {
    for (int n : {4, 6, 8, 10}) {
        Graph G = fan_graph(n);
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, 3, 1)) << n;
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 2, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, GrotzschGraphSelectedVertexCases) {
    Graph G = grotzsch_graph();
    EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, 4, 1));
    EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 3, 1));
    EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 2, 1));
}

TEST_F(CircularColouringClaspSlowTest, LongOddCyclesDecisionBoundaries) {
    for (int n : {15, 17, 19, 21, 23}) {
        Graph G = cycle_graph(n);
        EXPECT_TRUE(is_circularly_colourable_sat(ClaspSatSolver(), G, n, n / 2)) << n;
        EXPECT_FALSE(is_circularly_colourable_sat(ClaspSatSolver(), G, 2, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, VertexConstructiveWitnessesOnLargerGraphs) {
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return complete_bipartite_graph(3, 4); }, {2, 1}},
        {[] { return wheel_graph(6); }, {3, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {3, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        auto witness = is_circularly_colourable_sat_constructive(
            ClaspSatSolver(), G, params.first, params.second
        );
        ASSERT_TRUE(witness.has_value());
        EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *witness, params.first, params.second));
    }
}

TEST_F(CircularColouringClaspSlowTest, OddCyclesHaveExpectedCircularChromaticIndexes) {
    for (int n : {3, 5, 7, 9, 11, 13}) {
        auto result = circular_chromatic_index_sat(ClaspSatSolver(), cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, n / 2)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, EvenCyclesHaveCircularChromaticIndexTwo) {
    for (int n : {4, 6, 8, 10, 12, 16}) {
        auto result = circular_chromatic_index_sat(ClaspSatSolver(), cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, CompleteGraphEdgeIndexKnownCases) {
    const std::vector<std::pair<int, std::pair<int, int> > > cases = {
        {3, {3, 1}},
        {4, {3, 1}},
        {5, {5, 1}},
        {6, {5, 1}},
    };

    for (const auto &[n, expected] : cases) {
        auto result = circular_chromatic_index_sat(ClaspSatSolver(), create_complete_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, expected) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, CompleteGraphEdgeDecisionBoundaries) {
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), create_complete_graph(4), 3, 1)
    );
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), create_complete_graph(4), 2, 1)
    );
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), create_complete_graph(5), 5, 1)
    );
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), create_complete_graph(5), 4, 1)
    );
}

TEST_F(CircularColouringClaspSlowTest, StarEdgeIndexesMatchMaximumDegree) {
    for (int leaves : {3, 4, 5, 8, 10}) {
        auto result = circular_chromatic_index_sat(ClaspSatSolver(), star_graph(leaves));
        ASSERT_TRUE(result.has_value()) << leaves;
        EXPECT_EQ(*result, std::make_pair(leaves, 1)) << leaves;
    }
}

TEST_F(CircularColouringClaspSlowTest, CompleteBipartiteEdgeIndexesMatchMaximumDegree) {
    const std::vector<std::tuple<int, int, int> > cases = {
        {2, 3, 3},
        {3, 3, 3},
        {3, 5, 5},
        {4, 4, 4},
    };

    for (const auto &[left, right, expected] : cases) {
        auto result =
            circular_chromatic_index_sat(ClaspSatSolver(), complete_bipartite_graph(left, right));
        ASSERT_TRUE(result.has_value()) << left << "," << right;
        EXPECT_EQ(*result, std::make_pair(expected, 1)) << left << "," << right;
    }
}

TEST_F(CircularColouringClaspSlowTest, PetersenGraphEdgeCases) {
    Graph G = generalized_petersen_graph(5, 2);
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 4, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 3, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 11, 3));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 7, 2));
}

TEST_F(CircularColouringClaspSlowTest, EdgeConstructiveWitnessesOnLargerGraphs) {
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return create_complete_graph(4); }, {3, 1}},
        {[] { return complete_bipartite_graph(3, 5); }, {5, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {4, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        auto witness = is_circularly_edge_colourable_sat_constructive(
            ClaspSatSolver(), G, params.first, params.second
        );
        ASSERT_TRUE(witness.has_value());
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, params.first, params.second));
    }
}

TEST_F(CircularColouringClaspSlowTest, MatchingGraphsExerciseNoConflictTwoQGreaterThanPBranch) {
    for (int m : {2, 4, 8}) {
        Graph G = matching_graph(m);
        EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 3, 2)) << m;
        auto witness = is_circularly_edge_colourable_sat_constructive(ClaspSatSolver(), G, 3, 2);
        ASSERT_TRUE(witness.has_value()) << m;
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, 3, 2)) << m;
    }
}

TEST_F(CircularColouringClaspSlowTest, PathsAndCyclesExerciseConflictTwoQGreaterThanPBranch) {
    const std::vector<std::function<Graph()> > cases = {
        [] { return path_graph(3); },
        [] { return path_graph(8); },
        [] { return cycle_graph(4); },
        [] { return cycle_graph(6); },
    };

    for (const auto &factory : cases) {
        Graph G = factory();
        EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 3, 2));
        EXPECT_FALSE(
            is_circularly_edge_colourable_sat_constructive(ClaspSatSolver(), G, 3, 2).has_value()
        );
    }
}

TEST_F(CircularColouringClaspSlowTest, FatTrianglesNeedSixColoursWhenMultiplicityTwo) {
    Graph G = fat_triangle_graph(2);
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 6, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 5, 1));
    auto result = circular_chromatic_index_sat(ClaspSatSolver(), G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(6, 1));
}

TEST_F(CircularColouringClaspSlowTest, FatTrianglesNeedNineColoursWhenMultiplicityThree) {
    Graph G = fat_triangle_graph(3);
    EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 9, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 8, 1));
    auto result = circular_chromatic_index_sat(ClaspSatSolver(), G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(9, 1));
}

TEST_F(CircularColouringClaspSlowTest, DoubledEvenCyclesHaveCircularIndexFour) {
    for (int n : {4, 6, 8}) {
        Graph G = doubled_cycle_graph(n);
        EXPECT_TRUE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 4, 1)) << n;
        EXPECT_FALSE(is_circularly_edge_colourable_sat(ClaspSatSolver(), G, 3, 1)) << n;
        auto result = circular_chromatic_index_sat(ClaspSatSolver(), G);
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(4, 1)) << n;
    }
}

TEST_F(CircularColouringClaspSlowTest, VertexConstructiveWitnessesHaveExpectedSizes) {
    Graph c17 = cycle_graph(17);
    auto witness1 = is_circularly_colourable_sat_constructive(ClaspSatSolver(), c17, 17, 8);
    ASSERT_TRUE(witness1.has_value());
    EXPECT_EQ(witness1->size(), 17u);

    Graph grid = grid_graph(4, 5);
    auto witness2 = is_circularly_colourable_sat_constructive(ClaspSatSolver(), grid, 2, 1);
    ASSERT_TRUE(witness2.has_value());
    EXPECT_EQ(witness2->size(), 20u);
}

TEST_F(CircularColouringClaspSlowTest, EdgeConstructiveWitnessesHaveExpectedSizes) {
    Graph c17 = cycle_graph(17);
    auto witness1 = is_circularly_edge_colourable_sat_constructive(ClaspSatSolver(), c17, 17, 8);
    ASSERT_TRUE(witness1.has_value());
    EXPECT_EQ(witness1->size(), 17u);

    Graph k4 = create_complete_graph(4);
    auto witness2 = is_circularly_edge_colourable_sat_constructive(ClaspSatSolver(), k4, 3, 1);
    ASSERT_TRUE(witness2.has_value());
    EXPECT_EQ(witness2->size(), 6u);
}

#if BA_GRAPH_HAS_KISSAT_SUPPORT

TEST_F(CircularColouringClaspSlowTest, VertexClaspAgreesWithSatOnFamilySample) {
    KissatSolver solver;
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(7); }, {7, 3}},
        {[] { return cycle_graph(7); }, {2, 1}},
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return create_complete_graph(5); }, {5, 1}},
        {[] { return create_complete_graph(5); }, {4, 1}},
        {[] { return complete_bipartite_graph(4, 5); }, {2, 1}},
        {[] { return wheel_graph(5); }, {3, 1}},
        {[] { return fan_graph(6); }, {3, 1}},
        {[] { return grotzsch_graph(); }, {4, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        EXPECT_EQ(
            is_circularly_colourable_sat(ClaspSatSolver(), G, params.first, params.second),
            is_circularly_colourable_sat(solver, G, params.first, params.second)
        );
    }
}

TEST_F(CircularColouringClaspSlowTest, EdgeClaspAgreesWithSatOnFamilySample) {
    KissatSolver solver;
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(7); }, {7, 3}},
        {[] { return cycle_graph(7); }, {2, 1}},
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return create_complete_graph(5); }, {5, 1}},
        {[] { return create_complete_graph(5); }, {4, 1}},
        {[] { return complete_bipartite_graph(3, 4); }, {4, 1}},
        {[] { return complete_bipartite_graph(3, 5); }, {5, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {4, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {3, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        EXPECT_EQ(
            is_circularly_edge_colourable_sat(ClaspSatSolver(), G, params.first, params.second),
            is_circularly_edge_colourable_sat(solver, G, params.first, params.second)
        );
    }
}

#endif

#endif
