#ifdef _GLIBCXX_DEBUG
#undef _GLIBCXX_DEBUG
#define BA_GRAPH_ORTOOLS_DISABLED_GLIBCXX_DEBUG
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
#include <sat/exec_circular_cpsat.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_ORTOOLS_SUPPORT

class CircularColouringCpsatSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "OR-Tools support not compiled in"; }
};

TEST_F(CircularColouringCpsatSlowTest, Skipped) {}

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

std::vector<Location> cpsat_edge_locations(const Graph &G) {
    std::vector<Number> order;
    std::map<Number, int> index;
    for (const auto &r : G) {
        order.push_back(r.n());
    }
    for (std::size_t i = 0; i < order.size(); ++i) {
        index[order[i]] = static_cast<int>(i);
    }

    std::vector<Location> edges;
    for (const auto &r : G) {
        int u = index[r.n()];
        for (const auto &inc : r) {
            int v = index[inc.n2()];
            if (v <= u) {
                continue;
            }
            edges.push_back(inc.l());
        }
    }
    return edges;
}

bool is_valid_edge_circular_colouring_vector(
    const Graph &G, const std::vector<int> &colours, int p, int q
) {
    auto edges = cpsat_edge_locations(G);
    if (colours.size() != edges.size()) {
        return false;
    }
    for (int colour : colours) {
        if (colour < 0 || colour >= p) {
            return false;
        }
    }
    for (std::size_t i = 0; i < edges.size(); ++i) {
        for (std::size_t j = i + 1; j < edges.size(); ++j) {
            if (are_incident_locations(edges[i], edges[j]) &&
                circular_distance(p, colours[i], colours[j]) < q) {
                return false;
            }
        }
    }
    return true;
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

class CircularColouringCpsatSlowTest : public ::testing::Test {};

TEST_F(CircularColouringCpsatSlowTest, OddCyclesHaveExpectedCircularChromaticNumbers) {
    KissatSolver solver;
    const std::vector<int> ns = {3, 5, 7, 9, 11, 13};
    for (int n : ns) {
        auto result = circular_chromatic_number_cpsat(solver, cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, n / 2)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, EvenCyclesHaveCircularChromaticNumberTwo) {
    KissatSolver solver;
    for (int n : {4, 6, 8, 10, 12, 16}) {
        auto result = circular_chromatic_number_cpsat(solver, cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, CompleteGraphsHaveExpectedCircularChromaticNumbers) {
    KissatSolver solver;
    for (int n : {3, 4, 5, 6, 7}) {
        auto result = circular_chromatic_number_cpsat(solver, create_complete_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, CompleteGraphBoundaryDecisionCases) {
    for (int n : {4, 5, 6, 7}) {
        Graph G = create_complete_graph(n);
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, n, 1)) << n;
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, n - 1, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, BipartiteFamiliesHaveCircularChromaticNumberTwo) {
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
        KissatSolver solver;
        auto result = circular_chromatic_number_cpsat(solver, factory());
        ASSERT_TRUE(result.has_value()) << name;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << name;
    }
}

TEST_F(CircularColouringCpsatSlowTest, BipartiteFamiliesDecisionBoundaries) {
    const std::vector<std::function<Graph()> > cases = {
        [] { return path_graph(10); },
        [] { return complete_bipartite_graph(3, 5); },
        [] { return grid_graph(4, 4); },
        [] { return cube_graph(); },
    };

    for (const auto &factory : cases) {
        Graph G = factory();
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, 2, 1));
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, 1, 1));
    }
}

TEST_F(CircularColouringCpsatSlowTest, WheelsHaveExpectedVertexBehaviour) {
    for (int rim : {4, 6, 8}) {
        Graph G = wheel_graph(rim);
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, 3, 1)) << rim;
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, 2, 1)) << rim;
    }
    for (int rim : {3, 5, 7}) {
        Graph G = wheel_graph(rim);
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, 4, 1)) << rim;
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, 3, 1)) << rim;
    }
}

TEST_F(CircularColouringCpsatSlowTest, FansHaveExpectedVertexBehaviour) {
    for (int n : {4, 6, 8, 10}) {
        Graph G = fan_graph(n);
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, 3, 1)) << n;
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, 2, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, GrotzschGraphSelectedVertexCases) {
    Graph G = grotzsch_graph();
    EXPECT_TRUE(is_circularly_colourable_cpsat(G, 4, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(G, 3, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(G, 2, 1));
}

TEST_F(CircularColouringCpsatSlowTest, LongOddCyclesDecisionBoundaries) {
    for (int n : {15, 17, 19, 21}) {
        Graph G = cycle_graph(n);
        EXPECT_TRUE(is_circularly_colourable_cpsat(G, n, n / 2)) << n;
        EXPECT_FALSE(is_circularly_colourable_cpsat(G, 2, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, VertexConstructiveWitnessesOnLargerGraphs) {
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return complete_bipartite_graph(3, 4); }, {2, 1}},
        {[] { return wheel_graph(6); }, {3, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {3, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        auto witness = is_circularly_colourable_cpsat_constructive(G, params.first, params.second);
        ASSERT_TRUE(witness.has_value());
        EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *witness, params.first, params.second));
    }
}

TEST_F(CircularColouringCpsatSlowTest, OddCyclesHaveExpectedCircularChromaticIndexes) {
    KissatSolver solver;
    for (int n : {3, 5, 7, 9, 11}) {
        auto result = circular_chromatic_index_cpsat(solver, cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(n, n / 2)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, EvenCyclesHaveCircularChromaticIndexTwo) {
    KissatSolver solver;
    for (int n : {4, 6, 8, 10, 12, 16}) {
        auto result = circular_chromatic_index_cpsat(solver, cycle_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(2, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, CompleteGraphEdgeIndexKnownCases) {
    const std::vector<std::pair<int, std::pair<int, int> > > cases = {
        {3, {3, 1}},
        {4, {3, 1}},
        {5, {5, 1}},
        {6, {5, 1}},
    };

    KissatSolver solver;
    for (const auto &[n, expected] : cases) {
        auto result = circular_chromatic_index_cpsat(solver, create_complete_graph(n));
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, expected) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, CompleteGraphEdgeDecisionBoundaries) {
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(create_complete_graph(4), 3, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(create_complete_graph(4), 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(create_complete_graph(5), 5, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(create_complete_graph(5), 4, 1));
}

TEST_F(CircularColouringCpsatSlowTest, StarEdgeIndexesMatchMaximumDegree) {
    KissatSolver solver;
    for (int leaves : {3, 4, 5, 8, 10}) {
        auto result = circular_chromatic_index_cpsat(solver, star_graph(leaves));
        ASSERT_TRUE(result.has_value()) << leaves;
        EXPECT_EQ(*result, std::make_pair(leaves, 1)) << leaves;
    }
}

TEST_F(CircularColouringCpsatSlowTest, CompleteBipartiteEdgeIndexesMatchMaximumDegree) {
    const std::vector<std::tuple<int, int, int> > cases = {
        {2, 3, 3},
        {3, 3, 3},
        {3, 5, 5},
        {4, 4, 4},
    };

    KissatSolver solver;
    for (const auto &[left, right, expected] : cases) {
        auto result = circular_chromatic_index_cpsat(solver, complete_bipartite_graph(left, right));
        ASSERT_TRUE(result.has_value()) << left << "," << right;
        EXPECT_EQ(*result, std::make_pair(expected, 1)) << left << "," << right;
    }
}

TEST_F(CircularColouringCpsatSlowTest, PetersenGraphEdgeCases) {
    Graph G = generalized_petersen_graph(5, 2);
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 4, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 3, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 11, 3));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 7, 2));
}

TEST_F(CircularColouringCpsatSlowTest, EdgeConstructiveWitnessesOnLargerGraphs) {
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(9); }, {9, 4}},
        {[] { return create_complete_graph(4); }, {3, 1}},
        {[] { return complete_bipartite_graph(3, 5); }, {5, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {4, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        std::vector<int> colours;
        ASSERT_TRUE(is_circularly_edge_colourable_cpsat(G, params.first, params.second, &colours));
        EXPECT_TRUE(is_valid_edge_circular_colouring_vector(G, colours, params.first, params.second)
        );

        auto witness =
            is_circularly_edge_colourable_cpsat_constructive(G, params.first, params.second);
        EXPECT_TRUE(witness.has_value());
    }
}

TEST_F(CircularColouringCpsatSlowTest, MatchingGraphsExerciseNoConflictTwoQGreaterThanPBranch) {
    for (int m : {2, 4, 8}) {
        Graph G = matching_graph(m);
        EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 3, 2)) << m;
        auto witness = is_circularly_edge_colourable_cpsat_constructive(G, 3, 2);
        ASSERT_TRUE(witness.has_value()) << m;
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, 3, 2)) << m;
    }
}

TEST_F(CircularColouringCpsatSlowTest, PathsAndCyclesExerciseConflictTwoQGreaterThanPBranch) {
    const std::vector<std::function<Graph()> > cases = {
        [] { return path_graph(3); },
        [] { return path_graph(8); },
        [] { return cycle_graph(4); },
        [] { return cycle_graph(6); },
    };

    for (const auto &factory : cases) {
        Graph G = factory();
        EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 3, 2));
        EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(G, 3, 2).has_value());
    }
}

TEST_F(CircularColouringCpsatSlowTest, FatTrianglesNeedSixColoursWhenMultiplicityTwo) {
    Graph G = fat_triangle_graph(2);
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 6, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 5, 1));
    KissatSolver solver;
    auto result = circular_chromatic_index_cpsat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(6, 1));
}

TEST_F(CircularColouringCpsatSlowTest, FatTrianglesNeedNineColoursWhenMultiplicityThree) {
    Graph G = fat_triangle_graph(3);
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 9, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 8, 1));
    KissatSolver solver;
    auto result = circular_chromatic_index_cpsat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(9, 1));
}

TEST_F(CircularColouringCpsatSlowTest, DoubledEvenCyclesHaveCircularIndexFour) {
    KissatSolver solver;
    for (int n : {4, 6, 8}) {
        Graph G = doubled_cycle_graph(n);
        EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 4, 1)) << n;
        EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 3, 1)) << n;
        auto result = circular_chromatic_index_cpsat(solver, G);
        ASSERT_TRUE(result.has_value()) << n;
        EXPECT_EQ(*result, std::make_pair(4, 1)) << n;
    }
}

TEST_F(CircularColouringCpsatSlowTest, EdgeSymmetryDoesNotOverconstrainSeveralGraphs) {
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return create_complete_graph(3); }, {6, 2}},
        {[] { return create_complete_graph(4); }, {3, 1}},
        {[] { return cycle_graph(5); }, {5, 2}},
        {[] { return generalized_petersen_graph(5, 2); }, {4, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        EXPECT_TRUE(
            is_circularly_edge_colourable_cpsat(G, params.first, params.second, nullptr, true)
        );
        EXPECT_TRUE(
            is_circularly_edge_colourable_cpsat(G, params.first, params.second, nullptr, false)
        );
    }
}

TEST_F(CircularColouringCpsatSlowTest, VertexOutputVectorsHaveExpectedSizesOnLargerGraphs) {
    std::vector<int> colours;
    Graph c17 = cycle_graph(17);
    ASSERT_TRUE(is_circularly_colourable_cpsat(c17, 17, 8, &colours));
    EXPECT_EQ(colours.size(), 17);

    Graph grid = grid_graph(4, 5);
    ASSERT_TRUE(is_circularly_colourable_cpsat(grid, 2, 1, &colours));
    EXPECT_EQ(colours.size(), 20);
}

TEST_F(CircularColouringCpsatSlowTest, EdgeOutputVectorsHaveExpectedSizesOnLargerGraphs) {
    std::vector<int> colours;
    Graph c17 = cycle_graph(17);
    ASSERT_TRUE(is_circularly_edge_colourable_cpsat(c17, 17, 8, &colours));
    EXPECT_EQ(colours.size(), 17);

    Graph k4 = create_complete_graph(4);
    ASSERT_TRUE(is_circularly_edge_colourable_cpsat(k4, 3, 1, &colours));
    EXPECT_EQ(colours.size(), 6);
}

#if BA_GRAPH_HAS_KISSAT_SUPPORT

TEST_F(CircularColouringCpsatSlowTest, VertexCpsatAgreesWithSatOnFamilySample) {
    KissatSolver solver;
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(7); }, {7, 3}},
        {[] { return cycle_graph(7); }, {2, 1}},
        {[] { return create_complete_graph(5); }, {5, 1}},
        {[] { return create_complete_graph(5); }, {4, 1}},
        {[] { return complete_bipartite_graph(4, 5); }, {2, 1}},
        {[] { return wheel_graph(5); }, {3, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        EXPECT_EQ(
            is_circularly_colourable_cpsat(G, params.first, params.second),
            is_circularly_colourable_sat(solver, G, params.first, params.second)
        );
    }
}

TEST_F(CircularColouringCpsatSlowTest, EdgeCpsatAgreesWithSatOnFamilySample) {
    KissatSolver solver;
    const std::vector<std::pair<std::function<Graph()>, std::pair<int, int> > > cases = {
        {[] { return cycle_graph(7); }, {7, 3}},
        {[] { return cycle_graph(7); }, {2, 1}},
        {[] { return create_complete_graph(5); }, {5, 1}},
        {[] { return create_complete_graph(5); }, {4, 1}},
        {[] { return complete_bipartite_graph(3, 4); }, {4, 1}},
        {[] { return generalized_petersen_graph(5, 2); }, {4, 1}},
    };

    for (const auto &[factory, params] : cases) {
        Graph G = factory();
        EXPECT_EQ(
            is_circularly_edge_colourable_cpsat(G, params.first, params.second),
            is_circularly_edge_colourable_sat(solver, G, params.first, params.second)
        );
    }
}

#endif

#endif