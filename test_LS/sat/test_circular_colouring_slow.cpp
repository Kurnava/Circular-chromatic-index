// clang-format off
#include "implementation.h"

#include <algorithm>
#include <fstream>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <graphs/cubic.hpp>
#include <io/unified_io.hpp>
#include <operations/line_graph.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT

class CircularColouringSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularColouringSlowTest, Skipped) {}

#else

namespace {

Graph cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

Graph path_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i + 1 < n; ++i) {
        addE(G, Location(i, i + 1));
    }
    return G;
}

Graph complete_graph_manual(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            addE(G, Location(i, j));
        }
    }
    return G;
}

Graph complete_bipartite_graph_manual(int left, int right) {
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
    for (int r = 0; r < rows; ++r) {
        for (int c = 0; c < cols; ++c) {
            int v = r * cols + c;
            if (c + 1 < cols) {
                addE(G, Location(v, v + 1));
            }
            if (r + 1 < rows) {
                addE(G, Location(v, v + cols));
            }
        }
    }
    return G;
}

Graph cube_graph() {
    Graph G(create_empty_graph(8));
    for (int i = 0; i < 8; ++i) {
        for (int j = i + 1; j < 8; ++j) {
            int diff = i ^ j;
            if (diff != 0 && (diff & (diff - 1)) == 0) {
                addE(G, Location(i, j));
            }
        }
    }
    return G;
}

Graph wheel_graph(int rim_length) {
    Graph G(create_empty_graph(rim_length + 1));
    int center = rim_length;
    for (int i = 0; i < rim_length; ++i) {
        addE(G, Location(i, (i + 1) % rim_length));
        addE(G, Location(i, center));
    }
    return G;
}

Graph fan_graph(int path_vertices) {
    Graph G(create_empty_graph(path_vertices + 1));
    int center = path_vertices;
    for (int i = 0; i + 1 < path_vertices; ++i) {
        addE(G, Location(i, i + 1));
    }
    for (int i = 0; i < path_vertices; ++i) {
        addE(G, Location(i, center));
    }
    return G;
}

Graph petersen_graph() {
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

Graph disjoint_cycle_union(int n1, int n2) {
    Graph G(create_empty_graph(n1 + n2));
    for (int i = 0; i < n1; ++i) {
        addE(G, Location(i, (i + 1) % n1));
    }
    for (int i = 0; i < n2; ++i) {
        addE(G, Location(n1 + i, n1 + ((i + 1) % n2)));
    }
    return G;
}

Graph disjoint_complete_union(int n1, int n2) {
    Graph G(create_empty_graph(n1 + n2));
    for (int i = 0; i < n1; ++i) {
        for (int j = i + 1; j < n1; ++j) {
            addE(G, Location(i, j));
        }
    }
    for (int i = 0; i < n2; ++i) {
        for (int j = i + 1; j < n2; ++j) {
            addE(G, Location(n1 + i, n1 + j));
        }
    }
    return G;
}

Graph multi_two_vertex(int count) {
    Graph G(create_empty_graph(2));
    for (int i = 0; i < count; ++i) {
        addE(G, Location(0, 1));
    }
    return G;
}

Graph fat_triangle(int a, int b, int c) {
    Graph G(create_empty_graph(3));
    for (int i = 0; i < a; ++i) {
        addE(G, Location(0, 1));
    }
    for (int i = 0; i < b; ++i) {
        addE(G, Location(1, 2));
    }
    for (int i = 0; i < c; ++i) {
        addE(G, Location(2, 0));
    }
    return G;
}

Graph doubled_cycle(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
        addE(G, Location(i, (i + 1) % n));
    }
    return G;
}

std::vector<Graph> load_simple_graphs_upto_order(int max_order) {
    std::ifstream fin(
        std::string(BA_GRAPH_RESOURCES_DIR) + "/graphs/all/all_simple_graphs_upto09.g6"
    );
    if (!fin) {
        throw std::runtime_error("failed to open all_simple_graphs_upto09.g6");
    }

    std::vector<Graph> graphs;
    std::string line;
    while (std::getline(fin, line)) {
        if (line.empty()) {
            continue;
        }

        Graph G = read_graph(line, GraphIOFormat::IOF_GRAPH6);
        if (G.order() > max_order) {
            break;
        }
        graphs.push_back(std::move(G));
    }

    if (graphs.empty()) {
        throw std::runtime_error("no graphs loaded from all_simple_graphs_upto09.g6");
    }
    return graphs;
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
        if (it == colouring.end()) {
            return false;
        }
        if (it->second < 0 || it->second >= p) {
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
        if (it == colouring.end()) {
            return false;
        }
        if (it->second < 0 || it->second >= p) {
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

bool is_less_fraction(std::pair<int, int> lhs, std::pair<int, int> rhs) {
    return static_cast<long long>(lhs.first) * rhs.second <
           static_cast<long long>(rhs.first) * lhs.second;
}

void expect_circular_number(
    const SatSolver &solver, const Graph &G, std::pair<int, int> expected, const std::string &name
) {
    auto result = circular_chromatic_number_sat(solver, G);
    ASSERT_TRUE(result.has_value()) << name;
    EXPECT_EQ(*result, expected) << name;
}

void expect_circular_index(
    const SatSolver &solver, const Graph &G, std::pair<int, int> expected, const std::string &name
) {
    auto result = circular_chromatic_index_sat(solver, G);
    ASSERT_TRUE(result.has_value()) << name;
    EXPECT_EQ(*result, expected) << name;
}

}  // namespace

class CircularColouringSlowTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularColouringSlowTest, KnownOddCycleCircularChromaticNumbersAndIndices) {
    const std::vector<std::pair<int, int> > cases = {{3, 1},  {5, 2},  {7, 3},  {9, 4},
                                                     {11, 5}, {13, 6}, {15, 7}, {17, 8}};

    for (auto expected : cases) {
        int n = expected.first;
        Graph C = cycle_graph(n);
        std::string name = "C_" + std::to_string(n);
        expect_circular_number(solver, C, expected, name);
        expect_circular_index(solver, C, expected, name);
    }
}

TEST_F(CircularColouringSlowTest, KnownEvenCycleCircularChromaticNumbersAndIndices) {
    for (int n : {4, 6, 8, 10, 12, 14, 16, 18, 20}) {
        Graph C = cycle_graph(n);
        std::string name = "C_" + std::to_string(n);
        expect_circular_number(solver, C, {2, 1}, name);
        expect_circular_index(solver, C, {2, 1}, name);
    }
}

TEST_F(CircularColouringSlowTest, CompleteGraphCircularChromaticNumbers) {
    for (int n : {3, 4, 5, 6, 7, 8}) {
        Graph K = complete_graph_manual(n);
        expect_circular_number(solver, K, {n, 1}, "K_" + std::to_string(n));
    }
}

TEST_F(CircularColouringSlowTest, CompleteGraphCircularChromaticIndices) {
    expect_circular_index(solver, complete_graph_manual(3), {3, 1}, "K_3");
    expect_circular_index(solver, complete_graph_manual(4), {3, 1}, "K_4");
    expect_circular_index(solver, complete_graph_manual(5), {5, 1}, "K_5");
}

TEST_F(CircularColouringSlowTest, DisconnectedGraphsUseLargestComponentValue) {
    expect_circular_number(solver, disjoint_cycle_union(3, 4), {3, 1}, "C_3 union C_4");
    expect_circular_number(solver, disjoint_cycle_union(5, 7), {5, 2}, "C_5 union C_7");
    expect_circular_number(solver, disjoint_complete_union(3, 5), {5, 1}, "K_3 union K_5");

    expect_circular_index(solver, disjoint_cycle_union(3, 4), {3, 1}, "C_3 union C_4");
    expect_circular_index(solver, disjoint_cycle_union(5, 7), {5, 2}, "C_5 union C_7");
}

TEST_F(CircularColouringSlowTest, BipartiteFamiliesHaveCircularChromaticNumberTwo) {
    const std::vector<std::pair<std::string, std::function<Graph()> > > cases = {
        {"path_12", [] { return path_graph(12); }},
        {"K_1_10", [] { return complete_bipartite_graph_manual(1, 10); }},
        {"K_2_3", [] { return complete_bipartite_graph_manual(2, 3); }},
        {"K_3_3", [] { return complete_bipartite_graph_manual(3, 3); }},
        {"K_4_5", [] { return complete_bipartite_graph_manual(4, 5); }},
        {"grid_2_5", [] { return grid_graph(2, 5); }},
        {"grid_3_4", [] { return grid_graph(3, 4); }},
        {"cube", [] { return cube_graph(); }},
    };

    for (const auto &[name, factory] : cases) {
        Graph G = factory();
        expect_circular_number(solver, G, {2, 1}, name);
    }
}

TEST_F(CircularColouringSlowTest, WheelAndFanCircularChromaticNumbers) {
    const std::vector<std::pair<int, std::pair<int, int> > > wheel_cases = {
        {3, {4, 1}}, {4, {3, 1}}, {5, {4, 1}},  {6, {3, 1}},  {7, {4, 1}},
        {8, {3, 1}}, {9, {4, 1}}, {10, {3, 1}}, {11, {4, 1}}, {12, {3, 1}},
    };

    for (auto [rim_length, expected] : wheel_cases) {
        expect_circular_number(
            solver, wheel_graph(rim_length), expected, "wheel_" + std::to_string(rim_length)
        );
    }

    for (int path_vertices : {3, 4, 5, 6, 7, 8, 9}) {
        expect_circular_number(
            solver, fan_graph(path_vertices), {3, 1}, "fan_" + std::to_string(path_vertices)
        );
    }
}

TEST_F(CircularColouringSlowTest, SelectedKnownCircularChromaticIndices) {
    expect_circular_index(solver, petersen_graph(), {11, 3}, "Petersen");
    expect_circular_index(solver, multi_two_vertex(2), {2, 1}, "two vertices with 2 edges");
    expect_circular_index(solver, multi_two_vertex(3), {3, 1}, "two vertices with 3 edges");
    expect_circular_index(solver, multi_two_vertex(4), {4, 1}, "two vertices with 4 edges");
    expect_circular_index(solver, multi_two_vertex(5), {5, 1}, "two vertices with 5 edges");
    expect_circular_index(solver, fat_triangle(1, 1, 2), {4, 1}, "fat triangle 1,1,2");
    expect_circular_index(solver, fat_triangle(1, 2, 2), {5, 1}, "fat triangle 1,2,2");
    expect_circular_index(solver, fat_triangle(2, 2, 2), {6, 1}, "fat triangle 2,2,2");
    expect_circular_index(solver, doubled_cycle(4), {4, 1}, "doubled C_4");
    expect_circular_index(solver, doubled_cycle(5), {5, 1}, "doubled C_5");
}

TEST_F(CircularColouringSlowTest, BoundaryFractionsAroundKnownCircularChromaticNumbers) {
    Graph K3 = complete_graph_manual(3);
    Graph K4 = complete_graph_manual(4);
    Graph C5 = cycle_graph(5);
    Graph C7 = cycle_graph(7);
    Graph bipartite = complete_bipartite_graph_manual(3, 3);

    EXPECT_FALSE(is_circularly_colourable_sat(solver, K3, 29, 10));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, K3, 3, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, K3, 10, 3));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, K4, 39, 10));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, K4, 4, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, K4, 9, 2));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, C5, 12, 5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, C5, 5, 2));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, C7, 13, 6));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, C7, 7, 3));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, bipartite, 19, 10));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, bipartite, 2, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, bipartite, 21, 10));
}

TEST_F(CircularColouringSlowTest, BoundaryFractionsAroundKnownCircularChromaticIndices) {
    Graph C5 = cycle_graph(5);
    Graph C7 = cycle_graph(7);
    Graph K4 = complete_graph_manual(4);
    Graph petersen = petersen_graph();

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, C5, 12, 5));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, C5, 5, 2));

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, C7, 13, 6));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, C7, 7, 3));

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, K4, 29, 10));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, K4, 3, 1));

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, petersen, 7, 2));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, petersen, 11, 3));
}

TEST_F(CircularColouringSlowTest, ConstructiveVertexColouringsAreValidOnNamedGraphs) {
    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        cases = {
            {"C_5", [] { return cycle_graph(5); }, {5, 2}},
            {"C_7", [] { return cycle_graph(7); }, {7, 3}},
            {"K_4", [] { return complete_graph_manual(4); }, {4, 1}},
            {"K_3_4", [] { return complete_bipartite_graph_manual(3, 4); }, {2, 1}},
            {"wheel_5", [] { return wheel_graph(5); }, {4, 1}},
            {"wheel_6", [] { return wheel_graph(6); }, {3, 1}},
        };

    for (const auto &[name, factory, fraction] : cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto colouring = is_circularly_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(colouring.has_value()) << name << " fraction=" << p << "/" << q;
        EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *colouring, p, q))
            << name << " fraction=" << p << "/" << q;
    }
}

TEST_F(CircularColouringSlowTest, ConstructiveEdgeColouringsAreValidOnNamedGraphs) {
    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        cases = {
            {"C_5", [] { return cycle_graph(5); }, {5, 2}},
            {"C_7", [] { return cycle_graph(7); }, {7, 3}},
            {"K_4", [] { return complete_graph_manual(4); }, {3, 1}},
            {"K_5", [] { return complete_graph_manual(5); }, {5, 1}},
            {"multi_4", [] { return multi_two_vertex(4); }, {4, 1}},
            {"fat_triangle_1_2_2", [] { return fat_triangle(1, 2, 2); }, {5, 1}},
            {"Petersen", [] { return petersen_graph(); }, {11, 3}},
        };

    for (const auto &[name, factory, fraction] : cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(colouring.has_value()) << name << " fraction=" << p << "/" << q;
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, p, q))
            << name << " fraction=" << p << "/" << q;
    }
}

TEST_F(CircularColouringSlowTest, NonCoprimeConstructiveColouringsAreScaledCorrectly) {
    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        vertex_cases = {
            {"C_5", [] { return cycle_graph(5); }, {10, 4}},
            {"K_3", [] { return complete_graph_manual(3); }, {6, 2}},
            {"K_2_3", [] { return complete_bipartite_graph_manual(2, 3); }, {8, 4}},
        };

    for (const auto &[name, factory, fraction] : vertex_cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto colouring = is_circularly_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(colouring.has_value()) << name;
        EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *colouring, p, q)) << name;
    }

    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        edge_cases = {
            {"C_5", [] { return cycle_graph(5); }, {10, 4}},
            {"K_4", [] { return complete_graph_manual(4); }, {6, 2}},
            {"multi_3", [] { return multi_two_vertex(3); }, {9, 3}},
        };

    for (const auto &[name, factory, fraction] : edge_cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(colouring.has_value()) << name;
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, p, q)) << name;
    }
}

TEST_F(CircularColouringSlowTest, ReturnedVertexCircularChromaticNumberIsMinimalOnSmallGraphs) {
    auto graphs = load_simple_graphs_upto_order(5);

    for (const Graph &G : graphs) {
        auto result = circular_chromatic_number_sat(solver, G);
        ASSERT_TRUE(result.has_value()) << "order=" << G.order() << " size=" << G.size();

        auto [p, q] = *result;
        if (p == 0) {
            EXPECT_EQ(G.order(), 0);
            continue;
        }

        EXPECT_TRUE(is_circularly_colourable_sat(solver, G, p, q))
            << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/" << q;

        int chi = chromatic_number_sat(solver, G);
        if (chi > 1) {
            auto candidates =
                internal::computeCircularColouringFractions(G.order(), chi - 1, chi, false, true);
            for (auto candidate : candidates) {
                if (!is_less_fraction(candidate, *result)) {
                    break;
                }
                EXPECT_FALSE(
                    is_circularly_colourable_sat(solver, G, candidate.first, candidate.second)
                ) << "order="
                  << G.order() << " size=" << G.size() << " candidate=" << candidate.first << "/"
                  << candidate.second << " result=" << p << "/" << q;
            }
        }
    }
}

TEST_F(CircularColouringSlowTest, ConstructiveVertexColouringsAreValidOnSmallGraphs) {
    auto graphs = load_simple_graphs_upto_order(5);

    for (const Graph &G : graphs) {
        for (auto [p, q] : std::vector<std::pair<int, int> >{{3, 1}, {5, 2}, {7, 3}}) {
            bool exists = is_circularly_colourable_sat(solver, G, p, q);
            auto colouring = is_circularly_colourable_sat_constructive(solver, G, p, q);
            EXPECT_EQ(colouring.has_value(), exists)
                << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/" << q;
            if (colouring.has_value()) {
                EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *colouring, p, q))
                    << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/"
                    << q;
            }
        }
    }
}

TEST_F(CircularColouringSlowTest, ConstructiveEdgeColouringsAreValidOnSmallGraphs) {
    auto graphs = load_simple_graphs_upto_order(5);

    for (const Graph &G : graphs) {
        for (auto [p, q] : std::vector<std::pair<int, int> >{{3, 1}, {5, 2}, {7, 3}}) {
            bool exists = is_circularly_edge_colourable_sat(solver, G, p, q);
            auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, p, q);
            EXPECT_EQ(colouring.has_value(), exists)
                << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/" << q;
            if (colouring.has_value()) {
                EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, p, q))
                    << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/"
                    << q;
            }
        }
    }
}

TEST_F(CircularColouringSlowTest, EdgeIndexReturnedValueIsColourableOnSmallGraphs) {
    auto graphs = load_simple_graphs_upto_order(5);

    for (const Graph &G : graphs) {
        auto result = circular_chromatic_index_sat(solver, G);
        ASSERT_TRUE(result.has_value()) << "order=" << G.order() << " size=" << G.size();

        auto [p, q] = *result;
        if (p == 0) {
            EXPECT_EQ(G.size(), 0);
            continue;
        }

        EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, p, q))
            << "order=" << G.order() << " size=" << G.size() << " fraction=" << p << "/" << q;
    }
}

TEST_F(CircularColouringSlowTest, LongerOddCycleC19) {
    Graph G = cycle_graph(19);
    expect_circular_number(solver, G, {19, 9}, "C_19");
    expect_circular_index(solver, G, {19, 9}, "C_19");
}

TEST_F(CircularColouringSlowTest, LongerOddCycleC21) {
    Graph G = cycle_graph(21);
    expect_circular_number(solver, G, {21, 10}, "C_21");
    expect_circular_index(solver, G, {21, 10}, "C_21");
}

TEST_F(CircularColouringSlowTest, LongerOddCycleC25) {
    Graph G = cycle_graph(25);
    expect_circular_number(solver, G, {25, 12}, "C_25");
    expect_circular_index(solver, G, {25, 12}, "C_25");
}

TEST_F(CircularColouringSlowTest, LargerEvenCyclesHaveValueTwo) {
    for (int n : {22, 24, 28, 32, 36, 40}) {
        Graph G = cycle_graph(n);
        expect_circular_number(solver, G, {2, 1}, "even cycle");
        expect_circular_index(solver, G, {2, 1}, "even cycle");
    }
}

TEST_F(CircularColouringSlowTest, LargerCompleteGraphK9) {
    expect_circular_number(solver, complete_graph_manual(9), {9, 1}, "K_9");
}

TEST_F(CircularColouringSlowTest, CompleteGraphK5BoundaryFractions) {
    Graph G = complete_graph_manual(5);
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 49, 10));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 11, 2));
}

TEST_F(CircularColouringSlowTest, CompleteGraphK6BoundaryFractions) {
    Graph G = complete_graph_manual(6);
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 59, 10));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 6, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 13, 2));
}

TEST_F(CircularColouringSlowTest, CompleteBipartiteEdgeIndexK23) {
    expect_circular_index(solver, complete_bipartite_graph_manual(2, 3), {3, 1}, "K_2_3");
}

TEST_F(CircularColouringSlowTest, CompleteBipartiteEdgeIndexK35) {
    expect_circular_index(solver, complete_bipartite_graph_manual(3, 5), {5, 1}, "K_3_5");
}

TEST_F(CircularColouringSlowTest, CompleteBipartiteEdgeIndexK44) {
    expect_circular_index(solver, complete_bipartite_graph_manual(4, 4), {4, 1}, "K_4_4");
}

TEST_F(CircularColouringSlowTest, PathEdgeIndices) {
    for (int n : {3, 4, 7, 12, 20}) {
        expect_circular_index(solver, path_graph(n), {2, 1}, "path");
    }
}

TEST_F(CircularColouringSlowTest, StarEdgeIndices) {
    for (int leaves : {3, 4, 5, 8, 12}) {
        expect_circular_index(
            solver, complete_bipartite_graph_manual(1, leaves), {leaves, 1}, "star"
        );
    }
}

TEST_F(CircularColouringSlowTest, GridEdgeIndices) {
    expect_circular_index(solver, grid_graph(2, 5), {3, 1}, "grid_2_5");
    expect_circular_index(solver, grid_graph(3, 4), {4, 1}, "grid_3_4");
    expect_circular_index(solver, grid_graph(4, 4), {4, 1}, "grid_4_4");
}

TEST_F(CircularColouringSlowTest, CubeEdgeIndex) {
    expect_circular_index(solver, cube_graph(), {3, 1}, "cube");
}

TEST_F(CircularColouringSlowTest, LargerParallelEdgeMultigraphs) {
    for (int multiplicity : {6, 7, 8, 9, 10}) {
        expect_circular_index(solver, multi_two_vertex(multiplicity), {multiplicity, 1}, "multi");
    }
}

TEST_F(CircularColouringSlowTest, LargerFatTriangleCases) {
    expect_circular_index(solver, fat_triangle(2, 3, 3), {8, 1}, "fat_233");
    expect_circular_index(solver, fat_triangle(3, 3, 3), {9, 1}, "fat_333");
    expect_circular_index(solver, fat_triangle(2, 4, 4), {10, 1}, "fat_244");
}

TEST_F(CircularColouringSlowTest, MoreDoubledCycles) {
    expect_circular_index(solver, doubled_cycle(6), {4, 1}, "doubled_C6");
    expect_circular_index(solver, doubled_cycle(8), {4, 1}, "doubled_C8");
}

TEST_F(CircularColouringSlowTest, VertexPrecolouringOnLongOddCycleCanForceSatAndUnsat) {
    Graph G = cycle_graph(7);
    std::map<Vertex, int> valid;
    valid[G[0].v()] = 0;
    valid[G[1].v()] = 3;
    valid[G[3].v()] = 2;
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 7, 3, valid));

    auto witness = is_circularly_colourable_sat_constructive(solver, G, 7, 3, valid);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *witness, 7, 3));
    EXPECT_EQ(witness->at(0), 0);
    EXPECT_EQ(witness->at(1), 3);
    EXPECT_EQ(witness->at(3), 2);

    std::map<Vertex, int> invalid;
    invalid[G[0].v()] = 0;
    invalid[G[1].v()] = 1;
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 7, 3, invalid));
}

TEST_F(CircularColouringSlowTest, EdgePrecolouringOnOddCycleCanForceSatAndUnsat) {
    Graph G = cycle_graph(7);
    Edge e01 = G[0].find(Location(0, 1))->e();
    Edge e12 = G[1].find(Location(1, 2))->e();

    std::map<Edge, int> valid;
    valid[e01] = 0;
    valid[e12] = 3;
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 7, 3, valid));

    auto witness = is_circularly_edge_colourable_sat_constructive(solver, G, 7, 3, valid);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, 7, 3));

    std::map<Edge, int> invalid;
    invalid[e01] = 0;
    invalid[e12] = 1;
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 7, 3, invalid));
}

TEST_F(CircularColouringSlowTest, RelaxedVertexConstructiveFractionsStillProduceValidWitnesses) {
    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        cases = {
            {"C_5", [] { return cycle_graph(5); }, {11, 4}},
            {"C_7", [] { return cycle_graph(7); }, {15, 6}},
            {"K_4", [] { return complete_graph_manual(4); }, {9, 2}},
            {"wheel_5", [] { return wheel_graph(5); }, {17, 4}},
        };

    for (const auto &[name, factory, fraction] : cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto witness = is_circularly_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(witness.has_value()) << name;
        EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *witness, p, q)) << name;
    }
}

TEST_F(CircularColouringSlowTest, RelaxedEdgeConstructiveFractionsStillProduceValidWitnesses) {
    const std::vector<std::tuple<std::string, std::function<Graph()>, std::pair<int, int> > >
        cases = {
            {"C_5", [] { return cycle_graph(5); }, {11, 4}},
            {"C_7", [] { return cycle_graph(7); }, {15, 6}},
            {"K_4", [] { return complete_graph_manual(4); }, {10, 3}},
            {"K_5", [] { return complete_graph_manual(5); }, {6, 1}},
            {"Petersen", [] { return petersen_graph(); }, {15, 4}},
        };

    for (const auto &[name, factory, fraction] : cases) {
        Graph G = factory();
        auto [p, q] = fraction;
        auto witness = is_circularly_edge_colourable_sat_constructive(solver, G, p, q);
        ASSERT_TRUE(witness.has_value()) << name;
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, p, q)) << name;
    }
}

TEST_F(CircularColouringSlowTest, BoundaryFractionsForLongerCycles) {
    Graph C9 = cycle_graph(9);
    Graph C11 = cycle_graph(11);

    EXPECT_FALSE(is_circularly_colourable_sat(solver, C9, 11, 5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, C9, 9, 4));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, C9, 11, 5));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, C9, 9, 4));

    EXPECT_FALSE(is_circularly_colourable_sat(solver, C11, 13, 6));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, C11, 11, 5));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, C11, 13, 6));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, C11, 11, 5));
}

TEST_F(CircularColouringSlowTest, BoundaryFractionsForHighMultiplicityMultigraphs) {
    Graph multi6 = multi_two_vertex(6);
    Graph fat333 = fat_triangle(3, 3, 3);

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, multi6, 11, 2));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, multi6, 6, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, multi6, 13, 2));

    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, fat333, 17, 2));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, fat333, 9, 1));
}

TEST_F(CircularColouringSlowTest, CchnTightMethodAgreementAllSimpleUpTo5) {
    for (const Graph &G : load_simple_graphs_upto_order(5)) {
        if (G.order() < 2 || G.size() == 0) {
            continue;
        }
        auto baseline = circular_chromatic_number_sat(solver, G);
        auto tight_method = circular_chromatic_number_tight_cycles_method_sat(solver, G);
        ASSERT_EQ(baseline.has_value(), tight_method.has_value())
            << "order=" << G.order() << " size=" << G.size();
        if (baseline.has_value()) {
            EXPECT_EQ(*baseline, *tight_method)
                << "mismatch for order=" << G.order() << " size=" << G.size();
        }
    }
}

TEST_F(CircularColouringSlowTest, CchiTightMethodAgreementAllSimpleUpTo5) {
    for (const Graph &G : load_simple_graphs_upto_order(5)) {
        if (G.order() < 2 || G.size() == 0) {
            continue;
        }
        auto baseline = circular_chromatic_index_sat(solver, G);
        auto tight_method = circular_chromatic_index_tight_cycles_method_sat(solver, G);
        ASSERT_EQ(baseline.has_value(), tight_method.has_value())
            << "order=" << G.order() << " size=" << G.size();
        if (baseline.has_value()) {
            EXPECT_EQ(*baseline, *tight_method)
                << "mismatch for order=" << G.order() << " size=" << G.size();
        }
    }
}

TEST_F(CircularColouringSlowTest, CchiEdgeCriticalOnPetersen) {
    EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, create_petersen()));
}

TEST_F(CircularColouringSlowTest, CchiEdgeCriticalMatchesCchnVertexCriticalOnLineGraph) {
    Graph P = create_petersen();
    Graph LP = line_graph(P);
    EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, P));
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, LP));
}

TEST_F(CircularColouringSlowTest, CchiEdgeCriticalOnKnownSmallSnarks) {
    for (const auto &g6 : {"FUZv_", "FFzvO", "FUzro"}) {
        Graph G = read_graph_autodetect(g6);
        SCOPED_TRACE(g6);
        EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, G));
    }
}

TEST_F(CircularColouringSlowTest, CchiEdgeNotCriticalOnKnownNonCriticalGraphs) {
    for (const auto &g6 : {"L???CB?NBEWKoW"}) {
        Graph G = read_graph_autodetect(g6);
        SCOPED_TRACE(g6);
        EXPECT_FALSE(is_circular_chromatic_index_edge_critical_sat(solver, G));
    }
}

#endif