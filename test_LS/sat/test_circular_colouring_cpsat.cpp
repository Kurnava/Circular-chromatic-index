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
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
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

class CircularColouringCpsatFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "OR-Tools support not compiled in"; }
};

TEST_F(CircularColouringCpsatFastTest, Skipped) {}

#else

namespace {

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

Graph star_graph(int leaves) {
    Graph G(create_empty_graph(leaves + 1));
    for (int i = 1; i <= leaves; ++i) {
        addE(G, Location(0, i));
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

Graph two_incident_edges_graph() {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    return G;
}

Graph graph_with_loop() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 0));
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

Graph generalized_petersen_graph(int n, int k) {
    Graph G(create_empty_graph(2 * n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
        addE(G, Location(i, n + i));
        addE(G, Location(n + i, n + ((i + k) % n)));
    }
    return G;
}

Graph two_parallel_edges_graph() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
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

bool are_incident_locations(const Location &a, const Location &b) {
    return a.n1() == b.n1() || a.n1() == b.n2() || a.n2() == b.n1() || a.n2() == b.n2();
}

bool vector_has_size_and_range(const std::vector<int> &colours, std::size_t expected_size, int p) {
    if (colours.size() != expected_size) {
        return false;
    }
    return std::all_of(colours.begin(), colours.end(), [&](int colour) {
        return colour >= 0 && colour < p;
    });
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
    if (!vector_has_size_and_range(colours, edges.size(), p)) {
        return false;
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

class CircularColouringCpsatFastTest : public ::testing::Test {};

TEST_F(CircularColouringCpsatFastTest, VertexRejectsNegativePOnEmptyAndNonemptyGraphs) {
    EXPECT_FALSE(is_circularly_colourable_cpsat(create_empty_graph(0), -1, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(single_edge_graph(), -2, 1));
    EXPECT_FALSE(
        is_circularly_colourable_cpsat_constructive(create_empty_graph(0), -1, 1).has_value()
    );
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(single_edge_graph(), -2, 1).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, VertexRejectsNonPositiveQOnEmptyAndNonemptyGraphs) {
    EXPECT_FALSE(is_circularly_colourable_cpsat(create_empty_graph(0), 2, 0));
    EXPECT_FALSE(is_circularly_colourable_cpsat(single_edge_graph(), 2, -1));
    EXPECT_FALSE(
        is_circularly_colourable_cpsat_constructive(create_empty_graph(0), 2, 0).has_value()
    );
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(single_edge_graph(), 2, -1).has_value()
    );
}

TEST_F(
    CircularColouringCpsatFastTest, VertexZeroCircleAcceptsEmptyGraphInDecisionAndOutputPointer
) {
    std::vector<int> colours = {7};
    EXPECT_TRUE(is_circularly_colourable_cpsat(create_empty_graph(0), 0, 1, &colours));
    EXPECT_TRUE(colours.empty());

    colours = {1, 2, 3};
    EXPECT_TRUE(is_circularly_colourable_cpsat(create_empty_graph(0), 3, 1, &colours));
    EXPECT_TRUE(colours.empty());
}

TEST_F(CircularColouringCpsatFastTest, VertexZeroCircleAcceptsEmptyGraphConstructively) {
    auto zero = is_circularly_colourable_cpsat_constructive(create_empty_graph(0), 0, 1);
    ASSERT_TRUE(zero.has_value());
    EXPECT_TRUE(zero->empty());

    auto positive = is_circularly_colourable_cpsat_constructive(create_empty_graph(0), 3, 1);
    ASSERT_TRUE(positive.has_value());
    EXPECT_TRUE(positive->empty());
}

TEST_F(CircularColouringCpsatFastTest, VertexZeroCircleRejectsNonemptyGraphsTwice) {
    EXPECT_FALSE(is_circularly_colourable_cpsat(create_empty_graph(1), 0, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(single_edge_graph(), 0, 1));
    EXPECT_FALSE(
        is_circularly_colourable_cpsat_constructive(create_empty_graph(1), 0, 1).has_value()
    );
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(single_edge_graph(), 0, 1).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, VertexLoopIsRejectedBeforeModelBuilding) {
    Graph loop = graph_with_loop();
    EXPECT_FALSE(is_circularly_colourable_cpsat(loop, 3, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(loop, 5, 2));
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(loop, 3, 1).has_value());
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(loop, 5, 2).has_value());
}

TEST_F(CircularColouringCpsatFastTest, VertexTwoQGreaterThanPAcceptsGraphsWithoutEdges) {
    std::vector<int> colours;
    Graph isolated(create_empty_graph(4));
    ASSERT_TRUE(is_circularly_colourable_cpsat(isolated, 3, 2, &colours));
    EXPECT_TRUE(vector_has_size_and_range(colours, 4, 3));

    auto witness = is_circularly_colourable_cpsat_constructive(isolated, 3, 2);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(isolated, *witness, 3, 2));
}

TEST_F(CircularColouringCpsatFastTest, VertexTwoQGreaterThanPRejectsGraphsWithEdges) {
    EXPECT_FALSE(is_circularly_colourable_cpsat(single_edge_graph(), 3, 2));
    EXPECT_FALSE(is_circularly_colourable_cpsat(path_graph(3), 3, 2));
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(single_edge_graph(), 3, 2).has_value()
    );
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(path_graph(3), 3, 2).has_value());
}

TEST_F(CircularColouringCpsatFastTest, VertexDecisionFindsSimpleSatisfiableInstances) {
    EXPECT_TRUE(is_circularly_colourable_cpsat(single_edge_graph(), 2, 1));
    EXPECT_TRUE(is_circularly_colourable_cpsat(path_graph(4), 2, 1));
    EXPECT_TRUE(is_circularly_colourable_cpsat(cycle_graph(5), 5, 2));
    EXPECT_TRUE(is_circularly_colourable_cpsat(create_complete_graph(3), 3, 1));
}

TEST_F(CircularColouringCpsatFastTest, VertexDecisionFindsSimpleUnsatisfiableInstances) {
    EXPECT_FALSE(is_circularly_colourable_cpsat(single_edge_graph(), 1, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(cycle_graph(3), 2, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(cycle_graph(5), 2, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(create_complete_graph(4), 3, 1));
}

TEST_F(CircularColouringCpsatFastTest, VertexConstructiveReturnsValidWitnesses) {
    Graph path = path_graph(5);
    auto path_colouring = is_circularly_colourable_cpsat_constructive(path, 2, 1);
    ASSERT_TRUE(path_colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(path, *path_colouring, 2, 1));

    Graph pentagon = cycle_graph(5);
    auto pentagon_colouring = is_circularly_colourable_cpsat_constructive(pentagon, 5, 2);
    ASSERT_TRUE(pentagon_colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(pentagon, *pentagon_colouring, 5, 2));
}

TEST_F(CircularColouringCpsatFastTest, VertexConstructiveReturnsNulloptForUnsatInstances) {
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(single_edge_graph(), 1, 1).has_value()
    );
    EXPECT_FALSE(is_circularly_colourable_cpsat_constructive(cycle_graph(5), 2, 1).has_value());
    EXPECT_FALSE(
        is_circularly_colourable_cpsat_constructive(create_complete_graph(4), 3, 1).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, EdgeRejectsNegativePOnEmptyAndNonemptyGraphs) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(create_empty_graph(0), -1, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(single_edge_graph(), -2, 1));
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(create_empty_graph(0), -1, 1).has_value()
    );
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(single_edge_graph(), -2, 1).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, EdgeRejectsNonPositiveQOnEmptyAndNonemptyGraphs) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(create_empty_graph(0), 2, 0));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(single_edge_graph(), 2, -1));
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(create_empty_graph(0), 2, 0).has_value()
    );
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(single_edge_graph(), 2, -1).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, EdgeEmptyLineGraphAcceptsNoEdgesEvenForZeroCircle) {
    std::vector<int> colours = {9};
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(create_empty_graph(0), 0, 1, &colours));
    EXPECT_TRUE(colours.empty());

    colours = {1, 2};
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(create_empty_graph(3), 0, 1, &colours));
    EXPECT_TRUE(colours.empty());
}

TEST_F(CircularColouringCpsatFastTest, EdgeEmptyLineGraphConstructiveReturnsEmptyWitness) {
    auto empty = is_circularly_edge_colourable_cpsat_constructive(create_empty_graph(0), 0, 1);
    ASSERT_TRUE(empty.has_value());
    EXPECT_TRUE(empty->empty());

    auto edgeless = is_circularly_edge_colourable_cpsat_constructive(create_empty_graph(5), 2, 1);
    ASSERT_TRUE(edgeless.has_value());
    EXPECT_TRUE(edgeless->empty());
}

TEST_F(CircularColouringCpsatFastTest, EdgeZeroCircleRejectsGraphsWithEdgesTwice) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(single_edge_graph(), 0, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(path_graph(3), 0, 1));
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(single_edge_graph(), 0, 1).has_value()
    );
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(path_graph(3), 0, 1).has_value());
}

TEST_F(CircularColouringCpsatFastTest, EdgeLoopIsRejectedBeforeModelBuilding) {
    Graph loop = graph_with_loop();
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(loop, 3, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(loop, 5, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(loop, 3, 1).has_value());
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(loop, 5, 2).has_value());
}

TEST_F(CircularColouringCpsatFastTest, EdgeTwoQGreaterThanPAcceptsGraphsWithoutIncidentConflicts) {
    std::vector<int> colours;
    Graph one = single_edge_graph();
    ASSERT_TRUE(is_circularly_edge_colourable_cpsat(one, 3, 2, &colours));
    EXPECT_TRUE(vector_has_size_and_range(colours, 1, 3));

    Graph matching = matching_graph(2);
    ASSERT_TRUE(is_circularly_edge_colourable_cpsat(matching, 3, 2, &colours));
    EXPECT_TRUE(vector_has_size_and_range(colours, 2, 3));
}

TEST_F(CircularColouringCpsatFastTest, EdgeTwoQGreaterThanPRejectsGraphsWithIncidentConflicts) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(two_incident_edges_graph(), 3, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(cycle_graph(3), 3, 2));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(two_incident_edges_graph(), 3, 2)
                     .has_value());
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(cycle_graph(3), 3, 2).has_value()
    );
}

TEST_F(CircularColouringCpsatFastTest, EdgeDecisionFindsSimpleSatisfiableInstances) {
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(single_edge_graph(), 1, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(path_graph(4), 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(cycle_graph(4), 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(create_complete_graph(4), 3, 1));
}

TEST_F(CircularColouringCpsatFastTest, EdgeDecisionFindsSimpleUnsatisfiableInstances) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(two_incident_edges_graph(), 1, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(cycle_graph(3), 2, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(star_graph(3), 2, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(create_complete_graph(4), 2, 1));
}

TEST_F(CircularColouringCpsatFastTest, EdgeSymmetryBreakingTrueAndFalseBothSolveTriangleSixTwo) {
    Graph triangle = create_complete_graph(3);
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(triangle, 6, 2, nullptr, true));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(triangle, 6, 2, nullptr, false));

    auto sym = is_circularly_edge_colourable_cpsat_constructive(triangle, 6, 2, true);
    auto no_sym = is_circularly_edge_colourable_cpsat_constructive(triangle, 6, 2, false);
    ASSERT_TRUE(sym.has_value());
    ASSERT_TRUE(no_sym.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(triangle, *sym, 6, 2));
    EXPECT_TRUE(is_valid_edge_circular_colouring(triangle, *no_sym, 6, 2));
}

TEST_F(CircularColouringCpsatFastTest, EdgeSymmetryBreakingTrueAndFalseBothSolveK4ThreeOne) {
    Graph k4 = create_complete_graph(4);
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(k4, 3, 1, nullptr, true));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(k4, 3, 1, nullptr, false));

    auto sym = is_circularly_edge_colourable_cpsat_constructive(k4, 3, 1, true);
    auto no_sym = is_circularly_edge_colourable_cpsat_constructive(k4, 3, 1, false);
    ASSERT_TRUE(sym.has_value());
    ASSERT_TRUE(no_sym.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(k4, *sym, 3, 1));
    EXPECT_TRUE(is_valid_edge_circular_colouring(k4, *no_sym, 3, 1));
}

TEST_F(CircularColouringCpsatFastTest, EdgeConstructiveReturnsValidWitnesses) {
    Graph path = path_graph(5);
    auto path_colouring = is_circularly_edge_colourable_cpsat_constructive(path, 2, 1);
    ASSERT_TRUE(path_colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(path, *path_colouring, 2, 1));

    Graph k4 = create_complete_graph(4);
    auto k4_colouring = is_circularly_edge_colourable_cpsat_constructive(k4, 3, 1);
    ASSERT_TRUE(k4_colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(k4, *k4_colouring, 3, 1));
}

TEST_F(CircularColouringCpsatFastTest, EdgeConstructiveReturnsNulloptForUnsatInstances) {
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(two_incident_edges_graph(), 1, 1)
                     .has_value());
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat_constructive(cycle_graph(3), 2, 1).has_value()
    );
    EXPECT_FALSE(
        is_circularly_edge_colourable_cpsat_constructive(create_complete_graph(4), 2, 1).has_value()
    );
}

#if !BA_GRAPH_HAS_KISSAT_SUPPORT

TEST_F(CircularColouringCpsatFastTest, NumberAndIndexTestsSkippedWithoutKissat) {
    GTEST_SKIP() << "Kissat support not compiled in";
}

#else

TEST_F(CircularColouringCpsatFastTest, CircularChromaticNumberHandlesLoopAndEmptyGraphs) {
    KissatSolver solver;
    EXPECT_FALSE(circular_chromatic_number_cpsat(solver, graph_with_loop()).has_value());

    auto empty = circular_chromatic_number_cpsat(solver, create_empty_graph(0));
    ASSERT_TRUE(empty.has_value());
    EXPECT_EQ(*empty, std::make_pair(0, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticNumberHandlesEdgelessAndSingleEdgeGraphs) {
    KissatSolver solver;
    auto edgeless = circular_chromatic_number_cpsat(solver, create_empty_graph(4));
    ASSERT_TRUE(edgeless.has_value());
    EXPECT_EQ(*edgeless, std::make_pair(1, 1));

    auto edge = circular_chromatic_number_cpsat(solver, single_edge_graph());
    ASSERT_TRUE(edge.has_value());
    EXPECT_EQ(*edge, std::make_pair(2, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticNumberComputesOddCycles) {
    KissatSolver solver;
    auto c3 = circular_chromatic_number_cpsat(solver, cycle_graph(3));
    auto c5 = circular_chromatic_number_cpsat(solver, cycle_graph(5));
    ASSERT_TRUE(c3.has_value());
    ASSERT_TRUE(c5.has_value());
    EXPECT_EQ(*c3, std::make_pair(3, 1));
    EXPECT_EQ(*c5, std::make_pair(5, 2));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticNumberComputesCompleteAndBipartiteGraphs) {
    KissatSolver solver;
    auto k4 = circular_chromatic_number_cpsat(solver, create_complete_graph(4));
    auto k23 = circular_chromatic_number_cpsat(solver, complete_bipartite_graph(2, 3));
    ASSERT_TRUE(k4.has_value());
    ASSERT_TRUE(k23.has_value());
    EXPECT_EQ(*k4, std::make_pair(4, 1));
    EXPECT_EQ(*k23, std::make_pair(2, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticNumberProgressStreamBranchWritesOutput) {
    KissatSolver solver;
    std::ostringstream out;
    auto result = circular_chromatic_number_cpsat(solver, cycle_graph(5), &out);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(5, 2));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticIndexHandlesLoopAndNoEdges) {
    KissatSolver solver;
    EXPECT_FALSE(circular_chromatic_index_cpsat(solver, graph_with_loop()).has_value());

    auto empty = circular_chromatic_index_cpsat(solver, create_empty_graph(0));
    ASSERT_TRUE(empty.has_value());
    EXPECT_EQ(*empty, std::make_pair(0, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticIndexHandlesEdgelessAndSingleEdgeGraphs) {
    KissatSolver solver;
    auto edgeless = circular_chromatic_index_cpsat(solver, create_empty_graph(4));
    ASSERT_TRUE(edgeless.has_value());
    EXPECT_EQ(*edgeless, std::make_pair(0, 1));

    auto edge = circular_chromatic_index_cpsat(solver, single_edge_graph());
    ASSERT_TRUE(edge.has_value());
    EXPECT_EQ(*edge, std::make_pair(1, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticIndexEarlyReturnClassOneGraphs) {
    KissatSolver solver;
    auto c4 = circular_chromatic_index_cpsat(solver, cycle_graph(4));
    auto k4 = circular_chromatic_index_cpsat(solver, create_complete_graph(4));
    ASSERT_TRUE(c4.has_value());
    ASSERT_TRUE(k4.has_value());
    EXPECT_EQ(*c4, std::make_pair(2, 1));
    EXPECT_EQ(*k4, std::make_pair(3, 1));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticIndexUsesLineGraphBranchForClassTwoGraphs) {
    KissatSolver solver;
    auto c3 = circular_chromatic_index_cpsat(solver, cycle_graph(3));
    auto c5 = circular_chromatic_index_cpsat(solver, cycle_graph(5));
    ASSERT_TRUE(c3.has_value());
    ASSERT_TRUE(c5.has_value());
    EXPECT_EQ(*c3, std::make_pair(3, 1));
    EXPECT_EQ(*c5, std::make_pair(5, 2));
}

TEST_F(CircularColouringCpsatFastTest, CircularChromaticIndexProgressStreamBranchWritesOutput) {
    KissatSolver solver;
    std::ostringstream out;
    auto result = circular_chromatic_index_cpsat(solver, cycle_graph(5), &out);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(5, 2));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringCpsatFastTest, VertexCpSatAgreesWithSatOnSelectedSmallCases) {
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
            is_circularly_colourable_cpsat(G, test.p, test.q),
            is_circularly_colourable_sat(solver, G, test.p, test.q)
        );
    }
}

TEST_F(CircularColouringCpsatFastTest, EdgeCpSatAgreesWithSatOnSelectedSmallCases) {
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
            is_circularly_edge_colourable_cpsat(G, test.p, test.q),
            is_circularly_edge_colourable_sat(solver, G, test.p, test.q)
        );
    }
}

#endif

TEST_F(CircularColouringCpsatFastTest, ParallelEdgesAreHandledByEdgeColouring) {
    Graph G = two_parallel_edges_graph();
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 2, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 1, 1));

    auto witness = is_circularly_edge_colourable_cpsat_constructive(G, 2, 1);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *witness, 2, 1));
}

TEST_F(CircularColouringCpsatFastTest, FatTriangleBasicEdgeCasesAreHandled) {
    Graph G = fat_triangle_graph(2);

    std::vector<int> colours;
    ASSERT_TRUE(is_circularly_edge_colourable_cpsat(G, 6, 1, &colours));
    EXPECT_TRUE(is_valid_edge_circular_colouring_vector(G, colours, 6, 1));

    colours.clear();
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 5, 1, &colours));
    EXPECT_TRUE(colours.empty());
}

TEST_F(CircularColouringCpsatFastTest, PetersenGraphSelectedDecisionCases) {
    Graph G = generalized_petersen_graph(5, 2);
    EXPECT_TRUE(is_circularly_colourable_cpsat(G, 3, 1));
    EXPECT_FALSE(is_circularly_colourable_cpsat(G, 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_cpsat(G, 4, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_cpsat(G, 3, 1));
}

#endif
