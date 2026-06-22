// clang-format off
#include "implementation.h"

#include <cstddef>
#include <map>
#include <stdexcept>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <graphs/cubic.hpp>
#include <operations/line_graph.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/cnf_colouring.hpp>
#include <sat/cnf_hcolouring.hpp>
#include <sat/exec_circumference.hpp>
#include <sat/exec_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on
#include "constructive_validation_utils.hpp"

using namespace ba_graph;

// ======== Criticality Validation Tests (no solver required) ========

TEST(ColouringCriticalityTest, VertexDeletionValidationKLessThanTwo) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    EXPECT_THROW(validate_vertex_deletion_criticality_input(G, 1, "test"), std::invalid_argument);
    EXPECT_THROW(validate_vertex_deletion_criticality_input(G, 0, "test"), std::invalid_argument);
}

TEST(ColouringCriticalityTest, VertexDeletionValidationEmptyGraph) {
    Graph G(create_empty_graph(3));
    EXPECT_THROW(validate_vertex_deletion_criticality_input(G, 2, "test"), std::invalid_argument);
}

TEST(ColouringCriticalityTest, EdgeDeletionValidationKLessThanTwo) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    EXPECT_THROW(validate_edge_deletion_criticality_input(G, 1, "test"), std::invalid_argument);
}

TEST(ColouringCriticalityTest, EdgeDeletionValidationEmptyGraph) {
    Graph G(create_empty_graph(3));
    EXPECT_THROW(validate_edge_deletion_criticality_input(G, 2, "test"), std::invalid_argument);
}

TEST(ColouringCriticalityTest, VertexDeletionValidationWithEdges) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    EXPECT_NO_THROW(validate_vertex_deletion_criticality_input(G, 2, "test"));
}

TEST(ColouringCriticalityTest, EdgeDeletionValidationWithEdges) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    EXPECT_NO_THROW(validate_edge_deletion_criticality_input(G, 2, "test"));
}

// ======== Decode functions error paths ========

TEST(EncodingDecodeTest, VertexColouringShortModel) {
    Number n0(0), n1(1);
    std::map<Number, CnfVarList> vars = {{n0, {0, 1}}, {n1, {2, 3}}};
    VertexColouringCnfEncoding encoding{CNF(4, {}), vars, 2};
    EXPECT_THROW(encoding.decode_model({true}), std::runtime_error);
}

TEST(EncodingDecodeTest, VertexColouringExtraVarsAllowed) {
    Graph G(create_petersen());
    auto encoding = build_vertex_colouring_cnf_encoding(G, 3);
    KissatSolver solver;
    auto model = solver.solve(encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_EQ(colouring.size(), static_cast<std::size_t>(G.order()));
    EXPECT_TRUE(is_valid_vertex_colouring(G, 3, colouring));
}

TEST(EncodingDecodeTest, VertexColouringMultipleColours) {
    Number n0(0);
    std::map<Number, CnfVarList> vars = {{n0, {0, 1}}};
    VertexColouringCnfEncoding encoding{CNF::unsatisfiable(), vars, 2};
    EXPECT_THROW(encoding.decode_model({true, true}), std::runtime_error);
}

TEST(EncodingDecodeTest, VertexColouringMissingColour) {
    Number n0(0);
    std::map<Number, CnfVarList> vars = {{n0, {0, 1}}};
    VertexColouringCnfEncoding encoding{CNF::unsatisfiable(), vars, 2};
    EXPECT_THROW(encoding.decode_model({false, false}), std::runtime_error);
}

TEST(EncodingDecodeTest, EdgeColouringShortModel) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto encoding = build_edge_colouring_cnf_encoding(G, 3);
    std::vector<bool> short_model(1, true);
    EXPECT_THROW(encoding.decode_model(short_model), std::runtime_error);
}

TEST(EncodingDecodeTest, ColouringCnfOptionsNegativeThreshold) {
    ColouringCnfOptions opts;
    opts.vertex_colour_sinz_threshold = -1;
    EXPECT_THROW(opts.validate("test"), std::invalid_argument);
}

TEST(EncodingDecodeTest, EdgeColouringPrecolouredColourTooLarge) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto E = G[Number(0)].find(Location(0, 1));
    ASSERT_NE(E, G[Number(0)].end());
    std::map<Edge, int> pre;
    pre[E->e()] = 5;
    EXPECT_THROW(build_edge_colouring_cnf_encoding(G, 3, pre), std::invalid_argument);
}

TEST(EncodingDecodeTest, EdgeColouringPrecolouredEdgeNotFound) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    Graph Other(create_empty_graph(2));
    addE(Other, Location(0, 1));
    auto E = Other[Number(0)].find(Location(0, 1));
    ASSERT_NE(E, Other[Number(0)].end());
    std::map<Edge, int> pre;
    pre[E->e()] = 0;
    EXPECT_THROW(build_edge_colouring_cnf_encoding(G, 3, pre), std::invalid_argument);
}

TEST(EncodingDecodeTest, HColouringCnfEncodingShortModelThrows) {
    Graph G(create_circuit(4));
    Graph H(create_circuit(3));
    auto encoding = build_hcolouring_cnf_encoding(G, H, false);
    EXPECT_THROW(encoding.decode_model({true, false}), std::runtime_error);
}

TEST(EncodingDecodeTest, HColouringCnfEncodingMultipleColoursThrows) {
    Graph G(create_circuit(4));
    Graph H(create_circuit(3));
    auto encoding = build_hcolouring_cnf_encoding(G, H, false);
    std::vector<bool> bad_model(static_cast<std::size_t>(encoding.cnf.num_vars()), false);
    auto edgesG = internal_hcolouring::edges(G);
    auto edgesH = internal_hcolouring::edges(H);
    if (!edgesG.empty() && edgesH.size() >= 2) {
        bad_model[static_cast<std::size_t>(encoding.variables.get_x_var(edgesG[0], edgesH[0]))] =
            true;
        bad_model[static_cast<std::size_t>(encoding.variables.get_x_var(edgesG[0], edgesH[1]))] =
            true;
        EXPECT_THROW(encoding.decode_model(bad_model), std::runtime_error);
    }
}

TEST(EncodingDecodeTest, HColouringCnfEncodingMissingColourThrows) {
    Graph G(create_circuit(4));
    Graph H(create_circuit(3));
    auto encoding = build_hcolouring_cnf_encoding(G, H, false);
    std::vector<bool> bad_model(static_cast<std::size_t>(encoding.cnf.num_vars()), false);
    EXPECT_THROW(encoding.decode_model(bad_model), std::runtime_error);
}

TEST(EncodingDecodeTest, HColouringRejectsLoops) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 0));
    Graph H(create_circuit(3));
    EXPECT_THROW(build_hcolouring_cnf_encoding(G, H, false), std::invalid_argument);

    Graph G2(create_circuit(3));
    Graph H2(create_empty_graph(2));
    addE(H2, Location(0, 0));
    EXPECT_THROW(build_hcolouring_cnf_encoding(G2, H2, false), std::invalid_argument);
}

TEST(EncodingDecodeTest, HColouringSupportsParallelEdges) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1, 0));
    addE(G, Location(0, 1, 1));

    Graph H(create_empty_graph(2));
    addE(H, Location(0, 1, 0));
    addE(H, Location(0, 1, 1));

    auto encoding = build_hcolouring_cnf_encoding(G, H, false);
    EXPECT_GT(encoding.cnf.num_vars(), 0);
}

TEST(EncodingDecodeTest, CircularVertexCnfEncodingShortModelThrows) {
    Graph G(create_circuit(4));
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, 5, 2);
    EXPECT_THROW(encoding.decode_model({true, false}), std::runtime_error);
}

TEST(EncodingDecodeTest, CircularVertexCnfEncodingMultipleColoursThrows) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, 5, 2);
    std::vector<bool> bad_model(static_cast<std::size_t>(encoding.cnf.num_vars()), false);
    auto it = encoding.vertex_colour_vars.begin();
    if (it != encoding.vertex_colour_vars.end() && encoding.encoded_p >= 2) {
        auto &vars = it->second;
        bad_model[static_cast<std::size_t>(vars[0])] = true;
        bad_model[static_cast<std::size_t>(vars[1])] = true;
        EXPECT_THROW(encoding.decode_model(bad_model), std::runtime_error);
    }
}

TEST(EncodingDecodeTest, CircularVertexCnfEncodingMissingColourThrows) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, 5, 2);
    std::vector<bool> bad_model(static_cast<std::size_t>(encoding.cnf.num_vars()), false);
    EXPECT_THROW(encoding.decode_model(bad_model), std::runtime_error);
}

TEST(EncodingDecodeTest, CircularEdgeCnfEncodingShortModelThrows) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto encoding = build_circular_edge_colouring_cnf_encoding(G, 5, 2);
    EXPECT_THROW(encoding.decode_model({true, false}), std::runtime_error);
}

TEST(EncodingDecodeTest, CircuitEdgeNotFoundInEncoding) {
    std::unordered_map<Number, CnfVarList> vars_map;
    Number n0(0), n1(1);
    vars_map[n0] = {0, 1};
    vars_map[n1] = {2, 3};
    CircuitCnfEncoding encoding{
        CNF::unsatisfiable(), vars_map, 2, std::map<std::pair<Number, Number>, Location>{}
    };
    EXPECT_THROW(encoding.decode_model({true, false, false, true}), std::runtime_error);
}

TEST(EncodingDecodeTest, CircuitCnfEncodingShortModelThrows) {
    Graph G(create_circuit(4));
    auto encoding = build_circuit_cnf_encoding(G, 4);
    EXPECT_THROW(encoding.decode_model({true, false}), std::runtime_error);
}

TEST(EncodingDecodeTest, CircuitCnfEncodingDuplicatePositionThrows) {
    Number n0(0), n1(1), n2(2);
    std::unordered_map<Number, CnfVarList> vars;
    vars[n0] = {0, 1, 2, 3};
    vars[n1] = {4, 5, 6, 7};
    vars[n2] = {8, 9, 10, 11};
    std::map<std::pair<Number, Number>, Location> edge_map;
    edge_map[{n0, n1}] = Location(0, 1);
    edge_map[{n1, n2}] = Location(1, 2);
    edge_map[{n2, n0}] = Location(2, 0);
    edge_map[{n2, n1}] = Location(2, 1);
    CircuitCnfEncoding encoding{CNF(12, {}), vars, 3, edge_map};
    std::vector<bool> model(12, false);
    model[0] = true;
    model[4] = true;
    model[1] = true;
    EXPECT_THROW(encoding.decode_model(model), std::runtime_error);
}

TEST(EncodingDecodeTest, CircuitCnfEncodingMissingPositionThrows) {
    Number n0(0), n1(1), n2(2);
    std::unordered_map<Number, CnfVarList> vars;
    vars[n0] = {0, 1, 2, 3};
    vars[n1] = {4, 5, 6, 7};
    vars[n2] = {8, 9, 10, 11};
    std::map<std::pair<Number, Number>, Location> edge_map;
    edge_map[{n0, n1}] = Location(0, 1);
    CircuitCnfEncoding encoding{CNF(12, {}), vars, 3, edge_map};
    std::vector<bool> model(12, false);
    model[0] = true;
    model[5] = true;
    EXPECT_THROW(encoding.decode_model(model), std::runtime_error);
}

TEST(EncodingDecodeTest, CircuitCnfEncodingRepeatedVertexThrows) {
    Number n0(0), n1(1), n2(2);
    std::unordered_map<Number, CnfVarList> vars;
    vars[n0] = {0, 1, 2};
    vars[n1] = {3, 4, 5};
    vars[n2] = {6, 7, 8};
    std::map<std::pair<Number, Number>, Location> edge_map;
    edge_map[{n0, n0}] = Location(0, 0);
    edge_map[{n0, n1}] = Location(0, 1);
    edge_map[{n1, n0}] = Location(1, 0);
    CircuitCnfEncoding encoding{CNF(9, {}), vars, 3, edge_map};
    std::vector<bool> model(9, false);
    model[0] = true;
    model[1] = true;
    model[5] = true;
    EXPECT_THROW(encoding.decode_model(model), std::runtime_error);
}

#if !BA_GRAPH_HAS_KISSAT_SUPPORT
class OrdinaryColouringFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(OrdinaryColouringFastTest, Skipped) {}

#else

namespace {

Graph path_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i + 1 < n; ++i) {
        addE(G, Location(i, i + 1));
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

Graph single_edge_graph() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    return G;
}

Graph two_incident_edges_graph() {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    return G;
}

Graph loop_graph() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 0));
    return G;
}

Graph disconnected_triangles() {
    Graph G(create_empty_graph(6));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(0, 2));
    addE(G, Location(3, 4));
    addE(G, Location(4, 5));
    addE(G, Location(3, 5));
    return G;
}

Graph k5_minus_one_edge() {
    Graph G(create_empty_graph(5));
    for (int i = 0; i < 5; ++i) {
        for (int j = i + 1; j < 5; ++j) {
            if (!(i == 0 && j == 1)) {
                addE(G, Location(i, j));
            }
        }
    }
    return G;
}

Edge edge_between(const Graph &G, int u, int v) { return G[u].find(Location(u, v))->e(); }

}  // namespace

class OrdinaryColouringFastTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(OrdinaryColouringFastTest, VertexCnfNegativeKThrowsForBothOverloads) {
    Graph G(single_edge_graph());
    std::map<Vertex, int> pre;
    pre[G[0].v()] = 0;
    EXPECT_THROW(
        cnf_vertex_colouring(G, -1, ColouringCnfOptions{.break_symmetry_by_precolouring = false}),
        std::invalid_argument
    );
    EXPECT_THROW(cnf_vertex_colouring(G, -2), std::invalid_argument);
    EXPECT_THROW(cnf_vertex_colouring(G, -1, pre), std::invalid_argument);
    EXPECT_THROW(cnf_vertex_colouring(G, -3, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexCnfZeroColoursAcceptsEmptyGraphTwice) {
    Graph empty(create_empty_graph(0));
    EXPECT_TRUE(solver
                    .solve(cnf_vertex_colouring(
                        empty, 0, ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(empty, 0, std::map<Vertex, int>{})).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfZeroColoursRejectsNonemptyGraphs) {
    EXPECT_FALSE(solver
                     .solve(cnf_vertex_colouring(
                         create_empty_graph(1), 0,
                         ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(single_edge_graph(), 0, std::map<Vertex, int>{}))
                     .has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfLoopRejectedForBothOverloads) {
    Graph loop(loop_graph());
    std::map<Vertex, int> pre;
    pre[loop[0].v()] = 0;
    EXPECT_FALSE(solver
                     .solve(cnf_vertex_colouring(
                         loop, 2, ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(loop, 3, pre)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPrecolouringRejectsTooLargeColours) {
    Graph edge(single_edge_graph());
    std::map<Vertex, int> pre;
    pre[edge[0].v()] = 2;
    EXPECT_THROW(cnf_vertex_colouring(edge, 2, pre), std::invalid_argument);
    pre[edge[0].v()] = 4;
    EXPECT_THROW(cnf_vertex_colouring(edge, 4, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPrecolouringRejectsNegativeColoursBelowSentinel) {
    Graph edge(single_edge_graph());
    std::map<Vertex, int> pre;
    pre[edge[0].v()] = -2;
    EXPECT_THROW(cnf_vertex_colouring(edge, 2, pre), std::invalid_argument);
    pre[edge[0].v()] = -5;
    EXPECT_THROW(cnf_vertex_colouring(edge, 3, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPrecolouringRejectsMinusOneColours) {
    Graph edge(single_edge_graph());
    Graph isolated(create_empty_graph(1));
    std::map<Vertex, int> edge_pre;
    edge_pre[edge[0].v()] = -1;
    std::map<Vertex, int> isolated_pre;
    isolated_pre[isolated[0].v()] = -1;
    EXPECT_THROW(cnf_vertex_colouring(edge, 2, edge_pre), std::invalid_argument);
    EXPECT_THROW(cnf_vertex_colouring(isolated, 1, isolated_pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPrecolouringRejectsAdjacentEqualColours) {
    Graph edge(single_edge_graph());
    Graph path(path_graph(3));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 0;
    std::map<Vertex, int> pre2;
    pre2[path[0].v()] = 1;
    pre2[path[1].v()] = 1;
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(edge, 2, pre1)).has_value());
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(path, 3, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPrecolouringAcceptsAdjacentDifferentColours) {
    Graph edge(single_edge_graph());
    Graph triangle(create_complete_graph(3));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 1;
    std::map<Vertex, int> pre2;
    pre2[triangle[0].v()] = 0;
    pre2[triangle[1].v()] = 1;
    pre2[triangle[2].v()] = 2;
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(edge, 2, pre1)).has_value());
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(triangle, 3, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPartialPrecolouringCanForceUnsat) {
    Graph triangle(create_complete_graph(3));
    Graph c5(create_circuit(5));
    std::map<Vertex, int> pre1;
    pre1[triangle[0].v()] = 0;
    std::map<Vertex, int> pre2;
    pre2[c5[0].v()] = 0;
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(triangle, 2, pre1)).has_value());
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(c5, 2, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfPartialPrecolouringCanRemainSat) {
    Graph path(path_graph(4));
    Graph c4(create_circuit(4));
    std::map<Vertex, int> pre1;
    pre1[path[0].v()] = 0;
    std::map<Vertex, int> pre2;
    pre2[c4[0].v()] = 0;
    pre2[c4[1].v()] = 1;
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(path, 2, pre1)).has_value());
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(c4, 2, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfSymmetryBreakingNoEdgeBranch) {
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(create_empty_graph(0), 0)).has_value());
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(create_empty_graph(3), 1)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfSymmetryBreakingEdgeBranchRejectsOneColour) {
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(single_edge_graph(), 1)).has_value());
    EXPECT_FALSE(solver.solve(cnf_vertex_colouring(path_graph(3), 1)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexCnfSymmetryBreakingEdgeBranchAcceptsEnoughColours) {
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(single_edge_graph(), 2)).has_value());
    EXPECT_TRUE(solver.solve(cnf_vertex_colouring(create_circuit(5), 3)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfNegativeKThrowsForBothOverloads) {
    Graph G(single_edge_graph());
    std::map<Edge, int> pre;
    pre[edge_between(G, 0, 1)] = 0;
    EXPECT_THROW(
        cnf_edge_colouring(G, -1, ColouringCnfOptions{.break_symmetry_by_precolouring = false}),
        std::invalid_argument
    );
    EXPECT_THROW(cnf_edge_colouring(G, -2), std::invalid_argument);
    EXPECT_THROW(cnf_edge_colouring(G, -1, pre), std::invalid_argument);
    EXPECT_THROW(cnf_edge_colouring(G, -3, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfZeroColoursAcceptsGraphsWithoutEdges) {
    EXPECT_TRUE(solver
                    .solve(cnf_edge_colouring(
                        create_empty_graph(0), 0,
                        ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(create_empty_graph(4), 0, std::map<Edge, int>{}))
                    .has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfZeroColoursRejectsGraphsWithEdges) {
    EXPECT_FALSE(solver
                     .solve(cnf_edge_colouring(
                         single_edge_graph(), 0,
                         ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(
        solver.solve(cnf_edge_colouring(path_graph(3), 0, std::map<Edge, int>{})).has_value()
    );
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfLoopRejectedForBothOverloads) {
    Graph loop(loop_graph());
    std::map<Edge, int> pre;
    pre[edge_between(loop, 0, 1)] = 0;
    EXPECT_FALSE(solver
                     .solve(cnf_edge_colouring(
                         loop, 2, ColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver.solve(cnf_edge_colouring(loop, 3, pre)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringRejectsNegativeColours) {
    Graph edge(single_edge_graph());
    std::map<Edge, int> pre;
    pre[edge_between(edge, 0, 1)] = -1;
    EXPECT_THROW(cnf_edge_colouring(edge, 2, pre), std::invalid_argument);
    pre[edge_between(edge, 0, 1)] = -3;
    EXPECT_THROW(cnf_edge_colouring(edge, 3, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringRejectsTooLargeColours) {
    Graph edge(single_edge_graph());
    Graph path(path_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = 2;
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 0, 1)] = 3;
    EXPECT_THROW(cnf_edge_colouring(edge, 2, pre1), std::invalid_argument);
    EXPECT_THROW(cnf_edge_colouring(path, 3, pre2), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringAcceptsValidColours) {
    Graph edge(single_edge_graph());
    Graph path(path_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = 1;
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 0, 1)] = 0;
    pre2[edge_between(path, 1, 2)] = 1;
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(edge, 2, pre1)).has_value());
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(path, 2, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringRejectsIncidentEqualColours) {
    Graph path(path_graph(3));
    Graph star(star_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 0;
    std::map<Edge, int> pre2;
    pre2[edge_between(star, 0, 1)] = 1;
    pre2[edge_between(star, 0, 2)] = 1;
    EXPECT_FALSE(solver.solve(cnf_edge_colouring(path, 2, pre1)).has_value());
    EXPECT_FALSE(solver.solve(cnf_edge_colouring(star, 3, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringAcceptsNonincidentEqualColours) {
    Graph path(path_graph(4));
    Graph matching(create_empty_graph(4));
    addE(matching, Location(0, 1));
    addE(matching, Location(2, 3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 2, 3)] = 0;
    std::map<Edge, int> pre2;
    pre2[edge_between(matching, 0, 1)] = 0;
    pre2[edge_between(matching, 2, 3)] = 0;
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(path, 2, pre1)).has_value());
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(matching, 1, pre2)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfPrecolouringRejectsColourCountBelowMaxDegree) {
    EXPECT_FALSE(
        solver.solve(cnf_edge_colouring(star_graph(3), 2, std::map<Edge, int>{})).has_value()
    );
    EXPECT_FALSE(
        solver.solve(cnf_edge_colouring(star_graph(4), 3, std::map<Edge, int>{})).has_value()
    );
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfBooleanSymmetryRejectsColourCountBelowMaxDegree) {
    EXPECT_FALSE(solver.solve(cnf_edge_colouring(star_graph(3), 2)).has_value());
    EXPECT_FALSE(solver.solve(cnf_edge_colouring(star_graph(4), 3)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfBooleanSymmetryHandlesGraphsWithoutEdges) {
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(create_empty_graph(0), 0)).has_value());
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(create_empty_graph(5), 0)).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfBooleanSymmetryAcceptsEnoughColours) {
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(star_graph(3), 3)).has_value());
    EXPECT_TRUE(solver.solve(cnf_edge_colouring(create_complete_graph(4), 3)).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionRejectsNegativeKForBothOverloads) {
    Graph edge(single_edge_graph());
    std::map<Vertex, int> pre;
    pre[edge[0].v()] = 0;
    EXPECT_THROW(is_colourable_sat(solver, edge, -1), std::invalid_argument);
    EXPECT_THROW(is_colourable_sat(solver, edge, -2, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionRejectsLoopsForBothOverloads) {
    Graph loop(loop_graph());
    std::map<Vertex, int> pre;
    pre[loop[0].v()] = 0;
    EXPECT_FALSE(is_colourable_sat(solver, loop, 2));
    EXPECT_FALSE(is_colourable_sat(solver, loop, 3, pre));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionHandlesEmptyAndIsolatedGraphs) {
    EXPECT_TRUE(is_colourable_sat(solver, create_empty_graph(0), 0));
    EXPECT_TRUE(is_colourable_sat(solver, create_empty_graph(4), 1));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionRejectsZeroColoursOnNonemptyGraphs) {
    EXPECT_FALSE(is_colourable_sat(solver, create_empty_graph(2), 0));
    EXPECT_FALSE(is_colourable_sat(solver, single_edge_graph(), 0));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionHandlesSingleEdgeAndPath) {
    EXPECT_FALSE(is_colourable_sat(solver, single_edge_graph(), 1));
    EXPECT_TRUE(is_colourable_sat(solver, path_graph(4), 2));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionHandlesTriangleAndOddCycle) {
    EXPECT_FALSE(is_colourable_sat(solver, create_complete_graph(3), 2));
    EXPECT_TRUE(is_colourable_sat(solver, create_circuit(5), 3));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionHandlesEvenCycles) {
    EXPECT_TRUE(is_colourable_sat(solver, create_circuit(4), 2));
    EXPECT_TRUE(is_colourable_sat(solver, create_circuit(6), 2));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionWithPrecolouringCanForceFalse) {
    Graph edge(single_edge_graph());
    Graph path(path_graph(3));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 0;
    std::map<Vertex, int> pre2;
    pre2[path[0].v()] = 0;
    pre2[path[1].v()] = 0;
    EXPECT_FALSE(is_colourable_sat(solver, edge, 2, pre1));
    EXPECT_FALSE(is_colourable_sat(solver, path, 3, pre2));
}

TEST_F(OrdinaryColouringFastTest, VertexDecisionWithPrecolouringCanRemainTrue) {
    Graph edge(single_edge_graph());
    Graph path(path_graph(3));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 1;
    std::map<Vertex, int> pre2;
    pre2[path[0].v()] = 0;
    pre2[path[1].v()] = 1;
    EXPECT_TRUE(is_colourable_sat(solver, edge, 2, pre1));
    EXPECT_TRUE(is_colourable_sat(solver, path, 2, pre2));
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveRejectsNegativeKForBothOverloads) {
    Graph edge(single_edge_graph());
    std::map<Vertex, int> pre;
    pre[edge[0].v()] = 0;
    EXPECT_THROW(is_colourable_sat_constructive(solver, edge, -1), std::invalid_argument);
    EXPECT_THROW(is_colourable_sat_constructive(solver, edge, -2, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveReturnsNulloptForLoopsForBothOverloads) {
    Graph loop(loop_graph());
    std::map<Vertex, int> pre;
    pre[loop[0].v()] = 0;
    EXPECT_FALSE(is_colourable_sat_constructive(solver, loop, 2).has_value());
    EXPECT_FALSE(is_colourable_sat_constructive(solver, loop, 3, pre).has_value());
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveReturnsEmptyWitnessForEmptyGraph) {
    auto w0 = is_colourable_sat_constructive(solver, create_empty_graph(0), 0);
    auto w1 = is_colourable_sat_constructive(solver, create_empty_graph(0), 1);
    ASSERT_TRUE(w0.has_value());
    ASSERT_TRUE(w1.has_value());
    EXPECT_TRUE(w0->empty());
    EXPECT_TRUE(w1->empty());
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveReturnsValidWitnessForBipartiteGraphs) {
    Graph edge(single_edge_graph());
    Graph c4(create_circuit(4));
    auto w1 = is_colourable_sat_constructive(solver, edge, 2);
    auto w2 = is_colourable_sat_constructive(solver, c4, 2);
    ASSERT_TRUE(w1.has_value());
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_vertex_colouring(edge, *w1, 2));
    EXPECT_TRUE(sat_test_validation::is_valid_vertex_colouring(c4, *w2, 2));
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveReturnsValidWitnessForThreeColourableGraphs) {
    Graph triangle(create_complete_graph(3));
    Graph c5(create_circuit(5));
    auto w1 = is_colourable_sat_constructive(solver, triangle, 3);
    auto w2 = is_colourable_sat_constructive(solver, c5, 3);
    ASSERT_TRUE(w1.has_value());
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_vertex_colouring(triangle, *w1, 3));
    EXPECT_TRUE(sat_test_validation::is_valid_vertex_colouring(c5, *w2, 3));
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveReturnsNulloptForUnsatCases) {
    EXPECT_FALSE(is_colourable_sat_constructive(solver, single_edge_graph(), 1).has_value());
    EXPECT_FALSE(is_colourable_sat_constructive(solver, create_circuit(5), 2).has_value());
}

TEST_F(OrdinaryColouringFastTest, PrecolouringDomainMismatch) {
    Graph G = create_circuit(3);
    std::map<Vertex, int> precol;
    precol[Vertex()] = 1;
    EXPECT_THROW(cnf_vertex_colouring(G, 3, precol), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveWithPrecolouringRespectsFixedColours) {
    Graph path(path_graph(4));
    Graph triangle(create_complete_graph(3));
    std::map<Vertex, int> pre1;
    pre1[path[0].v()] = 0;
    pre1[path[1].v()] = 1;
    auto w1 = is_colourable_sat_constructive(solver, path, 2, pre1);
    ASSERT_TRUE(w1.has_value());
    EXPECT_TRUE(sat_test_validation::respects_vertex_precolouring(path, *w1, pre1));
    std::map<Vertex, int> pre2;
    pre2[triangle[0].v()] = 0;
    pre2[triangle[1].v()] = 1;
    auto w2 = is_colourable_sat_constructive(solver, triangle, 3, pre2);
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::respects_vertex_precolouring(triangle, *w2, pre2));
}

TEST_F(OrdinaryColouringFastTest, VertexConstructiveWithPrecolouringReturnsNulloptForConflicts) {
    Graph edge(single_edge_graph());
    Graph triangle(create_complete_graph(3));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 0;
    std::map<Vertex, int> pre2;
    pre2[triangle[0].v()] = 0;
    pre2[triangle[1].v()] = 0;
    EXPECT_FALSE(is_colourable_sat_constructive(solver, edge, 2, pre1).has_value());
    EXPECT_FALSE(is_colourable_sat_constructive(solver, triangle, 3, pre2).has_value());
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberHandlesSpecialCases) {
    EXPECT_EQ(chromatic_number_sat(solver, create_empty_graph(0)), 0);
    EXPECT_EQ(chromatic_number_sat(solver, create_empty_graph(5)), 1);
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberHandlesSmallStandardGraphs) {
    EXPECT_EQ(chromatic_number_sat(solver, single_edge_graph()), 2);
    EXPECT_EQ(chromatic_number_sat(solver, create_circuit(5)), 3);
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberHandlesCompleteGraphs) {
    EXPECT_EQ(chromatic_number_sat(solver, create_complete_graph(3)), 3);
    EXPECT_EQ(chromatic_number_sat(solver, create_complete_graph(4)), 4);
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberHandlesDisconnectedGraphs) {
    Graph c5_plus_isolated(create_empty_graph(6));
    for (int i = 0; i < 5; ++i) {
        addE(c5_plus_isolated, Location(i, (i + 1) % 5));
    }
    EXPECT_EQ(chromatic_number_sat(solver, disconnected_triangles()), 3);
    EXPECT_EQ(chromatic_number_sat(solver, c5_plus_isolated), 3);
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberRejectsGraphsWithLoops) {
    Graph loop1(loop_graph());
    Graph loop2(create_empty_graph(1));
    addE(loop2, Location(0, 0));
    EXPECT_EQ(chromatic_number_sat(solver, loop1), UNCOLOURABLE);
    EXPECT_EQ(chromatic_number_sat(solver, loop2), UNCOLOURABLE);
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionRejectsNegativeKForBothOverloads) {
    Graph edge(single_edge_graph());
    std::map<Edge, int> pre;
    pre[edge_between(edge, 0, 1)] = 0;
    EXPECT_THROW(is_edge_colourable_sat(solver, edge, -1), std::invalid_argument);
    EXPECT_THROW(is_edge_colourable_sat(solver, edge, -2, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionRejectsColourCountBelowMaxDegree) {
    EXPECT_FALSE(is_edge_colourable_sat(solver, star_graph(3), 2));
    EXPECT_FALSE(is_edge_colourable_sat(solver, star_graph(4), 3));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionHandlesLoopsAsFalse) {
    Graph loop(loop_graph());
    std::map<Edge, int> pre;
    pre[edge_between(loop, 0, 1)] = 0;
    EXPECT_FALSE(is_edge_colourable_sat(solver, loop, 3));
    EXPECT_FALSE(is_edge_colourable_sat(solver, loop, 3, pre));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionHandlesGraphsWithoutEdges) {
    EXPECT_TRUE(is_edge_colourable_sat(solver, create_empty_graph(0), 0));
    EXPECT_TRUE(is_edge_colourable_sat(solver, create_empty_graph(4), 0));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionHandlesSingleEdgeAndPath) {
    EXPECT_FALSE(is_edge_colourable_sat(solver, single_edge_graph(), 0));
    EXPECT_TRUE(is_edge_colourable_sat(solver, two_incident_edges_graph(), 2));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionHandlesCycles) {
    EXPECT_TRUE(is_edge_colourable_sat(solver, create_circuit(4), 2));
    EXPECT_FALSE(is_edge_colourable_sat(solver, create_circuit(5), 2));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionHandlesCompleteGraphs) {
    EXPECT_TRUE(is_edge_colourable_sat(solver, create_complete_graph(4), 3));
    EXPECT_TRUE(is_edge_colourable_sat(solver, create_complete_graph(5), 5));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionWithPrecolouringCanForceFalse) {
    Graph path(two_incident_edges_graph());
    Graph star(star_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 0;
    std::map<Edge, int> pre2;
    pre2[edge_between(star, 0, 1)] = 1;
    pre2[edge_between(star, 0, 2)] = 1;
    EXPECT_FALSE(is_edge_colourable_sat(solver, path, 2, pre1));
    EXPECT_FALSE(is_edge_colourable_sat(solver, star, 3, pre2));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionWithPrecolouringCanRemainTrue) {
    Graph path(two_incident_edges_graph());
    Graph star(star_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 1;
    std::map<Edge, int> pre2;
    pre2[edge_between(star, 0, 1)] = 0;
    pre2[edge_between(star, 0, 2)] = 1;
    pre2[edge_between(star, 0, 3)] = 2;
    EXPECT_TRUE(is_edge_colourable_sat(solver, path, 2, pre1));
    EXPECT_TRUE(is_edge_colourable_sat(solver, star, 3, pre2));
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveRejectsNegativeKForBothOverloads) {
    Graph edge(single_edge_graph());
    std::map<Edge, int> pre;
    pre[edge_between(edge, 0, 1)] = 0;
    EXPECT_THROW(is_edge_colourable_sat_constructive(solver, edge, -1), std::invalid_argument);
    EXPECT_THROW(is_edge_colourable_sat_constructive(solver, edge, -2, pre), std::invalid_argument);
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsNulloptForColourCountBelowMaxDegree) {
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, star_graph(3), 2).has_value());
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, star_graph(4), 3).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsNulloptForLoops) {
    Graph loop(loop_graph());
    std::map<Edge, int> pre;
    pre[edge_between(loop, 0, 1)] = 0;
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, loop, 3).has_value());
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, loop, 3, pre).has_value());
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsEmptyWitnessForGraphsWithoutEdges) {
    auto w0 = is_edge_colourable_sat_constructive(solver, create_empty_graph(0), 0);
    auto w1 = is_edge_colourable_sat_constructive(solver, create_empty_graph(3), 0);
    ASSERT_TRUE(w0.has_value());
    ASSERT_TRUE(w1.has_value());
    EXPECT_TRUE(w0->empty());
    EXPECT_TRUE(w1->empty());
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsValidWitnessForSmallGraphs) {
    Graph edge(single_edge_graph());
    Graph path(two_incident_edges_graph());
    auto w1 = is_edge_colourable_sat_constructive(solver, edge, 1);
    auto w2 = is_edge_colourable_sat_constructive(solver, path, 2);
    ASSERT_TRUE(w1.has_value());
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(edge, *w1, 1));
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(path, *w2, 2));
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsValidWitnessForCompleteAndOddCycleGraphs) {
    Graph k4(create_complete_graph(4));
    Graph c5(create_circuit(5));
    auto w1 = is_edge_colourable_sat_constructive(solver, k4, 3);
    auto w2 = is_edge_colourable_sat_constructive(solver, c5, 3);
    ASSERT_TRUE(w1.has_value());
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(k4, *w1, 3));
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(c5, *w2, 3));
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveReturnsNulloptForUnsatCases) {
    EXPECT_FALSE(
        is_edge_colourable_sat_constructive(solver, two_incident_edges_graph(), 1).has_value()
    );
    EXPECT_FALSE(
        is_edge_colourable_sat_constructive(solver, create_complete_graph(4), 2).has_value()
    );
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveWithPrecolouringRespectsFixedColours) {
    Graph path(two_incident_edges_graph());
    Graph k4(create_complete_graph(4));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 1;
    auto w1 = is_edge_colourable_sat_constructive(solver, path, 2, pre1);
    ASSERT_TRUE(w1.has_value());
    EXPECT_TRUE(sat_test_validation::respects_edge_precolouring(path, *w1, pre1));
    std::map<Edge, int> pre2;
    pre2[edge_between(k4, 0, 1)] = 0;
    pre2[edge_between(k4, 0, 2)] = 1;
    auto w2 = is_edge_colourable_sat_constructive(solver, k4, 3, pre2);
    ASSERT_TRUE(w2.has_value());
    EXPECT_TRUE(sat_test_validation::respects_edge_precolouring(k4, *w2, pre2));
}

TEST_F(OrdinaryColouringFastTest, EdgeConstructiveWithPrecolouringReturnsNulloptForConflicts) {
    Graph path(two_incident_edges_graph());
    Graph k4(create_complete_graph(4));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 0;
    std::map<Edge, int> pre2;
    pre2[edge_between(k4, 0, 1)] = 2;
    pre2[edge_between(k4, 0, 2)] = 2;
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, path, 2, pre1).has_value());
    EXPECT_FALSE(is_edge_colourable_sat_constructive(solver, k4, 3, pre2).has_value());
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexHandlesSpecialCases) {
    EXPECT_EQ(chromatic_index_sat(solver, create_empty_graph(0)), 0);
    EXPECT_EQ(chromatic_index_sat(solver, create_empty_graph(5)), 0);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexHandlesPathsAndStars) {
    EXPECT_EQ(chromatic_index_sat(solver, path_graph(4)), 2);
    EXPECT_EQ(chromatic_index_sat(solver, star_graph(4)), 4);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexHandlesCycles) {
    EXPECT_EQ(chromatic_index_sat(solver, create_circuit(4)), 2);
    EXPECT_EQ(chromatic_index_sat(solver, create_circuit(5)), 3);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexHandlesCompleteGraphs) {
    EXPECT_EQ(chromatic_index_sat(solver, create_complete_graph(4)), 3);
    EXPECT_EQ(chromatic_index_sat(solver, create_complete_graph(5)), 5);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexHandlesDisconnectedGraphs) {
    Graph matching(create_empty_graph(4));
    addE(matching, Location(0, 1));
    addE(matching, Location(2, 3));
    EXPECT_EQ(chromatic_index_sat(solver, disconnected_triangles()), 3);
    EXPECT_EQ(chromatic_index_sat(solver, matching), 1);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexRejectsGraphsWithLoops) {
    Graph loop1(loop_graph());
    Graph loop2(create_empty_graph(1));
    addE(loop2, Location(0, 0));
    EXPECT_EQ(chromatic_index_sat(solver, loop1), UNCOLOURABLE);
    EXPECT_EQ(chromatic_index_sat(solver, loop2), UNCOLOURABLE);
}

TEST_F(OrdinaryColouringFastTest, LineGraphMappingWorksForSimpleGraphs) {
    auto check = [](const Graph &G) {
        Factory f;
        auto [H, location_to_vertex] = line_graph_with_location_map(G, f);
        EXPECT_EQ(H.order(), G.size());
        EXPECT_EQ(location_to_vertex.size(), static_cast<std::size_t>(G.size()));
    };
    check(create_complete_graph(4));
    check(create_petersen());
}

TEST_F(OrdinaryColouringFastTest, LineGraphMappingWorksForMultigraphs) {
    Graph multi(create_empty_graph(3));
    addE(multi, Location(0, 1));
    addE(multi, Location(0, 1));
    addE(multi, Location(1, 2));
    Graph parallel(create_empty_graph(2));
    addE(parallel, Location(0, 1));
    addE(parallel, Location(0, 1));
    addE(parallel, Location(0, 1));
    auto check = [](const Graph &G) {
        Factory f;
        auto [H, location_to_vertex] = line_graph_with_location_map(G, f);
        EXPECT_EQ(H.order(), G.size());
        EXPECT_EQ(location_to_vertex.size(), static_cast<std::size_t>(G.size()));
    };
    check(multi);
    check(parallel);
}

TEST_F(OrdinaryColouringFastTest, MultigraphEdgeColouringTwoParallelEdges) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    EXPECT_FALSE(is_edge_colourable_sat(solver, G, 1));
    EXPECT_TRUE(is_edge_colourable_sat(solver, G, 2));
}

TEST_F(OrdinaryColouringFastTest, MultigraphEdgeColouringThreeParallelEdges) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    EXPECT_FALSE(is_edge_colourable_sat(solver, G, 2));
    EXPECT_EQ(chromatic_index_sat(solver, G), 3);
}

TEST_F(OrdinaryColouringFastTest, MultigraphConstructiveWitnessesAreValid) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    auto witness = is_edge_colourable_sat_constructive(solver, G, 3);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, *witness, 3));
}

TEST_F(OrdinaryColouringFastTest, K5MinusOneEdgeHasChromaticIndexFive) {
    Graph G(k5_minus_one_edge());
    EXPECT_FALSE(is_edge_colourable_sat(solver, G, 4));
    EXPECT_EQ(chromatic_index_sat(solver, G), 5);
}

// ======== CVD Heuristics Tests ========

TEST_F(OrdinaryColouringFastTest, EdgeDecisionWithCvdHeuristicsK4) {
    Graph k4(create_complete_graph(4));
    EXPECT_TRUE(is_edge_colourable_sat(solver, k4, 3, true));
}

TEST_F(OrdinaryColouringFastTest, EdgeDecisionWithCvdHeuristicsPetersen) {
    Graph petersen(create_petersen());
    EXPECT_TRUE(is_edge_colourable_sat(solver, petersen, 4, true));
    EXPECT_FALSE(is_edge_colourable_sat(solver, petersen, 3, true));
}

// ======== Vertex Criticality Tests ========

TEST_F(OrdinaryColouringFastTest, KChromaticNumberVertexCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_k_chromatic_number_vertex_critical_sat(solver, G, 3));
}

TEST_F(OrdinaryColouringFastTest, KChromaticNumberVertexCriticalK4) {
    Graph G(create_complete_graph(4));
    EXPECT_TRUE(is_k_chromatic_number_vertex_critical_sat(solver, G, 4));
}

TEST_F(OrdinaryColouringFastTest, KChromaticNumberVertexCriticalNonMatchingK) {
    Graph G(create_complete_graph(3));
    EXPECT_FALSE(is_k_chromatic_number_vertex_critical_sat(solver, G, 2));
    EXPECT_FALSE(is_k_chromatic_number_vertex_critical_sat(solver, G, 4));
}

TEST_F(OrdinaryColouringFastTest, ChromaticNumberVertexCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_chromatic_number_vertex_critical_sat(solver, G));
}

// ======== Edge Criticality (Chromatic Number) Tests ========

TEST_F(OrdinaryColouringFastTest, KChromaticNumberEdgeCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_k_chromatic_number_edge_critical_sat(solver, G, 3));
}

TEST_F(OrdinaryColouringFastTest, KChromaticNumberEdgeCriticalNonMatchingK) {
    Graph G(create_complete_graph(3));
    EXPECT_FALSE(is_k_chromatic_number_edge_critical_sat(solver, G, 2));
    EXPECT_FALSE(is_k_chromatic_number_edge_critical_sat(solver, G, 4));
}

// ======== Edge Criticality (Chromatic Index) Tests ========

TEST_F(OrdinaryColouringFastTest, KChromaticIndexVertexCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_k_chromatic_index_vertex_critical_sat(solver, G, 3));
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexVertexCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_chromatic_index_vertex_critical_sat(solver, G));
}

TEST_F(OrdinaryColouringFastTest, KChromaticIndexEdgeCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_k_chromatic_index_edge_critical_sat(solver, G, 3));
}

TEST_F(OrdinaryColouringFastTest, KChromaticIndexEdgeCriticalNonMatchingK) {
    Graph G(create_complete_graph(3));
    EXPECT_FALSE(is_k_chromatic_index_edge_critical_sat(solver, G, 2));
    EXPECT_FALSE(is_k_chromatic_index_edge_critical_sat(solver, G, 4));
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexEdgeCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_chromatic_index_edge_critical_sat(solver, G));
}

TEST_F(OrdinaryColouringFastTest, KChromaticIndexVertexCriticalC5) {
    // C5 has chromatic index 3 and IS vertex-critical for edge-colouring
    // (deleting any vertex gives a path, which is 2-edge-colourable)
    Graph G(create_circuit(5));
    EXPECT_TRUE(is_k_chromatic_index_vertex_critical_sat(solver, G, 3));
}

// ======== Chromatic Number Edge Critical Tests ========

TEST_F(OrdinaryColouringFastTest, ChromaticNumberEdgeCriticalK3) {
    Graph G(create_complete_graph(3));
    EXPECT_TRUE(is_chromatic_number_edge_critical_sat(solver, G));
}

// ======== Chromatic Number/Index Not Critical Tests ========

TEST_F(OrdinaryColouringFastTest, ChromaticNumberVertexCriticalEdgeCasesThrow) {
    Graph no_edges(create_empty_graph(3));
    EXPECT_THROW(is_chromatic_number_vertex_critical_sat(solver, no_edges), std::invalid_argument);
    Graph loop(loop_graph());
    EXPECT_EQ(chromatic_number_sat(solver, loop), UNCOLOURABLE);
}

TEST_F(OrdinaryColouringFastTest, ChromaticIndexEdgeCriticalEdgeCasesThrow) {
    Graph no_edges(create_empty_graph(3));
    EXPECT_THROW(is_chromatic_index_edge_critical_sat(solver, no_edges), std::invalid_argument);
}

// ======== Parallel edge and loop tests for colouring encodings ========

TEST_F(OrdinaryColouringFastTest, EdgeColouringWithParallelEdges) {
    Graph G(create_empty_graph(3));
    addE(G, Location(0, 1, 0));
    addE(G, Location(0, 1, 1));
    addE(G, Location(1, 2));
    EXPECT_EQ(max_deg(G), 3);
    EXPECT_TRUE(is_edge_colourable_sat(solver, G, 3));
    EXPECT_FALSE(is_edge_colourable_sat(solver, G, 2));
    auto witness = is_edge_colourable_sat_constructive(solver, G, 3);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(is_valid_edge_colouring(G, 3, *witness));
}

TEST_F(OrdinaryColouringFastTest, VertexColouringLoopRejected) {
    Graph G(create_empty_graph(1));
    addE(G, Location(0, 0));
    EXPECT_FALSE(is_colourable_sat(solver, G, 1));
}

TEST_F(OrdinaryColouringFastTest, EdgeColouringLoopRejected) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 0));
    addE(G, Location(0, 1));
    EXPECT_FALSE(is_edge_colourable_sat(solver, G, 3));
}

// ======== Post-mutation decode independence ========

TEST_F(OrdinaryColouringFastTest, VertexColouringDecodeAfterGraphRebuild) {
    Graph G(create_circuit(4));
    auto encoding = build_vertex_colouring_cnf_encoding(G, 3);
    auto model = solver.solve(encoding.cnf);
    ASSERT_TRUE(model.has_value());
    Graph G2(create_circuit(4));
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(is_valid_vertex_colouring(G2, 3, colouring));
}

TEST_F(OrdinaryColouringFastTest, EdgeColouringDecodeAfterGraphRebuild) {
    Graph G(create_circuit(4));
    auto encoding = build_edge_colouring_cnf_encoding(G, 3);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    Graph G2(create_circuit(4));
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(is_valid_edge_colouring(G2, 3, colouring));
}

// ======== Parallel Edge Ordering Symmetry Breaking Tests ========

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryTwoEdgesDirect) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));

    ColouringCnfOptions opts_off{.break_symmetry_by_ordering_parallel_edges = false};
    auto encoding_off = build_edge_colouring_cnf_encoding(G, 2, opts_off);
    auto model_off = solver.solve(encoding_off.line_graph_encoding.cnf);
    ASSERT_TRUE(model_off.has_value());
    auto colouring_off = encoding_off.decode_model(*model_off);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring_off, 2));

    ColouringCnfOptions opts_on{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto encoding_on = build_edge_colouring_cnf_encoding(G, 2, opts_on);
    auto model_on = solver.solve(encoding_on.line_graph_encoding.cnf);
    ASSERT_TRUE(model_on.has_value());
    auto colouring_on = encoding_on.decode_model(*model_on);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring_on, 2));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 2u);
    EXPECT_LE(colouring_on.at(edges[0]), colouring_on.at(edges[1]));
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryTwoEdgesSupport) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));

    ColouringCnfOptions opts{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT
    };
    auto encoding = build_edge_colouring_cnf_encoding(G, 2, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring, 2));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 2u);
    EXPECT_LE(colouring.at(edges[0]), colouring.at(edges[1]));
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryThreeEdgesK2Unsat) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));

    ColouringCnfOptions opts_off{.break_symmetry_by_ordering_parallel_edges = false};
    auto cnf_off = cnf_edge_colouring(G, 2, opts_off);
    EXPECT_FALSE(solver.solve(cnf_off).has_value());

    ColouringCnfOptions opts_on{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto cnf_on = cnf_edge_colouring(G, 2, opts_on);
    EXPECT_FALSE(solver.solve(cnf_on).has_value());
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetrySimpleGraphNoop) {
    Graph G(create_complete_graph(4));

    ColouringCnfOptions opts_off{.break_symmetry_by_ordering_parallel_edges = false};
    auto cnf_off = cnf_edge_colouring(G, 3, opts_off);

    ColouringCnfOptions opts_on{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto cnf_on = cnf_edge_colouring(G, 3, opts_on);

    EXPECT_EQ(
        static_cast<int>(cnf_off.clauses().size()), static_cast<int>(cnf_on.clauses().size())
    );
    EXPECT_TRUE(solver.solve(cnf_off).has_value());
    EXPECT_TRUE(solver.solve(cnf_on).has_value());
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryExecWrapperDefault) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));

    auto witness = is_edge_colourable_sat_constructive(solver, G, 2);
    ASSERT_TRUE(witness.has_value());
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, *witness, 2));
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryWithPrecolouring) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 1));

    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    ASSERT_EQ(primary_edges.size(), 2u);

    std::map<Edge, int> precolouring;
    precolouring[primary_edges[0]] = 0;

    ColouringCnfOptions opts{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto encoding = build_edge_colouring_cnf_encoding(G, 2, precolouring, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring, 2));
    EXPECT_TRUE(sat_test_validation::respects_edge_precolouring(G, colouring, precolouring));
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryReverseOrientation) {
    Factory f;
    Graph G(createG(f));
    addV(G, 0, f);
    addV(G, 1, f);
    addE(G, Location(1, 0), f);
    addE(G, Location(0, 1), f);

    ColouringCnfOptions opts{
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto encoding = build_edge_colouring_cnf_encoding(G, 2, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring, 2));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 2u);
    EXPECT_LE(colouring.at(edges[0]), colouring.at(edges[1]));
}

TEST_F(OrdinaryColouringFastTest, ParallelEdgeSymmetryBothFlags) {
    Factory f;
    Graph G(createG(f));
    addV(G, 0, f);
    addV(G, 1, f);
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(0, 1, 2), f);

    ColouringCnfOptions opts{
        .break_symmetry_by_precolouring = true,
        .break_symmetry_by_ordering_parallel_edges = true,
        .parallel_edge_ordering_encoding = OrderingEncoding::DIRECT
    };
    auto encoding = build_edge_colouring_cnf_encoding(G, 3, opts);
    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(sat_test_validation::is_valid_edge_colouring(G, colouring, 3));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 3u);
    EXPECT_LE(colouring.at(edges[0]), colouring.at(edges[1]));
    EXPECT_LE(colouring.at(edges[1]), colouring.at(edges[2]));
}

TEST_F(OrdinaryColouringFastTest, EdgeCnfNegativeKPrecolouringOverload) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    EXPECT_THROW(
        cnf_edge_colouring(G, -1, std::map<Edge, int>{}, ColouringCnfOptions{}),
        std::invalid_argument
    );
}

TEST(ColouringCnfOptionsTest, InvalidOrderingEncodingThrows) {
    {
        ColouringCnfOptions opts{.break_symmetry_by_ordering_parallel_edges = false};
        opts.parallel_edge_ordering_encoding = static_cast<OrderingEncoding>(999);
        EXPECT_THROW(opts.validate(static_cast<std::string>("test")), std::invalid_argument);
    }
    {
        ColouringCnfOptions opts{.break_symmetry_by_ordering_parallel_edges = true};
        opts.parallel_edge_ordering_encoding = static_cast<OrderingEncoding>(-1);
        EXPECT_THROW(opts.validate(static_cast<std::string>("test")), std::invalid_argument);
    }
}

#endif  // BA_GRAPH_HAS_KISSAT_SUPPORT
