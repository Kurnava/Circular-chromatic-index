// clang-format off
#include "implementation.h"

#include <map>
#include <stdexcept>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/exec_solver.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT
class CircularColouringWithoutTightCyclesFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularColouringWithoutTightCyclesFastTest, Skipped) {}

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

Graph complete_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            addE(G, Location(i, j));
        }
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

Graph loop_graph() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 0));
    return G;
}

Graph triangle_plus_path() {
    Graph G(create_empty_graph(6));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 0));
    addE(G, Location(3, 4));
    addE(G, Location(4, 5));
    return G;
}

Graph square_plus_path() {
    Graph G(create_empty_graph(7));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 3));
    addE(G, Location(3, 0));
    addE(G, Location(4, 5));
    addE(G, Location(5, 6));
    return G;
}

Edge edge_between(const Graph &G, int u, int v) { return G[u].find(Location(u, v))->e(); }

}  // namespace

class CircularColouringWithoutTightCyclesFastTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexBoolRejectsNegativePInTwoSmallGraphs) {
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(
            path_graph(2), -1, 1,
            CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, cycle_graph(3), -2, 1),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexBoolRejectsNonPositiveQInTwoSmallGraphs) {
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(
            path_graph(2), 3, 0,
            CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 4, -1),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringRejectsNegativePInTwoSmallGraphs
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    Graph triangle(cycle_graph(3));
    std::map<Vertex, int> pre2;
    pre2[triangle[1].v()] = 1;
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(edge, -1, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, -2, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexPrecolouringRejectsNonPositiveQInTwoSmallGraphs
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    Graph square(cycle_graph(4));
    std::map<Vertex, int> pre2;
    pre2[square[2].v()] = 2;
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(edge, 3, 0, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, square, 4, -1, pre2),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringRejectsNonCoprimeParameters) {
    Graph triangle(cycle_graph(3));
    std::map<Vertex, int> pre;
    pre[triangle[0].v()] = 0;

    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(triangle, 6, 2, pre),
        std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, 6, 2, pre),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexNoReduceRejectsNonCoprimeParameters) {
    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.reduce_fraction = false;

    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(cycle_graph(3), 6, 2, opts),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgeBoolRejectsNegativePInTwoSmallGraphs) {
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(
            path_graph(2), -1, 1,
            CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, cycle_graph(3), -2, 1),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgeBoolRejectsNonPositiveQInTwoSmallGraphs) {
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(
            path_graph(2), 3, 0,
            CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 4, -1),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringRejectsNegativePInTwoSmallGraphs
) {
    Graph edge(path_graph(2));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = 0;
    Graph path(path_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 1, 2)] = 1;
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(edge, -1, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, path, -2, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringRejectsNonPositiveQInTwoSmallGraphs
) {
    Graph edge(path_graph(2));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = 0;
    Graph path(path_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 0, 1)] = 1;
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(edge, 3, 0, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 4, -1, pre2),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringRejectsNonCoprimeParameters) {
    Graph path(path_graph(3));
    std::map<Edge, int> pre;
    pre[edge_between(path, 0, 1)] = 0;

    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(path, 6, 2, pre), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 6, 2, pre),
        std::invalid_argument
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgeNoReduceRejectsNonCoprimeParameters) {
    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.reduce_fraction = false;

    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(path_graph(3), 6, 2, opts),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexZeroCircleAcceptsEmptyGraphThroughTwoOverloads
) {
    Graph empty(create_empty_graph(0));
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring_without_tight_cycles(
                        empty, 0, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring_without_tight_cycles(
                        empty, 0, 1, std::map<Vertex, int>{}
                    ))
                    .has_value());
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexZeroCircleRejectsNonemptyGraphsThroughTwoOverloads
) {
    Graph isolated(create_empty_graph(1));
    Graph edge(path_graph(2));
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, isolated, 0, 1));
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(
        solver, edge, 0, 1, std::map<Vertex, int>{}
    ));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexQGreaterThanPRejectsEmptyAndNonemptyGraphs
) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, create_empty_graph(0), 2, 3)
    );
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, path_graph(2), 2, 3)
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    EdgeZeroCircleAcceptsGraphWithoutEdgesThroughTwoOverloads
) {
    Graph empty(create_empty_graph(0));
    Graph isolated(create_empty_graph(3));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, empty, 0, 1));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, isolated, 0, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    EdgeZeroCircleRejectsGraphsWithEdgesThroughTwoOverloads
) {
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path_graph(2), 0, 1));
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(
        solver, path_graph(3), 0, 1, std::map<Edge, int>{}
    ));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgeQGreaterThanPRejectsGraphsWithAndWithoutEdges
) {
    EXPECT_FALSE(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, create_empty_graph(3), 2, 3)
    );
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path_graph(2), 2, 3));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexLoopIsRejectedThroughCnfAndDecisionCalls
) {
    Graph loop(loop_graph());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_vertex_colouring_without_tight_cycles(
                         loop, 3, 1,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, loop, 3, 1));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgeLoopIsRejectedThroughCnfAndDecisionCalls) {
    Graph loop(loop_graph());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_edge_colouring_without_tight_cycles(
                         loop, 3, 1,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, loop, 3, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringRejectsNegativeColoursInTwoGraphs
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = -1;
    Graph triangle(cycle_graph(3));
    std::map<Vertex, int> pre2;
    pre2[triangle[1].v()] = -2;
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(edge, 3, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, 4, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringRejectsColoursAtLeastPInTwoGraphs
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 3;
    Graph square(cycle_graph(4));
    std::map<Vertex, int> pre2;
    pre2[square[1].v()] = 5;
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(edge, 3, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, square, 5, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringRejectsNegativeColoursInTwoGraphs
) {
    Graph edge(path_graph(2));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = -1;
    Graph path(path_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 1, 2)] = -2;
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(edge, 3, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 4, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringRejectsColoursAtLeastPInTwoGraphs
) {
    Graph edge(path_graph(2));
    std::map<Edge, int> pre1;
    pre1[edge_between(edge, 0, 1)] = 3;
    Graph path(path_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(path, 0, 1)] = 5;
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(edge, 3, 1, pre1), std::invalid_argument
    );
    EXPECT_THROW(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 5, 1, pre2),
        std::invalid_argument
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringCanForceUnsatOnAdjacentVertices
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> same;
    same[edge[0].v()] = 0;
    same[edge[1].v()] = 0;
    Graph path(path_graph(3));
    std::map<Vertex, int> close;
    close[path[0].v()] = 0;
    close[path[1].v()] = 1;
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, edge, 3, 1, same));
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, path, 5, 2, close));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringCanForceSatOnAdjacentVertices
) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 1;
    Graph path(path_graph(3));
    std::map<Vertex, int> pre2;
    pre2[path[0].v()] = 0;
    pre2[path[1].v()] = 2;
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, edge, 3, 1, pre1));
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, path, 5, 2, pre2));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringCanForceUnsatOnIncidentEdges) {
    Graph path(path_graph(3));
    std::map<Edge, int> same;
    same[edge_between(path, 0, 1)] = 0;
    same[edge_between(path, 1, 2)] = 0;
    Graph longer(path_graph(4));
    std::map<Edge, int> close;
    close[edge_between(longer, 0, 1)] = 0;
    close[edge_between(longer, 1, 2)] = 1;
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 3, 1, same));
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, longer, 5, 2, close));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringCanForceSatOnIncidentEdges) {
    Graph path(path_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 1;
    Graph longer(path_graph(4));
    std::map<Edge, int> pre2;
    pre2[edge_between(longer, 0, 1)] = 0;
    pre2[edge_between(longer, 1, 2)] = 2;
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path, 3, 1, pre1));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, longer, 5, 2, pre2));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringKeepsExactNonReducedColours) {
    Graph edge(path_graph(2));
    std::map<Vertex, int> pre1;
    pre1[edge[0].v()] = 0;
    pre1[edge[1].v()] = 4;
    Graph path(path_graph(3));
    std::map<Vertex, int> pre2;
    pre2[path[0].v()] = 5;
    pre2[path[1].v()] = 1;
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(
        solver, edge, 7, 2, pre1,
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
    ));
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(
        solver, path, 8, 3, pre2,
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
    ));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringKeepsExactNonReducedColours) {
    Graph path(path_graph(3));
    std::map<Edge, int> pre1;
    pre1[edge_between(path, 0, 1)] = 0;
    pre1[edge_between(path, 1, 2)] = 4;
    Graph longer(path_graph(4));
    std::map<Edge, int> pre2;
    pre2[edge_between(longer, 0, 1)] = 5;
    pre2[edge_between(longer, 1, 2)] = 1;
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(
        solver, path, 7, 2, pre1,
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
    ));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(
        solver, longer, 8, 3, pre2,
        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
    ));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexBoolReductionMatchesReducedFractionOnTwoGraphs
) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, cycle_graph(5), 10, 4)
    );
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, path_graph(4), 6, 2)
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, EdgeBoolReductionMatchesReducedFractionOnTwoGraphs
) {
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, cycle_graph(5), 10, 4)
    );
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path_graph(4), 6, 2));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexSymmetryBreakingCoversIsolatedAndNeighbourBranches
) {
    EXPECT_TRUE(
        solver
            .solve(cnf_circular_vertex_colouring_without_tight_cycles(create_empty_graph(1), 4, 1))
            .has_value()
    );
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring_without_tight_cycles(path_graph(2), 4, 1))
                    .has_value());
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    VertexSymmetryDisabledStillSolvesIsolatedAndNeighbourGraphs
) {
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring_without_tight_cycles(
                        create_empty_graph(1), 4, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring_without_tight_cycles(
                        path_graph(2), 4, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    EdgeSymmetryBreakingCoversEmptyAndSingleEdgeLineGraphs
) {
    EXPECT_TRUE(
        solver.solve(cnf_circular_edge_colouring_without_tight_cycles(create_empty_graph(3), 4, 1))
            .has_value()
    );
    EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring_without_tight_cycles(path_graph(2), 4, 1))
                    .has_value());
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    EdgeSymmetryBreakingCoversNeighbourAndDisabledBranches
) {
    EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring_without_tight_cycles(path_graph(3), 4, 1))
                    .has_value());
    EXPECT_TRUE(solver
                    .solve(cnf_circular_edge_colouring_without_tight_cycles(
                        path_graph(3), 4, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexWrappersReturnTrueForAcyclicGraphs) {
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, path_graph(6), 3, 1)
    );
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, star_graph(5), 3, 1)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgeWrappersReturnTrueForAcyclicLineGraphs) {
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path_graph(6), 2, 1));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, path_graph(3), 2, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    TriangleIsColourableButNotWithoutTightCyclesAtThreeOne
) {
    Graph triangle(cycle_graph(3));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, triangle, 3, 1));
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, 3, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    FiveCycleIsColourableButNotWithoutTightCyclesAtFiveTwo
) {
    Graph c5(cycle_graph(5));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, c5, 5, 2));
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, c5, 5, 2));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EvenCycleCanBeForcedTightOrRelaxed) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 2, 1)
    );
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 3, 1)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, CompleteGraphCanBeForcedTightOrRelaxed) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, complete_graph(3), 3, 1)
    );
    EXPECT_TRUE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, complete_graph(3), 4, 1)
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, DisconnectedVertexGraphsRespectTightComponents
) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle_plus_path(), 3, 1)
    );
    EXPECT_TRUE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, square_plus_path(), 3, 1)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringDoesNotHideTightCycleUnsat) {
    Graph c5(cycle_graph(5));
    std::map<Vertex, int> pre1;
    pre1[c5[0].v()] = 0;
    Graph triangle(cycle_graph(3));
    std::map<Vertex, int> pre2;
    pre2[triangle[1].v()] = 1;
    EXPECT_FALSE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, c5, 5, 2, pre1));
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, 3, 1, pre2)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, VertexPrecolouringCanStillAllowRelaxedCycles) {
    Graph square(cycle_graph(4));
    std::map<Vertex, int> pre1;
    pre1[square[0].v()] = 0;
    Graph triangle(cycle_graph(3));
    std::map<Vertex, int> pre2;
    pre2[triangle[0].v()] = 0;
    pre2[triangle[1].v()] = 1;
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, square, 3, 1, pre1));
    EXPECT_TRUE(has_circular_vertex_colouring_without_tight_cycles_sat(solver, triangle, 4, 1, pre2)
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    TriangleEdgesAreColourableButNotWithoutTightCyclesAtThreeOne
) {
    Graph triangle(cycle_graph(3));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, triangle, 3, 1));
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, triangle, 3, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    FiveCycleEdgesAreColourableButNotWithoutTightCyclesAtFiveTwo
) {
    Graph c5(cycle_graph(5));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, c5, 5, 2));
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, c5, 5, 2));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EvenCycleEdgesCanBeForcedTightOrRelaxed) {
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 2, 1)
    );
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, cycle_graph(4), 3, 1));
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, StarEdgesCanBeForcedTightOrRelaxed) {
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, star_graph(3), 3, 1));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, star_graph(3), 4, 1));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, CompleteGraphEdgesAtThreeColoursHaveTightCycles
) {
    EXPECT_FALSE(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, complete_graph(4), 3, 1)
    );
    EXPECT_TRUE(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, complete_graph(3), 4, 1)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringDoesNotHideTightCycleUnsat) {
    Graph c5(cycle_graph(5));
    std::map<Edge, int> pre1;
    pre1[edge_between(c5, 0, 1)] = 0;
    Graph triangle(cycle_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(triangle, 1, 2)] = 1;
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, c5, 5, 2, pre1));
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, triangle, 3, 1, pre2)
    );
}

TEST_F(CircularColouringWithoutTightCyclesFastTest, EdgePrecolouringCanStillAllowRelaxedCycles) {
    Graph square(cycle_graph(4));
    std::map<Edge, int> pre1;
    pre1[edge_between(square, 0, 1)] = 0;
    Graph triangle(cycle_graph(3));
    std::map<Edge, int> pre2;
    pre2[edge_between(triangle, 0, 1)] = 0;
    pre2[edge_between(triangle, 1, 2)] = 1;
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, square, 3, 1, pre1));
    EXPECT_TRUE(has_circular_edge_colouring_without_tight_cycles_sat(solver, triangle, 4, 1, pre2));
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest, CnfSatisfiableShortcutIsExercisedByEmptyGraphs
) {
    EXPECT_TRUE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, create_empty_graph(0), 0, 1)
    );
    EXPECT_TRUE(
        has_circular_edge_colouring_without_tight_cycles_sat(solver, create_empty_graph(0), 0, 1)
    );
}

TEST_F(
    CircularColouringWithoutTightCyclesFastTest,
    CnfUnsatisfiableShortcutIsExercisedByImpossibleInputs
) {
    EXPECT_FALSE(
        has_circular_vertex_colouring_without_tight_cycles_sat(solver, create_empty_graph(1), 0, 1)
    );
    EXPECT_FALSE(has_circular_edge_colouring_without_tight_cycles_sat(solver, loop_graph(), 3, 1));
}

#endif
