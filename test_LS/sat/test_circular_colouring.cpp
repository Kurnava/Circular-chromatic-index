// clang-format off
#include "implementation.h"

#include <algorithm>
#include <map>
#include <numeric>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <graphs/cubic.hpp>
#include <io/unified_io.hpp>
#include <operations/line_graph.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/exec_solver.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

TEST(CircularColouringOptionsTest, RejectsNegativeThresholdsInCnfBuilders) {
    CircularColouringCnfOptions opts;
    opts.vertex_colour_sinz_threshold = -1;

    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));

    EXPECT_THROW(cnf_circular_vertex_colouring(G, 3, 1, opts), std::invalid_argument);
    EXPECT_THROW(
        cnf_circular_vertex_colouring(G, 3, 1, std::map<Vertex, int>{}, opts), std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(G, 3, 1, opts), std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_vertex_colouring_without_tight_cycles(G, 3, 1, std::map<Vertex, int>{}, opts),
        std::invalid_argument
    );
    EXPECT_THROW(cnf_circular_edge_colouring(G, 3, 1, opts), std::invalid_argument);
    EXPECT_THROW(
        cnf_circular_edge_colouring(G, 3, 1, std::map<Edge, int>{}, opts), std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(G, 3, 1, opts), std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_edge_colouring_without_tight_cycles(G, 3, 1, std::map<Edge, int>{}, opts),
        std::invalid_argument
    );
}

TEST(CircularColouringOptionsTest, PLessThan2QReturnsUnsatForNonEmptyGraph) {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, 3, 2);
    EXPECT_EQ(encoding.cnf.num_vars(), 1);
    EXPECT_FALSE(encoding.cnf.clauses().empty());
}

TEST(CircularColouringOptionsTest, PLessThan2QEmptyGraph) {
    Graph G(create_empty_graph(0));
    EXPECT_NO_THROW(build_circular_vertex_colouring_cnf_encoding(G, 3, 2));
}

TEST(CircularColouringOptionsTest, QEqualsPAllowsOnlyEdgelessVertexColouring) {
    Graph edgeless(create_empty_graph(3));
    auto edgeless_encoding = build_circular_vertex_colouring_cnf_encoding(edgeless, 3, 3);
    EXPECT_FALSE(edgeless_encoding.cnf.clauses().empty());

    Graph edge(create_empty_graph(2));
    addE(edge, Location(0, 1));
    auto edge_encoding = build_circular_vertex_colouring_cnf_encoding(edge, 3, 3);
    EXPECT_EQ(edge_encoding.cnf.num_vars(), 1);
    EXPECT_FALSE(edge_encoding.cnf.clauses().empty());
}

#if !BA_GRAPH_HAS_KISSAT_SUPPORT

class CircularColouringFastTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularColouringFastTest, Skipped) {}

#else

namespace {

Graph cycle_graph(int n) {
    Graph G(create_empty_graph(n));
    for (int i = 0; i < n; ++i) {
        addE(G, Location(i, (i + 1) % n));
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

Graph star_graph(int leaves) {
    Graph G(create_empty_graph(leaves + 1));
    for (int i = 1; i <= leaves; ++i) {
        addE(G, Location(0, i));
    }
    return G;
}

Graph graph_with_loop() {
    Graph G(create_empty_graph(2));
    addE(G, Location(0, 1));
    addE(G, Location(0, 0));
    return G;
}

bool contains_fraction(const std::vector<std::pair<int, int> > &fractions, std::pair<int, int> f) {
    return std::find(fractions.begin(), fractions.end(), f) != fractions.end();
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

}  // namespace

class CircularColouringFastTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularColouringFastTest, CircularDistanceBasicCases) {
    EXPECT_EQ(circular_distance(5, 0, 0), 0);
    EXPECT_EQ(circular_distance(5, 0, 1), 1);
    EXPECT_EQ(circular_distance(5, 0, 4), 1);
    EXPECT_EQ(circular_distance(6, 1, 4), 3);
    EXPECT_EQ(circular_distance(10, 2, 8), 4);
}

TEST_F(CircularColouringFastTest, ReduceFractionOptionPreservesSatisfiability) {
    Graph G = cycle_graph(5);

    CircularColouringCnfOptions opts_reduce;
    opts_reduce.reduce_fraction = true;

    CircularColouringCnfOptions opts_no_reduce;
    opts_no_reduce.reduce_fraction = false;

    // C5 has circular chromatic number 5/2, so it is (5,2) colourable.
    // With p=10, q=4:
    // reduce_fraction=true reduces it to (5,2).
    // reduce_fraction=false uses (10,4) directly.
    // Both should be satisfiable!
    auto res_reduce = is_circularly_colourable_sat_constructive(solver, G, 10, 4, opts_reduce);
    auto res_no_reduce =
        is_circularly_colourable_sat_constructive(solver, G, 10, 4, opts_no_reduce);

    EXPECT_TRUE(res_reduce.has_value());
    EXPECT_TRUE(res_no_reduce.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *res_reduce, 10, 4));
    EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *res_no_reduce, 10, 4));

    // With p=10, q=5 (ratio 2): C5 is not colourable.
    auto res_reduce_unsat =
        is_circularly_colourable_sat_constructive(solver, G, 10, 5, opts_reduce);
    auto res_no_reduce_unsat =
        is_circularly_colourable_sat_constructive(solver, G, 10, 5, opts_no_reduce);

    EXPECT_FALSE(res_reduce_unsat.has_value());
    EXPECT_FALSE(res_no_reduce_unsat.has_value());
}

TEST_F(CircularColouringFastTest, VertexPrecolouringOverloadForcesUnreducedFraction) {
    Graph G = single_edge_graph();
    std::map<Vertex, int> precolouring;
    precolouring[G[0].v()] = 9;

    CircularColouringCnfOptions opts;
    opts.reduce_fraction = true;

    auto encoding = build_circular_vertex_colouring_cnf_encoding(G, 10, 4, precolouring, opts);
    EXPECT_EQ(encoding.requested_p, 10);
    EXPECT_EQ(encoding.requested_q, 4);
    EXPECT_EQ(encoding.encoded_p, 10);
    EXPECT_EQ(encoding.encoded_q, 4);
    EXPECT_EQ(encoding.colour_scale, 1);
    EXPECT_EQ(encoding.vertex_colour_vars.at(G[0].n()).size(), 10u);

    EXPECT_NO_THROW(cnf_circular_vertex_colouring(G, 10, 4, precolouring, opts));
}

TEST_F(CircularColouringFastTest, ComputeCircularColouringFractionsValidationAndBoundaries) {
    EXPECT_THROW(
        internal::computeCircularColouringFractions(5, 0, 3, true, true), std::invalid_argument
    );
    EXPECT_THROW(
        internal::computeCircularColouringFractions(5, 4, 3, true, true), std::invalid_argument
    );

    auto closed = internal::computeCircularColouringFractions(6, 2, 3, true, true);
    EXPECT_TRUE(contains_fraction(closed, {2, 1}));
    EXPECT_TRUE(contains_fraction(closed, {5, 2}));
    EXPECT_TRUE(contains_fraction(closed, {3, 1}));

    auto open = internal::computeCircularColouringFractions(6, 2, 3, false, false);
    EXPECT_FALSE(contains_fraction(open, {2, 1}));
    EXPECT_TRUE(contains_fraction(open, {5, 2}));
    EXPECT_FALSE(contains_fraction(open, {3, 1}));
}

TEST_F(CircularColouringFastTest, ComputeCircularColouringFractionsAreReducedUniqueAndSorted) {
    auto fractions = internal::computeCircularColouringFractions(10, 2, 4, true, true);

    for (const auto &[p, q] : fractions) {
        EXPECT_EQ(std::gcd(p, q), 1);
        EXPECT_LE(2 * q, p);
        EXPECT_LE(p, 4 * q);
    }

    EXPECT_TRUE(contains_fraction(fractions, {2, 1}));
    EXPECT_TRUE(contains_fraction(fractions, {5, 2}));
    EXPECT_TRUE(contains_fraction(fractions, {3, 1}));
    EXPECT_TRUE(contains_fraction(fractions, {7, 2}));

    EXPECT_EQ(
        std::adjacent_find(
            fractions.begin(), fractions.end(),
            [](const auto &a, const auto &b) {
                return static_cast<long long>(a.first) * b.second >
                       static_cast<long long>(b.first) * a.second;
            }
        ),
        fractions.end()
    );
}

TEST_F(CircularColouringFastTest, VertexParameterValidation) {
    Graph G = single_edge_graph();

    EXPECT_THROW(
        cnf_circular_vertex_colouring(
            G, -1, 1, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_vertex_colouring(
            G, 5, 0, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_vertex_colouring(
            G, 5, -1, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );

    EXPECT_THROW(is_circularly_colourable_sat(solver, G, -1, 1), std::invalid_argument);
    EXPECT_THROW(is_circularly_colourable_sat(solver, G, 5, 0), std::invalid_argument);
    EXPECT_THROW(is_circularly_colourable_sat(solver, G, 5, -1), std::invalid_argument);
}

TEST_F(CircularColouringFastTest, VertexZeroCircleAndQGreaterThanPCases) {
    Graph empty(create_empty_graph(0));
    Graph isolated(create_empty_graph(1));
    Graph edge = single_edge_graph();

    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring(
                        empty, 0, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_vertex_colouring(
                         isolated, 0, 1,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_vertex_colouring(
                         edge, 0, 1,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());

    EXPECT_FALSE(solver
                     .solve(cnf_circular_vertex_colouring(
                         edge, 2, 3,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(is_circularly_colourable_sat(solver, edge, 2, 3));
}

TEST_F(CircularColouringFastTest, VertexLoopIsRejectedByCnfDecisionAndConstructiveCalls) {
    Graph G = graph_with_loop();

    EXPECT_FALSE(solver
                     .solve(cnf_circular_vertex_colouring(
                         G, 5, 2,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 5, 2));
    EXPECT_FALSE(is_circularly_colourable_sat_constructive(solver, G, 5, 2).has_value());
    EXPECT_FALSE(circular_chromatic_number_sat(solver, G).has_value());
}

TEST_F(CircularColouringFastTest, VertexPrecolouringDomainMismatch) {
    Graph G = single_edge_graph();
    std::map<Vertex, int> precolouring;
    precolouring[Vertex()] = 1;
    EXPECT_THROW(cnf_circular_vertex_colouring(G, 5, 2, precolouring), std::invalid_argument);
}

TEST_F(CircularColouringFastTest, VertexPrecolouringValidation) {
    Graph G = single_edge_graph();

    std::map<Vertex, int> negative_precolouring;
    negative_precolouring[G[0].v()] = -1;
    EXPECT_THROW(
        cnf_circular_vertex_colouring(G, 5, 2, negative_precolouring), std::invalid_argument
    );
    EXPECT_THROW(
        is_circularly_colourable_sat(solver, G, 5, 2, negative_precolouring), std::invalid_argument
    );

    std::map<Vertex, int> too_large_precolouring;
    too_large_precolouring[G[0].v()] = 5;
    EXPECT_THROW(
        cnf_circular_vertex_colouring(G, 5, 2, too_large_precolouring), std::invalid_argument
    );
    EXPECT_THROW(
        is_circularly_colourable_sat(solver, G, 5, 2, too_large_precolouring), std::invalid_argument
    );
}

TEST_F(CircularColouringFastTest, VertexPrecolouringCanForceSatOrUnsat) {
    Graph G = single_edge_graph();

    std::map<Vertex, int> valid_precolouring;
    valid_precolouring[G[0].v()] = 0;
    valid_precolouring[G[1].v()] = 2;

    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(G, 5, 2, valid_precolouring)).has_value()
    );
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2, valid_precolouring));

    std::map<Vertex, int> invalid_distance_precolouring;
    invalid_distance_precolouring[G[0].v()] = 0;
    invalid_distance_precolouring[G[1].v()] = 1;

    EXPECT_FALSE(solver.solve(cnf_circular_vertex_colouring(G, 5, 2, invalid_distance_precolouring))
                     .has_value());
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 5, 2, invalid_distance_precolouring));
}

TEST_F(CircularColouringFastTest, VertexOneSidePrecolouredConstructiveKeepsGivenColour) {
    Graph G = single_edge_graph();

    std::map<Vertex, int> one_side;
    one_side[G[0].v()] = 0;

    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2, one_side));

    auto colouring = is_circularly_colourable_sat_constructive(solver, G, 5, 2, one_side);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *colouring, 5, 2));
    EXPECT_EQ(colouring->at(G[0].n()), 0);
}

TEST_F(CircularColouringFastTest, VertexSymmetryBreakingCoversIsolatedAndNeighbourBranches) {
    Graph isolated(create_empty_graph(3));
    Graph edge = single_edge_graph();

    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring(
                        isolated, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(isolated, 5, 2)).has_value());

    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring(
                        edge, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(edge, 5, 2)).has_value());

    EXPECT_TRUE(is_circularly_colourable_sat(solver, isolated, 5, 2));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, edge, 5, 2));
}

TEST_F(CircularColouringFastTest, VertexConstructiveSatUnsatAndReducedFraction) {
    Graph edge = single_edge_graph();
    Graph triangle(create_complete_graph(3));

    auto edge_colouring = is_circularly_colourable_sat_constructive(solver, edge, 5, 2);
    ASSERT_TRUE(edge_colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(edge, *edge_colouring, 5, 2));

    EXPECT_FALSE(is_circularly_colourable_sat_constructive(solver, triangle, 2, 1).has_value());

    auto triangle_colouring = is_circularly_colourable_sat_constructive(solver, triangle, 6, 2);
    ASSERT_TRUE(triangle_colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(triangle, *triangle_colouring, 6, 2));
    for (const auto &[vertex, colour] : *triangle_colouring) {
        (void)vertex;
        EXPECT_EQ(colour % 2, 0);
    }
}

TEST_F(CircularColouringFastTest, EdgeParameterValidation) {
    Graph G = two_incident_edges_graph();

    EXPECT_THROW(
        cnf_circular_edge_colouring(
            G, -1, 1, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_edge_colouring(
            G, 5, 0, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );
    EXPECT_THROW(
        cnf_circular_edge_colouring(
            G, 5, -1, CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
        ),
        std::invalid_argument
    );

    EXPECT_THROW(is_circularly_edge_colourable_sat(solver, G, -1, 1), std::invalid_argument);
    EXPECT_THROW(is_circularly_edge_colourable_sat(solver, G, 5, 0), std::invalid_argument);
    EXPECT_THROW(is_circularly_edge_colourable_sat(solver, G, 5, -1), std::invalid_argument);
}

TEST_F(CircularColouringFastTest, EdgeZeroCircleLoopAndQGreaterThanPCases) {
    Graph no_edges(create_empty_graph(3));
    Graph one_edge = single_edge_graph();
    Graph two_incident_edges = two_incident_edges_graph();
    Graph loop = graph_with_loop();

    EXPECT_TRUE(solver
                    .solve(cnf_circular_edge_colouring(
                        no_edges, 0, 1,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_edge_colouring(
                         one_edge, 0, 1,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_edge_colouring(
                         loop, 5, 2,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());

    EXPECT_FALSE(solver
                     .solve(cnf_circular_edge_colouring(
                         no_edges, 2, 3,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
    EXPECT_FALSE(solver
                     .solve(cnf_circular_edge_colouring(
                         two_incident_edges, 2, 3,
                         CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                     ))
                     .has_value());
}

TEST_F(CircularColouringFastTest, EdgePrecolouringValidation) {
    Graph G = two_incident_edges_graph();
    Edge e01 = G[0].find(Location(0, 1))->e();

    std::map<Edge, int> negative_precolouring;
    negative_precolouring[e01] = -1;
    EXPECT_THROW(
        cnf_circular_edge_colouring(G, 5, 2, negative_precolouring), std::invalid_argument
    );

    std::map<Edge, int> too_large_precolouring;
    too_large_precolouring[e01] = 5;
    EXPECT_THROW(
        cnf_circular_edge_colouring(G, 5, 2, too_large_precolouring), std::invalid_argument
    );
}

TEST_F(CircularColouringFastTest, EdgePrecolouringForeignEdge) {
    Graph G = two_incident_edges_graph();
    Factory f;
    Graph other(create_empty_graph(2, f));
    addE(other, Location(0, 1), f);
    Edge foreign = other[0].find(Location(0, 1))->e();
    std::map<Edge, int> foreign_edge_precolouring;
    foreign_edge_precolouring[foreign] = 0;
    EXPECT_THROW(
        cnf_circular_edge_colouring(G, 5, 2, foreign_edge_precolouring), std::invalid_argument
    );
    EXPECT_THROW(
        build_circular_edge_colouring_cnf_encoding(G, 5, 2, foreign_edge_precolouring),
        std::invalid_argument
    );
}

TEST_F(CircularColouringFastTest, EdgePrecolouringMultigraph) {
    Factory f;
    Graph G(create_empty_graph(3, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(1, 2), f);
    Edge e01_primary = G[0].find(Location(0, 1, 0))->e();
    std::map<Edge, int> multigraph_precolouring;
    multigraph_precolouring[e01_primary] = 0;
    auto cnf = cnf_circular_edge_colouring(G, 5, 2, multigraph_precolouring);
    EXPECT_GT(cnf.num_vars(), 0);
}

TEST_F(CircularColouringFastTest, EdgePrecolouringCanForceSatOrUnsat) {
    Graph G = two_incident_edges_graph();

    Edge e01 = G[0].find(Location(0, 1))->e();
    Edge e12 = G[1].find(Location(1, 2))->e();

    std::map<Edge, int> valid_precolouring;
    valid_precolouring[e01] = 0;
    valid_precolouring[e12] = 2;

    EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring(G, 5, 2, valid_precolouring)).has_value());
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2, valid_precolouring));

    std::map<Edge, int> invalid_distance_precolouring;
    invalid_distance_precolouring[e01] = 0;
    invalid_distance_precolouring[e12] = 1;

    EXPECT_FALSE(solver.solve(cnf_circular_edge_colouring(G, 5, 2, invalid_distance_precolouring))
                     .has_value());
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 5, 2, invalid_distance_precolouring));
}

TEST_F(CircularColouringFastTest, EdgeSymmetryBreakingCoversEmptyAndNonemptyLineGraphBranches) {
    Graph no_edges(create_empty_graph(4));
    Graph two_incident_edges = two_incident_edges_graph();

    EXPECT_TRUE(solver
                    .solve(cnf_circular_edge_colouring(
                        no_edges, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring(no_edges, 5, 2)).has_value());

    EXPECT_TRUE(solver
                    .solve(cnf_circular_edge_colouring(
                        two_incident_edges, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring(two_incident_edges, 5, 2)).has_value());
}

TEST_F(CircularColouringFastTest, EdgeConstructiveSatUnsatAndReducedFraction) {
    Graph two_incident_edges = two_incident_edges_graph();
    Graph star = star_graph(3);
    Graph triangle = cycle_graph(3);

    auto colouring =
        is_circularly_edge_colourable_sat_constructive(solver, two_incident_edges, 5, 2);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(two_incident_edges, *colouring, 5, 2));

    EXPECT_FALSE(is_circularly_edge_colourable_sat_constructive(solver, star, 2, 1).has_value());

    auto triangle_colouring =
        is_circularly_edge_colourable_sat_constructive(solver, triangle, 6, 2);
    ASSERT_TRUE(triangle_colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(triangle, *triangle_colouring, 6, 2));
    for (const auto &[edge, colour] : *triangle_colouring) {
        (void)edge;
        EXPECT_EQ(colour % 2, 0);
    }
}

TEST_F(CircularColouringFastTest, CircularChromaticNumberSpecialAndStandardGraphs) {
    Graph empty(create_empty_graph(0));
    Graph edgeless(create_empty_graph(4));
    Graph loop = graph_with_loop();
    Graph edge = single_edge_graph();
    Graph c5 = cycle_graph(5);
    Graph triangle(create_complete_graph(3));

    auto empty_result = circular_chromatic_number_sat(solver, empty);
    ASSERT_TRUE(empty_result.has_value());
    EXPECT_EQ(*empty_result, std::make_pair(0, 1));

    auto edgeless_result = circular_chromatic_number_sat(solver, edgeless);
    ASSERT_TRUE(edgeless_result.has_value());
    EXPECT_EQ(*edgeless_result, std::make_pair(1, 1));

    EXPECT_FALSE(circular_chromatic_number_sat(solver, loop).has_value());

    auto edge_result = circular_chromatic_number_sat(solver, edge);
    ASSERT_TRUE(edge_result.has_value());
    EXPECT_EQ(*edge_result, std::make_pair(2, 1));

    auto c5_result = circular_chromatic_number_sat(solver, c5);
    ASSERT_TRUE(c5_result.has_value());
    EXPECT_EQ(*c5_result, std::make_pair(5, 2));

    auto triangle_result = circular_chromatic_number_sat(solver, triangle);
    ASSERT_TRUE(triangle_result.has_value());
    EXPECT_EQ(*triangle_result, std::make_pair(3, 1));
}

TEST_F(CircularColouringFastTest, CircularChromaticNumberProgressStreamBranch) {
    Graph c5 = cycle_graph(5);
    std::ostringstream out;

    auto result = circular_chromatic_number_sat(solver, c5, &out);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(5, 2));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexSpecialAndStandardGraphs) {
    Graph empty(create_empty_graph(0));
    Graph no_edges(create_empty_graph(3));
    Graph one_edge = single_edge_graph();
    Graph loop = graph_with_loop();
    Graph c4 = cycle_graph(4);
    Graph c3 = cycle_graph(3);
    Graph k4(create_complete_graph(4));

    auto empty_result = circular_chromatic_index_sat(solver, empty);
    ASSERT_TRUE(empty_result.has_value());
    EXPECT_EQ(*empty_result, std::make_pair(0, 1));

    auto no_edges_result = circular_chromatic_index_sat(solver, no_edges);
    ASSERT_TRUE(no_edges_result.has_value());
    EXPECT_EQ(*no_edges_result, std::make_pair(0, 1));

    auto one_edge_result = circular_chromatic_index_sat(solver, one_edge);
    ASSERT_TRUE(one_edge_result.has_value());
    EXPECT_EQ(*one_edge_result, std::make_pair(1, 1));

    EXPECT_FALSE(circular_chromatic_index_sat(solver, loop).has_value());

    auto c4_result = circular_chromatic_index_sat(solver, c4);
    ASSERT_TRUE(c4_result.has_value());
    EXPECT_EQ(*c4_result, std::make_pair(2, 1));

    auto c3_result = circular_chromatic_index_sat(solver, c3);
    ASSERT_TRUE(c3_result.has_value());
    EXPECT_EQ(*c3_result, std::make_pair(3, 1));

    auto k4_result = circular_chromatic_index_sat(solver, k4);
    ASSERT_TRUE(k4_result.has_value());
    EXPECT_EQ(*k4_result, std::make_pair(3, 1));
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexProgressStreamBranch) {
    Graph c3 = cycle_graph(3);
    std::ostringstream out;

    auto result = circular_chromatic_index_sat(solver, c3, &out);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(3, 1));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringFastTest, CircularChromaticNumberTightCyclesProgressStream) {
    Graph c5 = cycle_graph(5);
    std::ostringstream out;

    auto result = circular_chromatic_number_tight_cycles_method_sat(solver, c5, &out);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(5, 2));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexTightCyclesProgressStream) {
    Graph c3 = cycle_graph(3);
    std::ostringstream out;

    auto result = circular_chromatic_index_tight_cycles_method_sat(solver, c3, &out);

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(3, 1));
    EXPECT_FALSE(out.str().empty());
}

TEST_F(CircularColouringFastTest, CircularDistanceIsSymmetric) {
    EXPECT_EQ(circular_distance(7, 0, 3), circular_distance(7, 3, 0));
    EXPECT_EQ(circular_distance(7, 1, 6), circular_distance(7, 6, 1));
    EXPECT_EQ(circular_distance(8, 2, 7), circular_distance(8, 7, 2));
}

TEST_F(CircularColouringFastTest, CircularDistanceUsesShorterArc) {
    EXPECT_EQ(circular_distance(7, 0, 6), 1);
    EXPECT_EQ(circular_distance(7, 1, 5), 3);
    EXPECT_EQ(circular_distance(8, 0, 4), 4);
}

TEST_F(CircularColouringFastTest, ComputeFractionsClosedIntervalContainsEndpoints) {
    auto fractions = internal::computeCircularColouringFractions(8, 2, 4, true, true);
    EXPECT_TRUE(contains_fraction(fractions, {2, 1}));
    EXPECT_TRUE(contains_fraction(fractions, {4, 1}));
}

TEST_F(CircularColouringFastTest, ComputeFractionsOpenIntervalSkipsEndpoints) {
    auto fractions = internal::computeCircularColouringFractions(8, 2, 4, false, false);
    EXPECT_FALSE(contains_fraction(fractions, {2, 1}));
    EXPECT_FALSE(contains_fraction(fractions, {4, 1}));
    EXPECT_TRUE(contains_fraction(fractions, {5, 2}));
}

TEST_F(CircularColouringFastTest, VertexEmptyGraphDecisionCases) {
    Graph G(create_empty_graph(0));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 0, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2));
}

TEST_F(CircularColouringFastTest, VertexZeroCircleConstructiveCases) {
    Graph empty(create_empty_graph(0));
    Graph isolated(create_empty_graph(1));

    auto empty_colouring = is_circularly_colourable_sat_constructive(solver, empty, 0, 1);
    ASSERT_TRUE(empty_colouring.has_value());
    EXPECT_TRUE(empty_colouring->empty());

    EXPECT_FALSE(is_circularly_colourable_sat_constructive(solver, isolated, 0, 1).has_value());

    std::map<Vertex, int> precolouring;
    precolouring[isolated[0].v()] = 0;
    EXPECT_THROW(
        is_circularly_colourable_sat_constructive(solver, isolated, 0, 1, precolouring),
        std::invalid_argument
    );
}

TEST_F(CircularColouringFastTest, VertexSingleVertexDecisionCases) {
    Graph G(create_empty_graph(1));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 0, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 1, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 2, 1));
}

TEST_F(CircularColouringFastTest, VertexSingleEdgeDecisionCases) {
    Graph G = single_edge_graph();
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 1, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 2, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2));
}

TEST_F(CircularColouringFastTest, VertexTriangleDecisionCases) {
    Graph G(create_complete_graph(3));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 2, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 3, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 6, 2));
}

TEST_F(CircularColouringFastTest, VertexC5BoundaryCases) {
    Graph G = cycle_graph(5);
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 4, 2));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 5, 2));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 3, 1));
}

TEST_F(CircularColouringFastTest, VertexK4BoundaryCases) {
    Graph G(create_complete_graph(4));
    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 3, 1));
    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 4, 1));
}

TEST_F(CircularColouringFastTest, SymmetryBreakingEmptyGraphReturnsCnfDirectly) {
    Graph empty(create_empty_graph(0));
    Graph edgeless(create_empty_graph(4));

    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring(
                        empty, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(empty, 5, 2)).has_value());
    EXPECT_TRUE(solver
                    .solve(cnf_circular_vertex_colouring(
                        edgeless, 5, 2,
                        CircularColouringCnfOptions{.break_symmetry_by_precolouring = false}
                    ))
                    .has_value());
    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(edgeless, 5, 2)).has_value());
}

TEST_F(CircularColouringFastTest, QEqualsPVertexColouringSolving) {
    Graph edgeless(create_empty_graph(3));
    EXPECT_TRUE(solver.solve(cnf_circular_vertex_colouring(edgeless, 3, 3)).has_value());

    auto colouring = is_circularly_colourable_sat_constructive(solver, edgeless, 3, 3);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_EQ(colouring->size(), 3u);

    Graph edge = single_edge_graph();
    EXPECT_FALSE(solver.solve(cnf_circular_vertex_colouring(edge, 3, 3)).has_value());
}

TEST_F(CircularColouringFastTest, SymmetryBreakingSingleEdgeFixesV0AndBoundsV1) {
    Graph edge = single_edge_graph();

    auto colouring = is_circularly_colourable_sat_constructive(solver, edge, 5, 2);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(edge, *colouring, 5, 2));

    auto c5 = cycle_graph(5);
    auto c5_colouring = is_circularly_colourable_sat_constructive(solver, c5, 5, 2);
    ASSERT_TRUE(c5_colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(c5, *c5_colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, SymmetryBreakingThroughEdgeColouring) {
    Graph edge = single_edge_graph();
    Graph triangle(create_complete_graph(3));

    auto edge_colouring = is_circularly_edge_colourable_sat_constructive(solver, edge, 5, 2);
    ASSERT_TRUE(edge_colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(edge, *edge_colouring, 5, 2));

    auto triangle_colouring =
        is_circularly_edge_colourable_sat_constructive(solver, triangle, 6, 2);
    ASSERT_TRUE(triangle_colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(triangle, *triangle_colouring, 6, 2));
}

TEST_F(CircularColouringFastTest, VertexDisconnectedGraphUsesHardestComponent) {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    addE(G, Location(1, 2));
    addE(G, Location(2, 0));

    auto result = circular_chromatic_number_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(3, 1));
}

TEST_F(CircularColouringFastTest, VertexPrecolouringNonAdjacentEqualColoursAllowed) {
    Graph G = two_incident_edges_graph();
    std::map<Vertex, int> precolouring;
    precolouring[G[0].v()] = 0;
    precolouring[G[2].v()] = 0;

    EXPECT_TRUE(is_circularly_colourable_sat(solver, G, 3, 1, precolouring));
}

TEST_F(CircularColouringFastTest, VertexPrecolouringAdjacentEqualColoursRejected) {
    Graph G = single_edge_graph();
    std::map<Vertex, int> precolouring;
    precolouring[G[0].v()] = 0;
    precolouring[G[1].v()] = 0;

    EXPECT_FALSE(is_circularly_colourable_sat(solver, G, 3, 1, precolouring));
}

TEST_F(CircularColouringFastTest, VertexConstructiveC5WitnessIsValid) {
    Graph G = cycle_graph(5);
    auto colouring = is_circularly_colourable_sat_constructive(solver, G, 5, 2);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_vertex_circular_colouring(G, *colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, VertexConstructiveUnsatReturnsNullopt) {
    Graph G = cycle_graph(5);
    auto colouring = is_circularly_colourable_sat_constructive(solver, G, 4, 2);
    EXPECT_FALSE(colouring.has_value());
}

TEST_F(CircularColouringFastTest, CircularChromaticNumberForPathIsTwo) {
    Graph G = two_incident_edges_graph();
    auto result = circular_chromatic_number_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(2, 1));
}

TEST_F(CircularColouringFastTest, CircularChromaticNumberForK4IsFour) {
    Graph G(create_complete_graph(4));
    auto result = circular_chromatic_number_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(4, 1));
}

TEST_F(CircularColouringFastTest, EdgeEmptyGraphDecisionCases) {
    Graph G(create_empty_graph(3));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 0, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 1, 1));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 2, 3));
}

TEST_F(CircularColouringFastTest, EdgeZeroCircleConstructiveCases) {
    Graph no_edges(create_empty_graph(3));
    Graph edge = single_edge_graph();

    auto empty_colouring = is_circularly_edge_colourable_sat_constructive(solver, no_edges, 0, 1);
    ASSERT_TRUE(empty_colouring.has_value());
    EXPECT_TRUE(empty_colouring->empty());

    EXPECT_FALSE(is_circularly_edge_colourable_sat_constructive(solver, edge, 0, 1).has_value());

    auto e01 = edge[0].find(Location(0, 1))->e();
    std::map<Edge, int> precolouring;
    precolouring[e01] = 0;
    EXPECT_THROW(
        is_circularly_edge_colourable_sat_constructive(solver, edge, 0, 1, precolouring),
        std::invalid_argument
    );
}

TEST_F(CircularColouringFastTest, EdgeSingleEdgeDecisionCases) {
    Graph G = single_edge_graph();
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 0, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 1, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2));
}

TEST_F(CircularColouringFastTest, EdgeTwoIncidentEdgesDecisionCases) {
    Graph G = two_incident_edges_graph();
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 1, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2));
}

TEST_F(CircularColouringFastTest, EdgeTwoNonIncidentEdgesMayShareColour) {
    Graph G(create_empty_graph(4));
    addE(G, Location(0, 1));
    addE(G, Location(2, 3));

    auto e01 = G[0].find(Location(0, 1))->e();
    auto e23 = G[2].find(Location(2, 3))->e();
    std::map<Edge, int> precolouring;
    precolouring[e01] = 0;
    precolouring[e23] = 0;

    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 3, 1, precolouring));
}

TEST_F(CircularColouringFastTest, EdgeSinglePrecolouringIsRespectedByConstructiveCall) {
    Graph G = single_edge_graph();
    auto e01 = G[0].find(Location(0, 1))->e();
    std::map<Edge, int> precolouring;
    precolouring[e01] = 4;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, precolouring);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
    EXPECT_EQ(colouring->at(Location(0, 1)), 4);
}

TEST_F(CircularColouringFastTest, EdgeConstructiveSingleEdgeWitnessIsValid) {
    Graph G = single_edge_graph();
    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 1, 1);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 1, 1));
}

TEST_F(CircularColouringFastTest, EdgeConstructiveUnsatReturnsNullopt) {
    Graph G = star_graph(3);
    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 2, 1);
    EXPECT_FALSE(colouring.has_value());
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexForTwoIncidentEdgesIsTwo) {
    Graph G = two_incident_edges_graph();
    auto result = circular_chromatic_index_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(2, 1));
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexForStarK13IsThree) {
    Graph G = star_graph(3);
    auto result = circular_chromatic_index_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(3, 1));
}

TEST_F(CircularColouringFastTest, CircularChromaticIndexForC5IsFiveOverTwo) {
    Graph G = cycle_graph(5);
    auto result = circular_chromatic_index_sat(solver, G);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, std::make_pair(5, 2));
}

TEST_F(CircularColouringFastTest, EdgeC5BoundaryCases) {
    Graph G = cycle_graph(5);
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 4, 2));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 3, 1));
}

TEST_F(CircularColouringFastTest, EdgeK4BoundaryCases) {
    Graph G(create_complete_graph(4));
    EXPECT_FALSE(is_circularly_edge_colourable_sat(solver, G, 2, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 3, 1));
    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 6, 2));
}

// ======== Parallel Edge Ordering Symmetry Breaking Tests ========

TEST_F(CircularColouringFastTest, TwoVertexTwoParallelEdgesSatWithOffDirectSupport) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    CircularColouringCnfOptions opts1;
    opts1.break_symmetry_by_precolouring = false;

    CircularColouringCnfOptions opts2;
    opts2.break_symmetry_by_precolouring = false;
    opts2.break_symmetry_by_ordering_parallel_edges = true;
    opts2.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    CircularColouringCnfOptions opts3;
    opts3.break_symmetry_by_precolouring = false;
    opts3.break_symmetry_by_ordering_parallel_edges = true;
    opts3.parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    for (const auto &opts : {opts1, opts2, opts3}) {
        auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, opts);
        ASSERT_TRUE(colouring.has_value());
        EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
        EXPECT_TRUE(solver.solve(cnf_circular_edge_colouring(G, 5, 2, opts)).has_value());
    }
}

TEST_F(CircularColouringFastTest, OrderingEnforcesStrictlyIncreasingColours) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(0, 1, 2), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 3, 1, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 3, 1));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 3u);
    int c0 = (*colouring).at(edges[0]);
    int c1 = (*colouring).at(edges[1]);
    int c2 = (*colouring).at(edges[2]);
    EXPECT_LT(c0, c1);
    EXPECT_LT(c1, c2);
}

TEST_F(CircularColouringFastTest, SimpleGraphNoop) {
    Graph G = two_incident_edges_graph();

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, PrecolouringAndOrderingCompatibility) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    ASSERT_EQ(primary_edges.size(), 2u);

    std::map<Edge, int> precolouring;
    precolouring[primary_edges[0]] = 0;

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = true;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring =
        is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, precolouring, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));

    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(primary_locations.size(), 2u);
    EXPECT_EQ(colouring->at(primary_locations[0]), 0);
}

TEST_F(CircularColouringFastTest, ReverseOrientationNormalizationHandlesReversedLocations) {
    Factory f;
    Graph G(createG(f));
    addV(G, 0, f);
    addV(G, 1, f);
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(1, 0, 1), f);
    addE(G, Location(0, 1, 2), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 3, 1, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 3, 1));
}

TEST_F(CircularColouringFastTest, NegativeParameterValidation) {
    Graph G = single_edge_graph();

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    EXPECT_THROW(cnf_circular_edge_colouring(G, 5, 0, opts), std::invalid_argument);
    EXPECT_THROW(cnf_circular_edge_colouring(G, 5, -1, opts), std::invalid_argument);
}

TEST_F(CircularColouringFastTest, BuildEncodingReturnsValidEncoding) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto encoding = build_circular_edge_colouring_cnf_encoding(G, 5, 2, opts);
    EXPECT_GT(encoding.line_graph_encoding.cnf.num_vars(), 0);
    EXPECT_EQ(encoding.line_vertex_to_location.size(), static_cast<std::size_t>(G.size()));

    auto model = solver.solve(encoding.line_graph_encoding.cnf);
    ASSERT_TRUE(model.has_value());
    auto colouring = encoding.decode_model(*model);
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, FractionReductionWithOrdering) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.reduce_fraction = true;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 8, 4, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 8, 4));
}

TEST_F(CircularColouringFastTest, BothSymmetryBreakingFlagsCombinedWithoutPrecolouringConflict) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = true;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, OrderingWithPrecolouringSat) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    ASSERT_EQ(primary_edges.size(), 2u);

    std::map<Edge, int> precolouring;
    precolouring[primary_edges[0]] = 0;

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring =
        is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, precolouring, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));

    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(primary_locations.size(), 2u);
    EXPECT_EQ(colouring->at(primary_locations[0]), 0);
}

TEST_F(CircularColouringFastTest, SUPPORTChainConstraintSatisfied) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(0, 1, 2), f);
    addE(G, Location(0, 1, 3), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 4, 1, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 4, 1));

    auto edges = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(edges.size(), 4u);
    int c0 = (*colouring).at(edges[0]);
    int c1 = (*colouring).at(edges[1]);
    int c2 = (*colouring).at(edges[2]);
    int c3 = (*colouring).at(edges[3]);
    EXPECT_NE(c0, c1);
    EXPECT_NE(c0, c2);
    EXPECT_NE(c0, c3);
    EXPECT_NE(c1, c2);
    EXPECT_NE(c1, c3);
    EXPECT_NE(c2, c3);
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingEmptyGraph) {
    Factory f;
    Graph G(create_empty_graph(0, f));

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2, opts));
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingSingleVertexNoEdges) {
    Factory f;
    Graph G(create_empty_graph(1, f));

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    EXPECT_TRUE(is_circularly_edge_colourable_sat(solver, G, 5, 2, opts));
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingDisconnectedParallelGroups) {
    Factory f;
    Graph G(create_empty_graph(4, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(2, 3, 0), f);
    addE(G, Location(2, 3, 1), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingInvalidEncodingThrows) {
    Graph G = single_edge_graph();

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = static_cast<OrderingEncoding>(999);

    EXPECT_THROW(cnf_circular_edge_colouring(G, 5, 2, opts), std::invalid_argument);
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingPrecolourNonZero) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    ASSERT_EQ(primary_edges.size(), 2u);

    std::map<Edge, int> precolouring;
    precolouring[primary_edges[0]] = 1;

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring =
        is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, precolouring, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));

    auto primary_locations = G.list(RP::all(), IP::primary(), IT::l());
    ASSERT_EQ(primary_locations.size(), 2u);
    EXPECT_EQ(colouring->at(primary_locations[0]), 1);
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingAllEdgesPrecoloured) {
    Factory f;
    Graph G(create_empty_graph(2, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);

    auto primary_edges = G.list(RP::all(), IP::primary(), IT::e());
    ASSERT_EQ(primary_edges.size(), 2u);

    std::map<Edge, int> precolouring;
    precolouring[primary_edges[0]] = 0;
    precolouring[primary_edges[1]] = 2;

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring =
        is_circularly_edge_colourable_sat_constructive(solver, G, 5, 2, precolouring, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 5, 2));
}

TEST_F(CircularColouringFastTest, ParallelEdgeOrderingMultipleParallelGroups) {
    Factory f;
    Graph G(create_empty_graph(4, f));
    addE(G, Location(0, 1, 0), f);
    addE(G, Location(0, 1, 1), f);
    addE(G, Location(1, 2, 0), f);
    addE(G, Location(1, 2, 1), f);
    addE(G, Location(2, 3, 0), f);
    addE(G, Location(2, 3, 1), f);

    CircularColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = false;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    auto colouring = is_circularly_edge_colourable_sat_constructive(solver, G, 9, 2, opts);
    ASSERT_TRUE(colouring.has_value());
    EXPECT_TRUE(is_valid_edge_circular_colouring(G, *colouring, 9, 2));
}

// ======== Circular Criticality Tests ========

class CircularCriticalityTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularCriticalityTest, CchnVertexCriticalOnC5AndK4) {
    Graph C5 = cycle_graph(5);
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, C5));

    Graph K4(create_complete_graph(4));
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, K4));
}

TEST_F(CircularCriticalityTest, CchnVertexNotCriticalOnTwoK4sJoinedByEdge) {
    // Two K4s joined by one bridge. cchn = 4 but removing a vertex from one
    // K4 leaves the other intact, so cchn stays 4 -- not vertex-critical.
    Factory f;
    Graph G(createG(f));
    // K4 on vertices 0-3
    addMultipleV(G, 8, 0, f);
    for (int i = 0; i < 4; ++i) {
        for (int j = i + 1; j < 4; ++j) {
            addE(G, Location(i, j), f);
        }
    }
    // K4 on vertices 4-7
    for (int i = 4; i < 8; ++i) {
        for (int j = i + 1; j < 8; ++j) {
            addE(G, Location(i, j), f);
        }
    }
    // bridge between vertex 3 and vertex 4
    addE(G, Location(3, 4), f);
    EXPECT_EQ(circular_chromatic_number_sat(solver, G).value(), std::make_pair(4, 1));
    EXPECT_FALSE(is_circular_chromatic_number_vertex_critical_sat(solver, G));
}

TEST_F(CircularCriticalityTest, CchnEdgeCriticalOnC5) {
    Graph C5 = cycle_graph(5);
    EXPECT_TRUE(is_circular_chromatic_number_edge_critical_sat(solver, C5));
}

TEST_F(CircularCriticalityTest, CchnEdgeNotCriticalOnC6) {
    // C6 has cchn = 2; removing any edge leaves a path, cchn = 2 as well.
    Graph C6 = cycle_graph(6);
    EXPECT_FALSE(is_circular_chromatic_number_edge_critical_sat(solver, C6));
}

TEST_F(CircularCriticalityTest, CchiVertexCriticalOnPetersen) {
    Graph PG(create_petersen());
    auto cchi = circular_chromatic_index_sat(solver, PG);
    ASSERT_TRUE(cchi.has_value());
    EXPECT_TRUE(is_circular_chromatic_index_vertex_critical_sat(solver, PG, *cchi));
}

TEST_F(CircularCriticalityTest, CchiVertexCriticalOnC5) {
    Graph C5 = cycle_graph(5);
    EXPECT_TRUE(is_circular_chromatic_index_vertex_critical_sat(solver, C5));
}

TEST_F(CircularCriticalityTest, CchiEdgeCriticalOnC5) {
    Graph C5 = cycle_graph(5);
    EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, C5));
}

TEST_F(CircularCriticalityTest, AllFourVariantsOnC5AreTrue) {
    Graph C5 = cycle_graph(5);
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, C5));
    EXPECT_TRUE(is_circular_chromatic_number_edge_critical_sat(solver, C5));
    EXPECT_TRUE(is_circular_chromatic_index_vertex_critical_sat(solver, C5));
    EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, C5));
}

TEST_F(CircularCriticalityTest, AllFourVariantsOnC6AreFalse) {
    Graph C6 = cycle_graph(6);
    EXPECT_FALSE(is_circular_chromatic_number_vertex_critical_sat(solver, C6));
    EXPECT_FALSE(is_circular_chromatic_number_edge_critical_sat(solver, C6));
    EXPECT_FALSE(is_circular_chromatic_index_vertex_critical_sat(solver, C6));
    EXPECT_FALSE(is_circular_chromatic_index_edge_critical_sat(solver, C6));
}

TEST_F(CircularCriticalityTest, CchiEdgeCriticalOnKnownSmallSnarks) {
    for (const auto &g6 : {"D~{", "ETno"}) {
        Graph G = read_graph_autodetect(g6);
        SCOPED_TRACE(g6);
        auto cchi = circular_chromatic_index_sat(solver, G);
        ASSERT_TRUE(cchi.has_value());
        EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, G, *cchi));
    }
}

TEST_F(CircularCriticalityTest, CchiEdgeNotCriticalOnKnownNonCriticalGraphs) {
    for (const auto &g6 : {"L???CB?oJ_DooK"}) {
        Graph G = read_graph_autodetect(g6);
        SCOPED_TRACE(g6);
        auto cchi = circular_chromatic_index_sat(solver, G);
        ASSERT_TRUE(cchi.has_value());
        EXPECT_FALSE(is_circular_chromatic_index_edge_critical_sat(solver, G, *cchi));
    }
}

TEST_F(CircularCriticalityTest, CchnVertexCriticalWithPrecomputedCchn) {
    // Passing the known cchn should give the same result as computing it internally.
    Graph C5 = cycle_graph(5);
    std::pair<int, int> cchn = {5, 2};
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, C5, cchn));

    Graph K4(create_complete_graph(4));
    cchn = {4, 1};
    EXPECT_TRUE(is_circular_chromatic_number_vertex_critical_sat(solver, K4, cchn));
}

TEST_F(CircularCriticalityTest, CchiEdgeCriticalWithPrecomputedCchi) {
    Graph C5(cycle_graph(5));
    std::pair<int, int> cchi = {5, 2};
    EXPECT_TRUE(is_circular_chromatic_index_edge_critical_sat(solver, C5, cchi));
}

#endif
