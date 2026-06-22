// clang-format off
#include "implementation.h"

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <random/random_graphs.hpp>
#include <invariants/degree.hpp>
#include <invariants/girth.hpp>
#include <sat/cnf_circular_colouring.hpp>
#include <sat/exec_circular_colouring.hpp>
#include <sat/solver_kissat.hpp>
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT

class CircularColouringMultigraphSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(CircularColouringMultigraphSlowTest, Skipped) {}

#else

namespace {

void check_multigraph_circular_chromatic_index(
    const KissatSolver &solver, const Graph &G, int p, int q, const std::string &name
) {
    CircularColouringCnfOptions opts_off;
    opts_off.break_symmetry_by_precolouring = false;
    opts_off.break_symmetry_by_ordering_parallel_edges = false;

    CircularColouringCnfOptions opts_support;
    opts_support.break_symmetry_by_precolouring = false;
    opts_support.break_symmetry_by_ordering_parallel_edges = true;
    opts_support.parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    CircularColouringCnfOptions opts_direct;
    opts_direct.break_symmetry_by_precolouring = false;
    opts_direct.break_symmetry_by_ordering_parallel_edges = true;
    opts_direct.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    bool sat_off = is_circularly_edge_colourable_sat(solver, G, p, q, opts_off);
    bool sat_support = is_circularly_edge_colourable_sat(solver, G, p, q, opts_support);
    bool sat_direct = is_circularly_edge_colourable_sat(solver, G, p, q, opts_direct);

    EXPECT_EQ(sat_off, sat_support) << name << " OFF vs SUPPORT disagree";
    EXPECT_EQ(sat_off, sat_direct) << name << " OFF vs DIRECT disagree";
    EXPECT_EQ(sat_support, sat_direct) << name << " SUPPORT vs DIRECT disagree";
}

}  // namespace

class CircularColouringMultigraphSlowTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(CircularColouringMultigraphSlowTest, RandomMultigraphN6P5Q2) {
    Graph G = random_multigraph(6, 24, static_cast<uint32_t>(800));
    check_multigraph_circular_chromatic_index(solver, G, 5, 2, "n=6,size=24,p=5,q=2");
}

TEST_F(CircularColouringMultigraphSlowTest, RandomMultigraphN8P5Q2) {
    Graph G = random_multigraph(8, 40, static_cast<uint32_t>(801));
    check_multigraph_circular_chromatic_index(solver, G, 5, 2, "n=8,size=40,p=5,q=2");
}

TEST_F(CircularColouringMultigraphSlowTest, RandomMultigraphN8P7Q3) {
    Graph G = random_multigraph(8, 40, static_cast<uint32_t>(802));
    check_multigraph_circular_chromatic_index(solver, G, 7, 3, "n=8,size=40,p=7,q=3");
}

#endif
