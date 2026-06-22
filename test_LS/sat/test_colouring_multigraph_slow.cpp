// clang-format off
#include "implementation.h"

#include <gtest/gtest.h>

#include <graphs/basic.hpp>
#include <random/random_graphs.hpp>
#include <invariants/degree.hpp>
#include <invariants/girth.hpp>
#include <sat/cnf_colouring.hpp>
#include <sat/exec_colouring.hpp>
#include <sat/solver_kissat.hpp>
#if BA_GRAPH_HAS_CLASP_SUPPORT
#include <sat/solver_clasp.hpp>
#endif
// clang-format on

using namespace ba_graph;

#if !BA_GRAPH_HAS_KISSAT_SUPPORT

class ColouringMultigraphSlowTest : public ::testing::Test {
protected:
    void SetUp() override { GTEST_SKIP() << "Kissat support not compiled in"; }
};

TEST_F(ColouringMultigraphSlowTest, Skipped) {}

#else

namespace {

void check_multigraph_chromatic_index(
    const KissatSolver &solver, const Graph &G, const std::string &name
) {
    ColouringCnfOptions opts_off;
    opts_off.break_symmetry_by_precolouring = true;
    opts_off.break_symmetry_by_ordering_parallel_edges = false;

    ColouringCnfOptions opts_support;
    opts_support.break_symmetry_by_precolouring = true;
    opts_support.break_symmetry_by_ordering_parallel_edges = true;
    opts_support.parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    ColouringCnfOptions opts_direct;
    opts_direct.break_symmetry_by_precolouring = true;
    opts_direct.break_symmetry_by_ordering_parallel_edges = true;
    opts_direct.parallel_edge_ordering_encoding = OrderingEncoding::DIRECT;

    int chi_off = chromatic_index_sat(solver, G, opts_off);
    int chi_support = chromatic_index_sat(solver, G, opts_support);
    int chi_direct = chromatic_index_sat(solver, G, opts_direct);

    EXPECT_EQ(chi_off, chi_support) << name;
    EXPECT_EQ(chi_off, chi_direct) << name;
    EXPECT_EQ(chi_support, chi_direct) << name;

    EXPECT_FALSE(is_edge_colourable_sat(solver, G, chi_off - 1, opts_off)) << name;
    EXPECT_TRUE(is_edge_colourable_sat(solver, G, chi_off, opts_off)) << name;

    EXPECT_FALSE(is_edge_colourable_sat(solver, G, chi_support - 1, opts_support)) << name;
    EXPECT_TRUE(is_edge_colourable_sat(solver, G, chi_support, opts_support)) << name;

    EXPECT_FALSE(is_edge_colourable_sat(solver, G, chi_direct - 1, opts_direct)) << name;
    EXPECT_TRUE(is_edge_colourable_sat(solver, G, chi_direct, opts_direct)) << name;
}

}  // namespace

class ColouringMultigraphSlowTest : public ::testing::Test {
protected:
    KissatSolver solver;
};

TEST_F(ColouringMultigraphSlowTest, RandomMultigraphN8) {
    Graph G = random_multigraph(8, 56, static_cast<uint32_t>(800));
    check_multigraph_chromatic_index(solver, G, "n=8,size=56,seed=800");
}

TEST_F(ColouringMultigraphSlowTest, RandomMultigraphN10) {
    Graph G = random_multigraph(10, 90, static_cast<uint32_t>(1000));
    check_multigraph_chromatic_index(solver, G, "n=10,size=90,seed=1000");
}

TEST_F(ColouringMultigraphSlowTest, RandomMultigraphN12) {
    Graph G = random_multigraph(12, 132, static_cast<uint32_t>(1200));
    check_multigraph_chromatic_index(solver, G, "n=12,size=132,seed=1200");
}

#if BA_GRAPH_HAS_CLASP_SUPPORT

TEST_F(ColouringMultigraphSlowTest, ClaspAgreesWithKissatN8) {
    Graph G = random_multigraph(8, 56, static_cast<uint32_t>(800));

    ColouringCnfOptions opts;
    opts.break_symmetry_by_precolouring = true;
    opts.break_symmetry_by_ordering_parallel_edges = true;
    opts.parallel_edge_ordering_encoding = OrderingEncoding::SUPPORT;

    ClaspSatSolver clasp_solver;
    int chi_kissat = chromatic_index_sat(solver, G, opts);
    int chi_clasp = chromatic_index_sat(clasp_solver, G, opts);
    EXPECT_EQ(chi_kissat, chi_clasp)
        << "Kissat and Clasp disagree on chromatic index for n=8 multigraph";
}

#endif

#endif
