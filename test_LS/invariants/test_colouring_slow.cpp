#include <cassert>
#include <iomanip>
#include <sstream>
#include <string>
#include <vector>

// clang-format off
#include "implementation.h"

#include <graphs/basic.hpp>
#include <gtest/gtest.h>
#include <invariants/colouring.hpp>
#include <invariants/degree.hpp>
#include <io/unified_io.hpp>
// clang-format on

#include "../test_resources.hpp"

using namespace ba_graph;

class CVDHeuristicTestSlow : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup if needed
    }
};

// Test CVD heuristic on snarks
TEST_F(CVDHeuristicTestSlow, CVDHeuristicOnSnarks) {
    Factory factory;
    std::vector<std::string> snark_orders = {"10", "18", "20", "22"};
    std::string base_path_template =
        test::resources_graphs_dir() + "/snarks/d03-g04-cc04-chi04/d03-g04-cc04-chi04.";
    for (const std::string& order : snark_orders) {
        std::string filename = base_path_template + order + ".s6";
        std::vector<Graph> graphs_in_file = read_all_graphs_autodetect(filename, factory);
        for (size_t i = 0; i < graphs_in_file.size(); ++i) {
            Graph& g = graphs_in_file[i];
            bool is_colourable_by_cvd = has_cvd_edge_colouring_general(g, -1, -1, 42);
            EXPECT_FALSE(is_colourable_by_cvd);
            is_colourable_by_cvd = has_cvd_edge_colouring_3regular(g, -1, -1);
            EXPECT_FALSE(is_colourable_by_cvd);
        }
    }
}

// Test CVD on cubic graphs
TEST_F(CVDHeuristicTestSlow, CVDOnCubicCC01G03) {
    const std::string correctAnswer = R"(
1
11
11111
0111111111111111110
0000111111111111111111111111111111111111111111111111111111111101111111111111111111111
00000000000000000000000111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111000011111111111111001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111101111111111101111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
)";
    std::stringstream output_ss;
    output_ss << std::endl;  // Match the initial newline in correctAnswer
    Factory factory;
    for (int i = 4; i <= 14; i += 2) {
        std::stringstream ss;
        ss << test::resources_graphs_dir() << "/d03-g03-cc01/d03-g03-cc01." << std::setw(2)
           << std::setfill('0') << i << ".s6";
        std::string filename = ss.str();
        std::vector<Graph> graphs = read_all_graphs_autodetect(filename, factory);
        for (Graph& G : graphs) {
            bool colourable = is_edge_colourable_basic(G, 3);
            bool colourable_cvd = has_cvd_edge_colouring_general(G, -1, -1, 42);
            bool colourable_cvd_3reg = has_cvd_edge_colouring_3regular(G);
            int chi = chromatic_index_basic(G);
            EXPECT_EQ(colourable, colourable_cvd);
            EXPECT_EQ(colourable, colourable_cvd_3reg);
            EXPECT_EQ(colourable, (chi == 3));
            output_ss << colourable;
        }
        output_ss << std::endl;
    }
    EXPECT_EQ(output_ss.str(), correctAnswer);
}
