// clang-format off
#include "implementation.h"

#include <cmath>
#include <graphs/basic.hpp>
#include <graphs/bipartite.hpp>
#include <graphs/cubic.hpp>
#include <invariants/circular_cvd.hpp>
// clang-format on

#include <map>
#include <string>
#include <vector>

#include "gtest/gtest.h"

using namespace ba_graph;

void verify_colouring_validity(const Graph &G, const std::map<Edge, int> &colouring, int p, int q) {
    for (const auto &rot : G) {
        std::vector<Edge> incident_edges;
        for (const auto &inc : rot) {
            incident_edges.push_back(inc.e());
        }
        for (size_t i = 0; i < incident_edges.size(); ++i) {
            for (size_t j = i + 1; j < incident_edges.size(); ++j) {
                int c1 = colouring.at(incident_edges[i]);
                int c2 = colouring.at(incident_edges[j]);
                int diff = std::abs(c1 - c2);
                int dist = std::min(diff, p - diff);
                if (dist < q) {
                    FAIL() << "Validation error at vertex " << rot.n().to_int() << " with colors "
                           << c1 << " and " << c2 << " distance " << dist << " (required >= " << q
                           << ")";
                    return;
                }
            }
        }
    }
}

void run_test(
    [[maybe_unused]] const std::string &name, const Graph &G, int p, int q, bool expect_sat,
    int max_steps = 1'000'000
) {
    CircularCVD solver(p, q, max_steps);
    std::map<Edge, int> colouring;
    bool result = solver.run(G, colouring);

    if (result == expect_sat) {
        if (result) {
            verify_colouring_validity(G, colouring, p, q);
            ASSERT_EQ(colouring.size(), static_cast<size_t>(G.size()));
        }
    } else {
        FAIL() << "Expected " << (expect_sat ? "SAT" : "UNSAT") << " but got "
               << (result ? "SAT" : "UNSAT");
    }
}

TEST(CircularCVDSlow, Comprehensive) {
    Factory f;

    run_test("K3 impossible", create_complete_graph(3, f), 2, 1, false);
    run_test("K3 standard", create_complete_graph(3, f), 3, 1, true);
    run_test("Star S5", create_star(5, f), 5, 1, true);
    run_test("Star S5 Tight", create_star(5, f), 4, 1, false);
    run_test("K3,3 Bipartite", create_complete_bipartite_graph(3, 3, f), 3, 1, true);
    run_test("Cube Q3", create_hypercube(3, f), 3, 1, true);

    Graph P = create_petersen(f);
    run_test("Petersen (3,1)", P, 3, 1, false);
    run_test("Petersen (4,1)", P, 4, 1, true);
    run_test("Petersen (7,2)", P, 7, 2, false, 2'000'000);
    run_test("Petersen (9,2) [Easy]", P, 9, 2, true);

    {
        Graph Disconnected = f.cG();
        f.aVs(Disconnected, 4);
        f.aE(Disconnected, Location(0, 1));
        f.aE(Disconnected, Location(2, 3));
        run_test("Disconnected (1,1)", Disconnected, 1, 1, true);
    }

    {
        Graph R = create_empty_graph(20, f);
        std::srand(12345);
        int edges_added = 0;
        while (edges_added < 40) {
            int u = std::rand() % 20;
            int v = std::rand() % 20;
            if (u != v) {
                f.aE(R, Location(u, v));
                edges_added++;
            }
        }

        run_test("Random Graph (20v, 40e) Large P", R, 15, 1, true);

        CircularCVD solver(5, 2);
        std::map<Edge, int> map;
        bool res = solver.run(R, map);
        if (res) {
            verify_colouring_validity(R, map, 5, 2);
        }
    }
}
