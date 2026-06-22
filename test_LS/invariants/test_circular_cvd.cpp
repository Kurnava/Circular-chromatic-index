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

void run_test(const std::string &, const Graph &G, int p, int q, bool expect_sat) {
    CircularCVD solver(p, q);
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

TEST(CircularCVD, Basic) {
    Factory f;

    run_test("K3 standard", create_complete_graph(3, f), 3, 1, true);
    run_test("Star S5", create_star(5, f), 5, 1, true);
    run_test("K3,3 Bipartite", create_complete_bipartite_graph(3, 3, f), 3, 1, true);
    run_test("Cube Q3", create_hypercube(3, f), 3, 1, true);

    Graph P = create_petersen(f);
    run_test("Petersen (4,1)", P, 4, 1, true);

    Graph Disconnected = f.cG();
    f.aVs(Disconnected, 4);
    f.aE(Disconnected, Location(0, 1));
    f.aE(Disconnected, Location(2, 3));
    run_test("Disconnected (1,1)", Disconnected, 1, 1, true);
}

TEST(CircularCVD, EmptyGraphIsColourable) {
    CircularCVD solver(3, 1);
    Graph G = create_empty_graph(0);
    std::map<Edge, int> colouring;

    EXPECT_TRUE(solver.run(G, colouring));
    EXPECT_TRUE(colouring.empty());
}

TEST(CircularCVD, PGreaterThanQ) {
    // p > q should be solvable for simple graphs (like a single edge).
    Factory f;
    CircularCVD solver(3, 2);
    Graph G = create_path_edges(1, f);
    std::map<Edge, int> colouring;
    EXPECT_TRUE(solver.run(G, colouring));
    EXPECT_EQ(colouring.size(), 1u);
}

TEST(CircularCVD, PLessThanQ) {
    // p < q makes the circular distance condition impossible for adjacent edges.
    // Use K3 (triangle) where each vertex has degree 2, forcing conflicts.
    Factory f;
    CircularCVD solver(2, 3, 100000);
    Graph G = create_complete_graph(3, f);
    std::map<Edge, int> colouring;
    EXPECT_FALSE(solver.run(G, colouring));
}

TEST(CircularCVD, PrecolouredInputAsInitialState) {
    // Pre-populate the colouring map as initial state (not enforced constraint).
    Factory f;
    CircularCVD solver(3, 1);
    Graph G = create_complete_graph(3, f);
    std::map<Edge, int> colouring;
    // Precolour one edge.
    for (const auto &inc : G[0]) {
        colouring[inc.e()] = 0;
        break;
    }
    bool result = solver.run(G, colouring);
    // Precolouring is used as initial state, solver may change it.
    // Key test: doesn't crash and produces valid colours if SAT.
    if (result) {
        EXPECT_EQ(colouring.size(), static_cast<size_t>(G.size()));
        verify_colouring_validity(G, colouring, 3, 1);
    }
}

TEST(CircularCVD, PrecolouredInputLarge) {
    // Precolouring on a larger graph: should not crash, results are valid if SAT.
    Factory f;
    CircularCVD solver(5, 1);
    Graph G = create_petersen(f);
    std::map<Edge, int> colouring;
    // Precolour all edges of vertex 0 with colour 0.
    for (const auto &inc : G[0]) {
        colouring[inc.e()] = 0;
    }
    // Petersen is colourable with (5,1).
    EXPECT_TRUE(solver.run(G, colouring));
    EXPECT_EQ(colouring.size(), static_cast<size_t>(G.size()));
    verify_colouring_validity(G, colouring, 5, 1);
}

TEST(CircularCVD, InvalidPThrows) { EXPECT_THROW(CircularCVD(0, 2), std::runtime_error); }

TEST(CircularCVD, InvalidQThrows) { EXPECT_THROW(CircularCVD(1, 0), std::runtime_error); }

TEST(CircularCVD, InvalidMaxStepsThrows) {
    EXPECT_THROW(CircularCVD(1, 2, -1), std::runtime_error);
}
