#include <iostream>
#include <cassert>
#include <map>
#include <vector>
#include <cmath>
#include <string>
#include <set>

#include "impl/basic.hpp"
#include "impl/basic/graph.h"
#include "invariants/fractional_cvd.hpp"

using namespace ba_graph;

// Verifies if the colouring satisfies the circular distance constraint
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
                    std::cerr << "!!! VALIDATION ERROR !!!" << std::endl;
                    std::cerr << "Vertex: " << rot.n().to_int() << std::endl;
                    std::cerr << "Colors: " << c1 << " and " << c2 << std::endl;
                    std::cerr << "Distance: " << dist << " (required >= " << q << ")" << std::endl;
                    assert(false);
                }
            }
        }
    }
}

// Creates an empty graph with n vertices
Graph build_empty_graph(int n, Factory &f) {
    Graph G = f.cG();
    f.aVs(G, n);
    return G;
}

// Creates a complete graph
Graph build_complete_graph(int n, Factory &f) {
    Graph G = build_empty_graph(n, f);
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            f.aE(G, Location(i, j));
        }
    }
    return G;
}

// Creates a star graph with n leaves
Graph build_star_graph(int n_leaves, Factory &f) {
    Graph G = build_empty_graph(n_leaves + 1, f);
    for (int i = 1; i <= n_leaves; ++i) {
        f.aE(G, Location(0, i));
    }
    return G;
}

// Creates a cycle graph
Graph build_cycle_graph(int n, Factory &f) {
    Graph G = build_empty_graph(n, f);
    for (int i = 0; i < n; i++) {
        f.aE(G, Location(i, (i + 1) % n));
    }
    return G;
}

// Creates a K3,3 bipartite graph
Graph build_k33(Factory &f) {
    Graph G = build_empty_graph(6, f);
    for (int i = 0; i < 3; ++i) {
        for (int j = 3; j < 6; ++j) {
            f.aE(G, Location(i, j));
        }
    }
    return G;
}

// Creates a cube graph
Graph build_cube(Factory &f) {
    Graph G = build_empty_graph(8, f);
    f.aE(G, Location(0, 1)); f.aE(G, Location(1, 2)); f.aE(G, Location(2, 3)); f.aE(G, Location(3, 0));
    f.aE(G, Location(4, 5)); f.aE(G, Location(5, 6)); f.aE(G, Location(6, 7)); f.aE(G, Location(7, 4));
    f.aE(G, Location(0, 4)); f.aE(G, Location(1, 5)); f.aE(G, Location(2, 6)); f.aE(G, Location(3, 7));
    return G;
}

// Creates a Petersen graph
Graph build_petersen(Factory &f) {
    Graph G = build_empty_graph(10, f);
    f.aE(G, Location(0, 1)); f.aE(G, Location(1, 2)); f.aE(G, Location(2, 3)); f.aE(G, Location(3, 4)); f.aE(G, Location(4, 0));
    f.aE(G, Location(5, 7)); f.aE(G, Location(7, 9)); f.aE(G, Location(9, 6)); f.aE(G, Location(6, 8)); f.aE(G, Location(8, 5));
    for(int i=0; i<5; ++i) f.aE(G, Location(i, i+5));
    return G;
}

// Creates a Dodecahedron graph
Graph build_dodecahedron(Factory &f) {
    Graph G = build_empty_graph(20, f);
    for(int i=0; i<5; ++i) f.aE(G, Location(i, (i+1)%5));
    for(int i=15; i<20; ++i) f.aE(G, Location(i, (i==19 ? 15 : i+1)));
    for(int i=0; i<5; ++i) f.aE(G, Location(i, i+5));
    return G; 
}

// Runs a specific test case and asserts the result
void run_test(const std::string& name, const Graph& G, int p, int q, bool expect_sat) {
    std::cout << "TEST: " << name << " (p=" << p << ", q=" << q << ")... ";
    
    FractionalCVD solver(p, q, 2000000);
    std::map<Edge, int> colouring;

    bool result = solver.run(G, colouring);

    if (result == expect_sat) {
        if (result) {
            verify_colouring_validity(G, colouring, p, q);
            assert(colouring.size() == (size_t)G.size());
        }
        std::cout << "PASS " << (result ? "(SAT)" : "(UNSAT)") << std::endl;
    } else {
        std::cout << "FAIL! Expected " << (expect_sat ? "SAT" : "UNSAT") 
                  << " but got " << (result ? "SAT" : "UNSAT") << std::endl;
        assert(false);
    }
}

// Main function executing all test cases
int main() {
    Factory f;

    std::cout << "=== BASIC TESTS ===" << std::endl;
    run_test("K3 impossible", build_complete_graph(3, f), 2, 1, false);
    run_test("K3 standard", build_complete_graph(3, f), 3, 1, true);

    run_test("Star S5", build_star_graph(5, f), 5, 1, true);
    run_test("Star S5 Tight", build_star_graph(5, f), 4, 1, false);

    std::cout << "\n=== BIPARTITE GRAPHS (Class 1) ===" << std::endl;
    run_test("K3,3 Bipartite", build_k33(f), 3, 1, true);
    run_test("Cube Q3", build_cube(f), 3, 1, true);

    std::cout << "\n=== PETERSEN GRAPH (The Circular Benchmark) ===" << std::endl;
    Graph P = build_petersen(f);

    run_test("Petersen (3,1)", P, 3, 1, false);
    run_test("Petersen (4,1)", P, 4, 1, true);
    run_test("Petersen (7,2)", P, 7, 2, false);
    run_test("Petersen (9,2) [Easy]", P, 9, 2, true);

    std::cout << "\n=== ISOLATED / DISCONNECTED ===" << std::endl;
    {
        Graph Disconnected = f.cG();
        f.aVs(Disconnected, 4);
        f.aE(Disconnected, Location(0,1));
        f.aE(Disconnected, Location(2,3));
        run_test("Disconnected (1,1)", Disconnected, 1, 1, true); 
    }

    std::cout << "\n=== RANDOM STRESS TEST ===" << std::endl;
    {
        Graph R = build_empty_graph(20, f);
        std::srand(12345);
        int edges_added = 0;
        while(edges_added < 40) {
            int u = std::rand() % 20;
            int v = std::rand() % 20;
            if (u != v) {
                f.aE(R, Location(u, v));
                edges_added++;
            }
        }
        
        run_test("Random Graph (20v, 40e) Large P", R, 15, 1, true);
        
        FractionalCVD solver(5, 2);
        std::map<Edge, int> map;
        bool res = solver.run(R, map);
        if (res) verify_colouring_validity(R, map, 5, 2);
        std::cout << "Random Graph (5,2) Stress: " << (res ? "SAT" : "UNSAT") << " (No crash)" << std::endl;
    }

    std::cout << "\nAll comprehensive tests passed!" << std::endl;

    return 0;
}