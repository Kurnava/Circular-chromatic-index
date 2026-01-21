#ifndef FRACTIONAL_CVD_HPP
#define FRACTIONAL_CVD_HPP

#include <vector>
#include <random>
#include <algorithm>
#include <cmath>
#include <map>

#include "impl/basic.hpp"
#include "impl/basic/graph.h"
#include "impl/basic/incidence_predicates.hpp"
#include "impl/basic/rotation_predicates.hpp"

namespace ba_graph {

/**
 * @brief Internal structure representing an edge for the Fractional CVD solver.
 * * Stores the endpoint indices, the current assigned color, and the original edge handle.
 */
struct FCVDInternalEdge {
    int u_idx;
    int v_idx;
    int color;
    Edge original_edge;
};

/**
 * @brief Internal graph representation optimized for the Fractional CVD solver.
 * * Uses integer indices for vertices and edges to allow fast iteration and access 
 * during the local search phase.
 */
struct FCVDInternalGraph {
    int n;
    std::vector<FCVDInternalEdge> edges;
    std::vector<std::vector<int>> inc;

    explicit FCVDInternalGraph(int n) : n(n), inc(n) {}

    void add_edge(int u, int v, const Edge& e) {
        int id = static_cast<int>(edges.size());
        edges.push_back({u, v, 0, e});
        inc[u].push_back(id);
        inc[v].push_back(id);
    }
};

/**
 * @brief Heuristic solver for fractional (circular) edge colouring using randomized local search.
 *
 * This class attempts to find a valid (p,q)-edge-colouring of a graph G. 
 * A (p,q)-edge-colouring assigns colors from {0, ..., p-1} to edges such that 
 * for any two edges incident to the same vertex, the circular distance between 
 * their colors is at least q.
 * * The algorithm uses a randomized local search strategy (Markov Chain based) to resolve conflicts.
 */
class FractionalCVD {
public:
    /**
     * @brief Constructs the FractionalCVD solver.
     * * @param p The perimeter of the circle (number of available colors).
     * @param q The required minimum circular distance between incident edges (default is 2).
     * @param max_steps The maximum number of iterations for the local search before giving up (default 1,000,000).
     */
    FractionalCVD(int p, int q = 2, int max_steps = 1'000'000)
        : p_(p), q_(q), max_steps_(max_steps), rng_(std::random_device{}()) {
        candidates_.reserve(p_);
    }

    /**
     * @brief Runs the heuristic solver to find a valid colouring.
     * * If an initial colouring is provided in the map, the solver starts from that state.
     * Otherwise, it starts from a random assignment.
     * * @param G The input graph to colour.
     * @param colouring [in/out] A map to store the result. If not empty, used as initial state. 
     * On success, contains the valid (p,q)-colouring.
     * @return true if a valid (p,q)-colouring was found within max_steps.
     * @return false if the solver failed to find a valid colouring (the partial result is still returned in colouring).
     */
    [[nodiscard]] bool run(const Graph &G, std::map<Edge, int> &colouring) {
        std::map<int, int> vertex_to_idx;
        int idx_counter = 0;
        for (const auto& rot : G) {
            vertex_to_idx[rot.n().to_int()] = idx_counter++;
        }

        FCVDInternalGraph IG(idx_counter);

        auto primary_incidences = G.list(RP::all(), IP::primary());
        for (const auto& inc : primary_incidences) {
            int u = vertex_to_idx[inc->n1().to_int()];
            int v = vertex_to_idx[inc->n2().to_int()];
            IG.add_edge(u, v, inc->e());
        }

        if (colouring.empty()) {
             random_init(IG);
        } else {
            for (auto &e : IG.edges) {
                if (colouring.count(e.original_edge)) {
                    e.color = colouring.at(e.original_edge);
                } else {
                    e.color = rand_color();
                }
            }
        }

        bool success = false;
        for (int i = 0; i < max_steps_; ++i) {
            if (!step(IG)) {
                success = true; 
                break;
            }
        }

        colouring.clear();
        for (const auto &e : IG.edges) {
            colouring[e.original_edge] = e.color;
        }

        return success;
    }

private:
    int p_;
    int q_;
    int max_steps_;
    std::mt19937 rng_;
    std::vector<int> candidates_;

    inline int rand_color() {
        return std::uniform_int_distribution<int>(0, p_ - 1)(rng_);
    }

    /**
     * @brief Computes the shortest distance between two points on a circle of length p.
     */
    inline static int cyclic_dist(int a, int b, int p) {
        int d = std::abs(a - b);
        return (d < p - d) ? d : p - d;
    }

    void random_init(FCVDInternalGraph &G) {
        for (auto &e : G.edges)
            e.color = rand_color();
    }

    /**
     * @brief Checks if assigning new_color to edge e_id creates a conflict at vertex u.
     */
    bool creates_conflict_at(
        const FCVDInternalGraph &G, int u, int e_id, int new_color) const {

        for (int f_id : G.inc[u]) {
            if (f_id == e_id) continue;
            if (cyclic_dist(new_color, G.edges[f_id].color, p_) < q_)
                return true;
        }
        return false;
    }

    /**
     * @brief Performs one step of the local search.
     * * Finds a conflict (if any) and attempts to resolve it by recoloring an involved edge.
     * * @return true if a conflict was found and processed (search should continue).
     * @return false if no conflicts were found (graph is validly coloured).
     */
    bool step(FCVDInternalGraph &G) {
        int n = G.n;
        int start_idx = std::uniform_int_distribution<int>(0, n - 1)(rng_);

        for (int k = 0; k < n; ++k) {
            int u = (start_idx + k); 
            if (u >= n) u -= n;

            const auto &L = G.inc[u];
            for (size_t i = 0; i < L.size(); ++i) {
                for (size_t j = i + 1; j < L.size(); ++j) {
                    int e1_id = L[i];
                    int e2_id = L[j];
                    
                    if (cyclic_dist(
                            G.edges[e1_id].color,
                            G.edges[e2_id].color,
                            p_) >= q_) 
                        continue;

                    // Conflict found, try to resolve it
                    int e_id = (rng_() & 1) ? e1_id : e2_id;
                    
                    int v = (G.edges[e_id].u_idx == u)
                                ? G.edges[e_id].v_idx
                                : G.edges[e_id].u_idx;

                    int old_color = G.edges[e_id].color;
                    
                    candidates_.clear();
                    
                    for (int c = 0; c < p_; ++c) {
                        if (c == old_color) continue;
                        if (!creates_conflict_at(G, u, e_id, c))
                            candidates_.push_back(c);
                    }

                    std::shuffle(candidates_.begin(), candidates_.end(), rng_);

                    for (int c : candidates_) {
                        if (!creates_conflict_at(G, v, e_id, c)) {
                            G.edges[e_id].color = c;
                            return true; 
                        }
                    }

                    if (!candidates_.empty()) {
                        G.edges[e_id].color = candidates_[0];
                    } else {
                        G.edges[e_id].color = rand_color();
                    }

                    return true; 
                }
            }
        }
        return false; 
    }
};

} // namespace ba_graph

#endif