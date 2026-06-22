#ifndef BA_GRAPH_INVARIANTS_COLOURING_CVD_HPP
#define BA_GRAPH_INVARIANTS_COLOURING_CVD_HPP

#include <algorithm>  // For std::find, std::fill, std::shuffle, std::max
#include <cmath>      // For sqrt
#include <iterator>   // For std::advance
#include <map>
#include <numeric>    // For std::iota
#include <random>     // For std::random_device, std::mt19937, std::uniform_int_distribution
#include <set>        // For std::set
#include <stdexcept>  // For std::runtime_error
#include <string>     // For std::to_string
#include <utility>    // For std::pair
#include <vector>

#include "colouring_cvd_3regular.hpp"
#include "colouring_cvd_4regular.hpp"
#include "degree.hpp"        // For is_d_regular
#include "graphs/basic.hpp"  // For ba_graph::Graph, Vertex, Edge

/* Fiol-Vilaltella CVD heuristics, https://arxiv.org/abs/1210.5176, based on Gemini output */
namespace ba_graph {

namespace cvd_internal {  // Encapsulate in a detail namespace

// Simplified graph structure for internal CVD operations.
// This structure is used to represent the graph in a way that is more
// convenient for the colouring algorithm, using integer IDs for vertices and edges,
// and storing adjacency information directly.
struct SimpleCVDGraph {
    int num_vertices;
    int num_edges;
    int G_max_degree;  // Max degree of the original graph, for colouring (Delta)

    // Adjacency list: for vertex u_id, adj[u_id][i] is the i-th neighbor's u_id
    std::vector<std::vector<int>> adj;
    // Edge IDs: adj_edge_ids[u_id][i] is the ID of the edge (u_id, adj[u_id][i])
    std::vector<std::vector<int>> adj_edge_ids;
    // Vertex degrees in the simple graph
    std::vector<int> degree;

    // Edge colours, indexed by edge ID (0 to num_edges-1)
    std::vector<int> edge_colours;

    // Mappings from original ba_graph::Vertex to simple int ID
    std::map<Vertex, int> vertex_to_int_id;
    // For each simple edge ID, store its pair of simple vertex endpoint IDs {u_simple_id,
    // v_simple_id}
    std::vector<std::pair<int, int>> edge_endpoints;

    SimpleCVDGraph(const Graph& G, int G_max_deg_param)
        : G_max_degree(G_max_deg_param) {
        num_vertices = G.order();
        adj.resize(num_vertices);
        adj_edge_ids.resize(num_vertices);
        degree.resize(num_vertices, 0);

        int current_vertex_id_counter = 0;
        // Temporary map to store original vertex to int ID mapping during construction
        std::map<Vertex, int> temp_vertex_to_int_id;

        for (const auto& r_it : G) {
            Vertex orig_v = r_it.v();
            temp_vertex_to_int_id[orig_v] = current_vertex_id_counter;
            current_vertex_id_counter++;
        }
        vertex_to_int_id = temp_vertex_to_int_id;

        int current_edge_id_counter = 0;
        std::map<Edge, int> temp_orig_edge_to_id;

        std::vector<std::pair<int, int>> temp_edge_endpoints_build;
        for (const auto& r_it : G) {
            int u_id = vertex_to_int_id.at(r_it.v());
            degree[u_id] = r_it.degree();
            adj[u_id].resize(degree[u_id]);
            adj_edge_ids[u_id].resize(degree[u_id]);

            int neighbor_idx = 0;
            for (const auto& inc : r_it) {
                Edge orig_e = inc.e();
                Vertex orig_neighbor_v = inc.v2();
                int v_id = vertex_to_int_id.at(orig_neighbor_v);

                adj[u_id][neighbor_idx] = v_id;

                auto map_find_res = temp_orig_edge_to_id.find(orig_e);
                int edge_id;
                if (map_find_res == temp_orig_edge_to_id.end()) {
                    edge_id = current_edge_id_counter;
                    temp_orig_edge_to_id[orig_e] = edge_id;

                    if (edge_id >= static_cast<int>(temp_edge_endpoints_build.size())) {
                        // Grow by a reasonable chunk to avoid frequent reallocations
                        // if edges are not added in a perfectly sequential manner (e.g. due to map
                        // iteration order)
                        temp_edge_endpoints_build.resize(edge_id + 128);
                    }
                    temp_edge_endpoints_build[edge_id] = {u_id, v_id};
                    current_edge_id_counter++;
                } else {
                    edge_id = map_find_res->second;
                }
                adj_edge_ids[u_id][neighbor_idx] = edge_id;
                neighbor_idx++;
            }
        }
        num_edges = current_edge_id_counter;
        edge_colours.assign(num_edges, 0);
        edge_endpoints.assign(
            temp_edge_endpoints_build.begin(), temp_edge_endpoints_build.begin() + num_edges
        );
    }
};

// Helper function to calculate conflict level for a vertex in SimpleCVDGraph.
// The conflict level of a vertex 'u' is defined as deg(u) - d(u),
// where deg(u) is the degree of u, and d(u) is the number of distinct colours
// used on edges incident to u. A conflict level of 0 means the vertex is properly coloured.
static int calculate_conflict_level(int u_id, const SimpleCVDGraph& sg) {
    if (sg.degree[u_id] == 0) {
        return 0;
    }
    int distinct_colours_count = 0;
    std::vector<bool> colours_present(sg.G_max_degree + 1, false);

    for (int i = 0; i < sg.degree[u_id]; ++i) {
        int edge_id = sg.adj_edge_ids[u_id][i];
        if (edge_id < 0 || edge_id >= sg.num_edges) {
            // LCOV_EXCL_START — requires corrupted internal state to trigger
            throw std::runtime_error(
                "calculate_conflict_level: out-of-bounds edge_id " + std::to_string(edge_id) +
                " for vertex " + std::to_string(u_id)
            );
            // LCOV_EXCL_STOP
        }
        int colour = sg.edge_colours[edge_id];

        if (colour >= 1 && colour <= sg.G_max_degree) {
            if (!colours_present[colour]) {
                colours_present[colour] = true;
                distinct_colours_count++;
            }
        }
    }
    return sg.degree[u_id] - distinct_colours_count;
}

// Structure to manage the conflict state of the graph during general CVD.
// It encapsulates the conflict dictionary, current conflict levels per vertex,
// and the total sum of conflicts.
struct ConflictState {
    std::vector<std::vector<int>>
        dict_array;                   // dict_array[cl] stores vertices with conflict level cl
    std::vector<int> current_levels;  // current_levels[u_id] stores conflict level of vertex u_id
    int total_conflicts_val;          // Sum of all conflict levels
    int G_max_degree_cache;           // Cache max degree for dict_array sizing

    ConflictState(int num_vertices, int max_degree)
        : total_conflicts_val(0),
          G_max_degree_cache(max_degree) {
        // Conflict level ranges [0, G_max_degree]. dict_array needs size G_max_degree + 1.
        dict_array.assign(max_degree + 1, std::vector<int>());
        current_levels.assign(num_vertices, 0);
    }

    // Initializes the conflict state based on the current edge colouring of sg.
    void initialize(const SimpleCVDGraph& sg) {
        total_conflicts_val = 0;
        // Ensure dict_array is correctly sized and cleared
        dict_array.assign(G_max_degree_cache + 1, std::vector<int>());
        std::fill(current_levels.begin(), current_levels.end(), 0);

        for (int u_id = 0; u_id < sg.num_vertices; ++u_id) {
            int cl = calculate_conflict_level(u_id, sg);
            current_levels[u_id] = cl;
            if (cl > 0) {
                if (cl < static_cast<int>(dict_array.size())) {
                    dict_array[cl].push_back(u_id);
                }
                total_conflicts_val += cl;
            }
        }
    }

    // Updates the conflict state for a single vertex u_id after its incident edge colours might
    // have changed.
    void update_vertex_state(int u_id, const SimpleCVDGraph& sg) {
        int old_cl = current_levels[u_id];
        if (old_cl > 0) {
            if (old_cl < static_cast<int>(dict_array.size())) {
                auto& v_list = dict_array[old_cl];
                auto it_remove = std::find(v_list.begin(), v_list.end(), u_id);
                if (it_remove != v_list.end()) {
                    *it_remove = v_list.back();
                    v_list.pop_back();
                }
            }
        }
        total_conflicts_val -= old_cl;
        int new_cl = calculate_conflict_level(u_id, sg);
        current_levels[u_id] = new_cl;
        if (new_cl > 0) {
            if (new_cl < static_cast<int>(dict_array.size())) {
                dict_array[new_cl].push_back(u_id);
            }
        }
        total_conflicts_val += new_cl;
    }
};

// Helper function for the initial random colouring of edges
// This function assigns an initial colour to each edge of the graph.
// It iterates through edges in a random order. For each edge (u,v),
// it tries to assign the smallest available colour (not used by other edges
// incident to u or v). If all G_max_degree colours are forbidden,
// a random colour is chosen. This creates a partially "good" starting point.
static void initialize_random_edge_colouring(
    SimpleCVDGraph& sg,  // sg.edge_colours will be modified
    std::mt19937& g_rand
) {
    std::vector<int> local_edge_shuffling_indices(sg.num_edges);
    std::iota(local_edge_shuffling_indices.begin(), local_edge_shuffling_indices.end(), 0);
    std::shuffle(
        local_edge_shuffling_indices.begin(), local_edge_shuffling_indices.end(),
        g_rand
    );  // Randomize edge processing order

    std::fill(sg.edge_colours.begin(), sg.edge_colours.end(), 0);  // Reset all colours
    for (int edge_id : local_edge_shuffling_indices) {
        if (edge_id < 0 || edge_id >= sg.num_edges) {
            // LCOV_EXCL_START — requires corrupted internal state to trigger
            throw std::runtime_error(
                "initialize_random_edge_colouring: out-of-bounds edge_id " + std::to_string(edge_id)
            );
            // LCOV_EXCL_STOP
        }
        const auto& endpoints = sg.edge_endpoints[edge_id];
        int u_id = endpoints.first;
        int v_id = endpoints.second;

        std::vector<bool> forbidden_colours_vec(sg.G_max_degree + 1, false);

        // Identify colours already used by other edges incident to u_id
        for (int i = 0; i < sg.degree[u_id]; ++i) {
            int incident_edge_id = sg.adj_edge_ids[u_id][i];
            if (incident_edge_id != edge_id && sg.edge_colours[incident_edge_id] != 0) {
                int colour = sg.edge_colours[incident_edge_id];
                if (colour >= 1 && colour <= sg.G_max_degree) {
                    forbidden_colours_vec[colour] = true;
                }
            }
        }
        // Identify colours already used by other edges incident to v_id
        for (int i = 0; i < sg.degree[v_id]; ++i) {
            int incident_edge_id = sg.adj_edge_ids[v_id][i];
            if (incident_edge_id != edge_id && sg.edge_colours[incident_edge_id] != 0) {
                int colour = sg.edge_colours[incident_edge_id];
                if (colour >= 1 && colour <= sg.G_max_degree) {
                    forbidden_colours_vec[colour] = true;
                }
            }
        }

        int chosen_colour = 0;
        bool found_colour = false;
        // Greedily pick the smallest available colour
        for (int c = 1; c <= sg.G_max_degree; ++c) {
            if (!forbidden_colours_vec[c]) {
                chosen_colour = c;
                found_colour = true;
                break;
            }
        }
        if (!found_colour) {
            // If all colours up to G_max_degree are forbidden (should be rare for Delta-colouring),
            // pick one randomly.
            chosen_colour = std::uniform_int_distribution<>(1, sg.G_max_degree)(g_rand);
        }
        sg.edge_colours[edge_id] = chosen_colour;
    }
}

// Helper function to perform one Kempe chain step
// This is the core of the iterative improvement.
// 1. Select a conflicting vertex, identified by `conflicting_vertex_id`.
// 2. Identify a colour c1 that is used on at least two edges incident to this vertex.
// 3. Choose a colour c2 (different from c1) that is either not incident to this vertex or incident
// exactly once.
// 4. Construct a maximal (c1, c2)-Kempe chain starting from one of the c1-coloured edges at this
// vertex.
// 5. Swap colours c1 and c2 along this chain.
// 6. Update conflict levels for all vertices affected by the swap.
static bool perform_kempe_chain_step(
    SimpleCVDGraph& sg, int conflicting_vertex_id, ConflictState& conflict_state,
    std::mt19937& g_rand
) {
    // Find a colour c1 that is involved in a conflict at conflicting_vertex_id.
    // This means c1 is used on more than one edge incident to u.
    int conflicting_edge_id = -1;
    int c1 = 0;

    std::vector<int> colour_counts_at_u_vec(sg.G_max_degree + 1, 0);
    std::vector<bool> incident_colours_at_u_vec(sg.G_max_degree + 1, false);
    // Count occurrences of each colour on edges incident to conflicting_vertex_id
    for (int i = 0; i < sg.degree[conflicting_vertex_id]; ++i) {
        int current_edge_id = sg.adj_edge_ids[conflicting_vertex_id][i];
        if (current_edge_id < 0 || current_edge_id >= sg.num_edges) {
            // LCOV_EXCL_START — requires corrupted internal state to trigger
            throw std::runtime_error(
                "perform_kempe_chain_step: out-of-bounds edge_id " +
                std::to_string(current_edge_id) + " for vertex " +
                std::to_string(conflicting_vertex_id)
            );
            // LCOV_EXCL_STOP
        }
        int c_val = sg.edge_colours[current_edge_id];

        if (c_val == 0) {  // Uncoloured edge
            continue;
        }

        if (c_val >= 1 && c_val <= sg.G_max_degree) {
            incident_colours_at_u_vec[c_val] = true;
            colour_counts_at_u_vec[c_val]++;
            if (colour_counts_at_u_vec[c_val] > 1 && conflicting_edge_id == -1) {
                conflicting_edge_id = current_edge_id;
                c1 = c_val;
            }
        }
    }

    if (conflicting_edge_id == -1 || c1 == 0) {
        return false;  // Could not find a conflicting colour c1
    }

    // Find a candidate colour c2 for the Kempe chain.
    // c2 should ideally be a colour not present at conflicting_vertex_id,
    // or a colour present exactly once (so swapping with c1 won't create a new c2-conflict).
    std::vector<int> candidate_c2_colours_list;
    for (int c = 1; c <= sg.G_max_degree; ++c) {  // Iterate through all possible colours
        if (c != c1) {                            // c2 must be different from c1
            // Colour c is not present at u OR colour c is present exactly once
            if (!incident_colours_at_u_vec[c]) {
                candidate_c2_colours_list.push_back(c);
            } else if (colour_counts_at_u_vec[c] == 1) {
                candidate_c2_colours_list.push_back(c);
            }
        }
    }
    // Fallback: if no such c2, pick any colour different from c1
    // (This happens if all other colours are involved in multiple conflicts or absent,
    //  which is rare but possible if G_max_degree is small, e.g., 2)
    if (candidate_c2_colours_list.empty() && sg.G_max_degree > 1) {
        for (int c = 1; c <= sg.G_max_degree; ++c) {
            if (c != c1) {
                candidate_c2_colours_list.push_back(c);
            }
        }
    }

    if (candidate_c2_colours_list.empty()) {
        return false;  // No suitable c2 found
    }

    int c2;
    std::uniform_int_distribution<> dist_c2_idx(0, candidate_c2_colours_list.size() - 1);
    c2 = candidate_c2_colours_list[dist_c2_idx(g_rand)];

    // --- Kempe Chain Construction and Swap ---
    // A Kempe chain is a maximal connected component in the subgraph formed by
    // edges coloured with c1 or c2. We start from conflicting_edge_id (coloured c1).
    std::vector<int> kempe_chain_edges;
    std::set<int> visited_path_vertex_ids;  // Local to this Kempe chain operation

    int current_path_edge = conflicting_edge_id;  // Start with an edge coloured c1
    const auto& initial_endpoints = sg.edge_endpoints[conflicting_edge_id];
    int path_tip_vertex = (initial_endpoints.first == conflicting_vertex_id)
                              ? initial_endpoints.second
                              : initial_endpoints.first;
    int colour_to_search_for_next = c2;
    int kempe_path_len = 0;

    while (kempe_path_len < sg.num_vertices + 5) {
        // Traverse the alternating path of c1 and c2 edges
        kempe_chain_edges.push_back(current_path_edge);
        kempe_path_len++;
        if (path_tip_vertex == conflicting_vertex_id) {
            break;  // Path looped back to the starting conflicting vertex u
        }
        if (visited_path_vertex_ids.count(path_tip_vertex)) {
            break;  // Visited this node before in the current path construction (cycle in path)
        }
        visited_path_vertex_ids.insert(path_tip_vertex);
        // Early exit condition from Fiol & Vilaltella:
        // if the path reaches another conflicting vertex, stop.
        if (conflict_state.current_levels[path_tip_vertex] > 0) {
            break;
        }

        int next_path_edge = -1;
        for (int i = 0; i < sg.degree[path_tip_vertex]; ++i) {
            int candidate_path_edge = sg.adj_edge_ids[path_tip_vertex][i];
            if (candidate_path_edge != current_path_edge &&
                sg.edge_colours[candidate_path_edge] == colour_to_search_for_next) {
                next_path_edge = candidate_path_edge;
                break;
            }
        }
        if (next_path_edge == -1) {
            break;  // No edge with the required colour to continue the chain
        }

        const auto& next_endpoints = sg.edge_endpoints[next_path_edge];
        // Determine the new tip of the path (the other endpoint of next_path_edge)
        int next_path_tip_vertex = (next_endpoints.first == path_tip_vertex) ? next_endpoints.second
                                                                             : next_endpoints.first;
        current_path_edge = next_path_edge;
        path_tip_vertex = next_path_tip_vertex;
        colour_to_search_for_next = (colour_to_search_for_next == c1) ? c2 : c1;
    }

    // Swap colours c1 and c2 along the identified Kempe chain
    std::set<int> affected_vertex_ids_in_swap;
    for (size_t i = 0; i < kempe_chain_edges.size(); ++i) {
        int edge_to_swap = kempe_chain_edges[i];
        int new_colour_for_e = (i % 2 == 0) ? c2 : c1;
        const auto& endpoints_to_affect = sg.edge_endpoints[edge_to_swap];
        affected_vertex_ids_in_swap.insert(endpoints_to_affect.first);
        affected_vertex_ids_in_swap.insert(endpoints_to_affect.second);
        sg.edge_colours[edge_to_swap] = new_colour_for_e;
    }

    // Update conflict levels for all vertices that were endpoints of edges in the chain
    for (int affected_vertex : affected_vertex_ids_in_swap) {
        conflict_state.update_vertex_state(affected_vertex, sg);
    }
    return true;  // Kempe chain operation performed
}

// Helper function containing the main iteration loop for CVD colouring
// The algorithm performs `iteration_limit` independent attempts (outer loop).
// Each attempt starts with a new random initial colouring.
// The inner `while` loop iteratively tries to reduce `total_conflicts` by
// performing Kempe chain operations on vertices with the highest conflict level.
static bool cvd_main_iteration_loop(
    SimpleCVDGraph& sg, int iteration_limit, int repetition_limit, std::mt19937& g_rand
) {
    const int max_inner_loop_steps =
        sg.num_vertices * sg.num_vertices * std::max(1, sg.G_max_degree) + 1000;

    // Outer loop: Each iteration is a fresh attempt to find a colouring.
    for (int iter = 0; iter < iteration_limit; ++iter) {
        initialize_random_edge_colouring(sg, g_rand);
        // After initial colouring, calculate conflicts.
        ConflictState conflict_state(sg.num_vertices, sg.G_max_degree);
        conflict_state.initialize(sg);

        if (conflict_state.total_conflicts_val == 0) {
            return true;  // Graph is colourable
        }

        int current_repetition_counter = 0;
        int previous_total_conflicts = conflict_state.total_conflicts_val;
        int inner_loop_step_count = 0;

        // Inner loop: Iteratively reduce conflicts using Kempe chain operations.
        while (conflict_state.total_conflicts_val > 0) {
            if (inner_loop_step_count++ > max_inner_loop_steps) {  // Safety break for inner loop
                break;
            }

            int highest_cl = 0;
            // Find the highest conflict level currently present in the graph.
            // Iterate from G_max_degree-1 down to 1.
            for (int cl_check = sg.G_max_degree - 1; cl_check >= 1;
                 --cl_check) {  // sg.G_max_degree is conflict_state.G_max_degree_cache
                if (cl_check < static_cast<int>(conflict_state.dict_array.size()) &&
                    !conflict_state.dict_array[cl_check].empty()) {
                    highest_cl = cl_check;
                    break;
                }
            }

            if (highest_cl == 0) {
                // This case should ideally be caught by total_conflicts == 0.
                // If conflict_dict is empty but total_conflicts > 0, it's an inconsistency or stuck
                // state.
                int check_conflicts = 0;
                for (int cl_val : conflict_state.current_levels) {
                    check_conflicts += cl_val;
                }
                conflict_state.total_conflicts_val =
                    check_conflicts;  // Correct the total_conflicts_val
                if (conflict_state.total_conflicts_val ==
                    0) {  // Successfully coloured in this iteration
                    break;
                } else {
                    throw std::runtime_error(
                        "CVD: conflict dictionary is empty but total_conflicts_val = " +
                        std::to_string(conflict_state.total_conflicts_val)
                    );
                }
            }

            // Select a vertex randomly from those with the highest conflict level.
            const std::vector<int>& highest_conflict_vertices_vec =
                conflict_state.dict_array[highest_cl];

            std::uniform_int_distribution<> dist_vertex_idx(
                0, highest_conflict_vertices_vec.size() - 1
            );
            int conflicting_vertex_id = highest_conflict_vertices_vec[dist_vertex_idx(g_rand)];

            bool kempe_step_performed =
                perform_kempe_chain_step(sg, conflicting_vertex_id, conflict_state, g_rand);

            if (!kempe_step_performed) {  // Kempe step failed (e.g., no c1 or c2)
                current_repetition_counter++;
                if (current_repetition_counter > repetition_limit) {  // Stuck
                    break;
                }
                previous_total_conflicts =
                    conflict_state.total_conflicts_val;  // Update for next comparison
                continue;  // Try another conflicting vertex or restart if stuck
            }

            if (conflict_state.total_conflicts_val == 0) {
                return true;  // Graph is colourable
            }
            // Check if colouring is complete after Kempe step

            // Check for stagnation: if total conflicts haven't decreased.
            if (conflict_state.total_conflicts_val >= previous_total_conflicts) {
                current_repetition_counter++;
                // If stagnated for too long, break this inner attempt and try a new initial
                // colouring.
                if (current_repetition_counter > repetition_limit) {
                    // Exceeded repetition limit without improvement, break inner loop
                    // This will lead to a new outer iteration or failure if iteration_limit is
                    // reached.
                    break;
                }
            } else {
                current_repetition_counter = 0;
                // Reset repetition counter if progress was made.
            }
            previous_total_conflicts = conflict_state.total_conflicts_val;
        }
    }
    return false;  // No colouring found after all iterations
}

}  // end namespace cvd_internal

// Main CVD (conflicting vertex displacement) edge colouring heuristic.
// Attempts to find a Delta-edge-colouring (using G_orig_max_degree colours).
// Parameters:
//   G: The graph to colour.
//   iteration_limit_param: Number of independent attempts with new random initial colourings.
//   repetition_limit_param: Max number of consecutive Kempe steps without reducing total conflicts.
//   seed: Seed for the random number generator.
inline bool has_cvd_edge_colouring_general(
    const Graph& G, int iteration_limit_param = -1, int repetition_limit_param = -1, int seed = -1
) {
    if (G.order() == 0) {
        return true;  // Empty graph is trivially coloured.
    }

    int G_orig_max_degree = ba_graph::max_deg(G);
    // Note: The condition (G_orig_max_degree == 0 && G.size() > 0) is likely always false.
    // If a graph has edges (G.size() > 0), its maximum degree cannot be 0.
    // This line is kept for consistency with original code or as a safeguard for an unexpected
    // state.
    if (G_orig_max_degree == 0 && G.size() > 0) {
        throw std::runtime_error("has_cvd_edge_colouring: graph has edges but max_degree is 0");
    }
    if (G_orig_max_degree == 0) {
        return true;  // No edges, trivially coloured.
    }

    if (G_orig_max_degree >= 64) {
        throw std::runtime_error(
            "CVD edge colouring: maximum degree " + std::to_string(G_orig_max_degree) +
            " is too high (>= 64). Algorithm optimized for degree < 64."
        );
    }

    // Set default limits if not provided.
    int repetition_limit = repetition_limit_param;
    if (repetition_limit == -1) {
        if (G.size() == 0) {
            repetition_limit = 1;
        } else {
            repetition_limit = static_cast<int>(sqrt(G.size())) + 1;
        }
    }
    int iteration_limit = iteration_limit_param;
    if (iteration_limit == -1) {
        iteration_limit = 64;
    }

    // Convert to internal simplified graph representation.
    cvd_internal::SimpleCVDGraph sg(G, G_orig_max_degree);
    if (sg.num_edges == 0) {
        return true;  // No edges in the simplified graph.
    }

    // Initialize random number generator.
    // Using a fixed seed allows for reproducible results.
    std::mt19937 g_rand;
    if (seed == -1) {
        std::random_device rd;
        g_rand.seed(rd());
    } else {
        g_rand.seed(static_cast<unsigned int>(seed));
    }

    // Start the main iterative colouring process.
    return cvd_internal::cvd_main_iteration_loop(sg, iteration_limit, repetition_limit, g_rand);
}

/**
 * @brief Unified CVD edge colouring function that automatically selects the best variant.
 *
 * This function automatically chooses the appropriate CVD heuristic based on the graph's
 * regularity:
 * - For 3-regular graphs: uses has_cvd_edge_colouring_3regular
 * - For 4-regular graphs: uses has_cvd_edge_colouring_4regular
 * - For all other graphs: uses has_the general has_cvd_edge_colouring
 *
 * @param G The graph to color
 * @param iteration_limit_param Number of independent attempts (-1 for default)
 * @param repetition_limit_param Max consecutive steps without improvement (-1 for default)
 * @param seed Random seed (-1 for random seed)
 * @return true if a valid edge coloring exists, false otherwise
 */
inline bool has_cvd_edge_colouring(
    const Graph& G, int iteration_limit_param = -1, int repetition_limit_param = -1, int seed = -1
) {
    if (is_d_regular(G, 3)) {
        return has_cvd_edge_colouring_3regular(
            G, iteration_limit_param, repetition_limit_param, seed
        );
    }

    if (is_d_regular(G, 4)) {
        return has_cvd_edge_colouring_4regular(
            G, iteration_limit_param, repetition_limit_param, seed
        );
    }

    // General case
    return has_cvd_edge_colouring_general(G, iteration_limit_param, repetition_limit_param, seed);
}

}  // namespace ba_graph

#endif  // BA_GRAPH_INVARIANTS_COLOURING_CVD_HPP
