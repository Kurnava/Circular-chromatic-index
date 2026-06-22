#ifndef BA_GRAPH_INVARIANTS_COLOURING_CVD_4REGULAR_HPP
#define BA_GRAPH_INVARIANTS_COLOURING_CVD_4REGULAR_HPP

#include <algorithm>  // For std::shuffle, std::fill, std::max (though std::max not explicitly used here, often useful)
#include <array>  // For std::array
#include <cmath>  // For sqrt
#include <map>
#include <numeric>  // For std::iota
#include <random>   // For std::random_device, std::mt19937, std::uniform_int_distribution
#include <utility>  // For std::pair
#include <vector>

// Project-specific headers
#include "graphs/basic.hpp"  // For ba_graph::Graph, Vertex, Edge

namespace ba_graph {  // Ensure public function is in the main namespace

// This namespace encapsulates the internal implementation details of the
// Fiol-Vilaltella CVD (conflicting vertex displacement) heuristic,
// specifically adapted and optimized for 4-regular graphs.
// The algorithm attempts to find a 4-edge-colouring.
namespace ba_graph_cvd_internal_4reg {

const int DEGREE = 4;
// Mask representing all colours {1, 2, 3, 4} -> bits 0, 1, 2, 3 set -> 1+2+4+8 = 15 (0xF)
// This is used for efficient bitwise operations on sets of colours.
const int ALL_COLOURS_MASK_4REG = (1 << DEGREE) - 1;

// Population count (number of set bits)
// Counts how many '1's are in the binary representation of an integer.
// Using __builtin_popcount if available (GCC/Clang) for performance
#if defined(__GNUC__) || defined(__clang__)
inline int popcount(unsigned int n) { return __builtin_popcount(n); }
#else
// Software fallback for popcount
inline int popcount(unsigned int n) {
    int count = 0;
    while (n > 0) {
        n &= (n - 1);
        count++;
    }
    return count;
}
#endif

// Simplified graph structure for internal CVD operations.
// This structure is used to represent the graph in a way that is more
// convenient for the colouring algorithm, using integer IDs for vertices and edges,
// and storing adjacency information directly. For this specialization, G_max_degree is
// implicitly 4.
struct SimpleCVDGraph {
    int num_vertices;
    int num_edges;

    std::vector<std::array<int, DEGREE>> adj;
    std::vector<std::array<int, DEGREE>> adj_edge_ids;
    std::vector<int> edge_colours;
    std::map<ba_graph::Vertex, int> vertex_to_int_id;
    std::vector<std::pair<int, int>> edge_endpoints;

    // Constructor: Converts a ba_graph::Graph object into the SimpleCVDGraph representation.
    // It maps original Vertex objects to integer IDs (0 to num_vertices-1),
    // builds adjacency lists (adj) and lists of incident edge IDs (adj_edge_ids).
    // It also populates edge_endpoints, storing the pair of (integer) vertex IDs for each edge ID.
    // This conversion facilitates faster lookups and iterations during the colouring process.
    SimpleCVDGraph(const ba_graph::Graph& G) {
        num_vertices = G.order();
        adj.resize(num_vertices);
        adj_edge_ids.resize(num_vertices);

        int current_vertex_id_counter = 0;
        // Populate vertex_to_int_id map directly
        for (const auto& r_it : G) {
            ba_graph::Vertex orig_v = r_it.v();
            vertex_to_int_id[orig_v] = current_vertex_id_counter++;
        }

        int current_edge_id_counter = 0;
        std::map<ba_graph::Edge, int> temp_orig_edge_to_id;
        // Pre-allocate simple_edge_endpoints if G.size() is a good estimate for the number of
        // edges.
        if (G.size() > 0) {                    // G.size() from ba_graph::Graph
            edge_endpoints.reserve(G.size());  // Reserve, will grow if needed
        }

        for (const auto& r_it : G) {
            int u_id = vertex_to_int_id.at(r_it.v());
            // In a 4-regular graph, degree is guaranteed by the calling function's check.
            assert(r_it.degree() == DEGREE);

            int neighbor_idx = 0;
            for (const auto& inc : r_it) {
                ba_graph::Edge orig_e = inc.e();
                ba_graph::Vertex orig_neighbor_v = inc.v2();
                int v_id = vertex_to_int_id.at(orig_neighbor_v);
                adj[u_id][neighbor_idx] = v_id;
                auto map_find_res = temp_orig_edge_to_id.find(orig_e);
                int edge_id;
                if (map_find_res == temp_orig_edge_to_id.end()) {
                    edge_id = current_edge_id_counter++;
                    temp_orig_edge_to_id[orig_e] = edge_id;
                    // Grow simple_edge_endpoints directly
                    if (edge_id >= static_cast<int>(edge_endpoints.size())) {
                        edge_endpoints.resize(edge_id + 128);  // Or a different growth factor
                    }
                    edge_endpoints[edge_id] = {u_id, v_id};
                } else {
                    edge_id = map_find_res->second;
                }
                adj_edge_ids[u_id][neighbor_idx] = edge_id;
                neighbor_idx++;
            }
        }
        num_edges = current_edge_id_counter;
        edge_colours.assign(num_edges, 0);
        // Shrink simple_edge_endpoints to actual number of unique edges
        edge_endpoints.resize(num_edges);
    }
};

// Helper function to calculate conflict level for a vertex in SimpleCVDGraph (4-regular specific).
// The conflict level of a vertex 'u' is defined as deg(u) - d(u),
// where deg(u) is the degree of u (expected to be 4 for internal vertices of a 4-regular graph),
// and d(u) is the number of distinct colours used on edges incident to u.
// A conflict level of 0 means the vertex is properly coloured (all incident edges have distinct
// colours). This version uses bitmasks for efficient calculation with up to 4 colours.
static int calculate_conflict_level_4reg(int u_id, const SimpleCVDGraph& sg) {
    // For a non-empty 4-regular graph, degree[u_id] is DEGREE (4).
    // If sg.num_vertices is 0, this function won't be called for any u_id.
    unsigned int incident_colours_mask = 0;
    for (int i = 0; i < DEGREE; ++i) {  // Iterate DEGREE times
        int edge_id = sg.adj_edge_ids[u_id][i];
        if (edge_id < 0 || edge_id >= sg.num_edges) {
            throw std::runtime_error(
                "calculate_conflict_level_4reg: out-of-bounds edge_id " + std::to_string(edge_id) +
                " for vertex " + std::to_string(u_id)
            );
        }
        int colour = sg.edge_colours[edge_id];
        if (colour >= 1 && colour <= DEGREE) {
            incident_colours_mask |= (1 << (colour - 1));
        }
    }
    return DEGREE - popcount(incident_colours_mask);
}

// Structure to manage the conflict state of the graph during 4-regular CVD.
// It encapsulates the conflict dictionary, current conflict levels per vertex,
// positions for O(1) updates, and the total sum of conflicts.
struct ConflictState4Reg {
    std::vector<std::vector<int>>
        dict_array;                   // dict_array[cl] stores vertices with conflict level cl
    std::vector<int> current_levels;  // current_levels[u_id] stores conflict level of vertex u_id
    std::vector<int> positions_in_list;  // positions_in_list[u_id] stores index of u_id in
                                         // dict_array[current_levels[u_id]]
    int total_conflicts_val;             // Sum of all conflict levels

    ConflictState4Reg(int num_vertices)
        : total_conflicts_val(0) {
        // Conflict level ranges [0, DEGREE]. dict_array needs size DEGREE + 1.
        dict_array.assign(DEGREE + 1, std::vector<int>());
        current_levels.assign(num_vertices, 0);
        positions_in_list.assign(num_vertices, -1);
    }

    // Initializes the conflict state based on the current edge colouring of sg.
    void initialize(const SimpleCVDGraph& sg) {
        total_conflicts_val = 0;
        for (auto& list : dict_array) {
            list.clear();
        }  // Clear old data
        std::fill(current_levels.begin(), current_levels.end(), 0);
        std::fill(positions_in_list.begin(), positions_in_list.end(), -1);

        for (int u_id = 0; u_id < sg.num_vertices; ++u_id) {
            int cl = calculate_conflict_level_4reg(u_id, sg);
            current_levels[u_id] = cl;
            if (cl > 0) {
                if (cl < static_cast<int>(dict_array.size())) {  // cl <= DEGREE
                    dict_array[cl].push_back(u_id);
                    positions_in_list[u_id] = dict_array[cl].size() - 1;
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
                if (!v_list.empty()) {
                    int pos_of_u_to_remove = positions_in_list[u_id];
                    if (pos_of_u_to_remove < static_cast<int>(v_list.size()) &&
                        v_list[pos_of_u_to_remove] == u_id) {
                        int last_vertex_in_list = v_list.back();
                        if (u_id != last_vertex_in_list) {
                            v_list[pos_of_u_to_remove] = last_vertex_in_list;
                            positions_in_list[last_vertex_in_list] = pos_of_u_to_remove;
                        }
                        v_list.pop_back();
                    }
                }
            }
        }
        total_conflicts_val -= old_cl;
        int new_cl = calculate_conflict_level_4reg(u_id, sg);
        current_levels[u_id] = new_cl;
        if (new_cl > 0) {
            if (new_cl < static_cast<int>(dict_array.size())) {
                dict_array[new_cl].push_back(u_id);
                positions_in_list[u_id] = dict_array[new_cl].size() - 1;
            }
        }
        total_conflicts_val += new_cl;
    }
};

// Helper function for the initial random colouring of edges (4-regular specific).
// This function assigns an initial colour (1-4) to each edge of the graph.
// The process is:
// 1. Iterate through all edges in a random order (shuffled `local_edge_shuffling_indices`).
// 2. For each edge (u,v):
//    a. Identify colours already used by other edges incident to u or v (forbidden colours).
//    b. Greedily pick the smallest available colour (1-4) not in the forbidden set.
//    c. If all 4 colours are forbidden (should be rare if aiming for a Delta-colouring), assign a
//    random colour (1-4).
// This creates a partially "good" starting point for the iterative improvement phase.
static void initialize_random_edge_colouring_4reg(SimpleCVDGraph& sg, std::mt19937& g_rand) {
    std::vector<int> shuffled_edge_ids(sg.num_edges);
    std::iota(shuffled_edge_ids.begin(), shuffled_edge_ids.end(), 0);
    std::shuffle(shuffled_edge_ids.begin(), shuffled_edge_ids.end(), g_rand);

    std::fill(sg.edge_colours.begin(), sg.edge_colours.end(), 0);  // Reset all colours

    for (int edge_id : shuffled_edge_ids) {
        if (edge_id < 0 || edge_id >= sg.num_edges) {
            throw std::runtime_error(
                "initialize_random_edge_colouring_4reg: out-of-bounds edge_id " +
                std::to_string(edge_id)
            );
        }
        const auto& endpoints = sg.edge_endpoints[edge_id];
        int u_id = endpoints.first;
        int v_id = endpoints.second;

        unsigned int forbidden_colours_mask = 0;
        // Colours at u_id
        for (int i = 0; i < DEGREE; ++i) {
            int incident_edge_id = sg.adj_edge_ids[u_id][i];
            if (incident_edge_id != edge_id && sg.edge_colours[incident_edge_id] != 0) {
                int colour = sg.edge_colours[incident_edge_id];
                if (colour >= 1 && colour <= DEGREE) {
                    forbidden_colours_mask |= (1 << (colour - 1));
                }
            }
        }
        // Colours at v_id
        for (int i = 0; i < DEGREE; ++i) {
            int incident_edge_id = sg.adj_edge_ids[v_id][i];
            if (incident_edge_id != edge_id && sg.edge_colours[incident_edge_id] != 0) {
                int colour = sg.edge_colours[incident_edge_id];
                if (colour >= 1 && colour <= DEGREE) {
                    forbidden_colours_mask |= (1 << (colour - 1));
                }
            }
        }

        int chosen_colour = 0;
        bool found_colour = false;
        for (int c = 1; c <= DEGREE; ++c) {
            if (!(forbidden_colours_mask & (1 << (c - 1)))) {
                chosen_colour = c;
                found_colour = true;
                break;
            }
        }
        if (!found_colour) {
            chosen_colour = std::uniform_int_distribution<>(1, DEGREE)(g_rand);
        }
        sg.edge_colours[edge_id] = chosen_colour;
    }
}

// Helper function to perform one Kempe chain step (4-regular specific).
// This is the core iterative improvement mechanism of the CVD algorithm.
// Given a `u_conflicting_id` (a vertex with non-zero conflict level):
// 1. Identify a colour `c1`: This colour must be involved in the conflict at `u_conflicting_id`,
//    meaning `c1` is present on at least two edges incident to `u_conflicting_id`.
//    An edge `conflicting_edge_id` coloured `c1` is chosen to start the chain.
// 2. Choose a colour `c2`: This colour must be different from `c1`. Ideally, `c2` is
//    either not present on any edge incident to `u_conflicting_id`, or present on exactly one.
//    This choice aims to reduce the conflict at `u_conflicting_id` after the swap.
// 3. Construct a Kempe chain:
//    A Kempe chain is a maximal path/cycle of edges alternating in colours `c1` and `c2`,
//    starting from `conflicting_edge_id`. The chain extends from `u_conflicting_id`'s neighbor
//    along `conflicting_edge_id`.
//    The chain stops if it loops back, revisits a vertex, reaches another conflicting vertex
//    (heuristic), or cannot extend.
// 4. Swap colours: Along all edges in the identified Kempe chain, swap `c1` with `c2` and
// vice-versa.
//    This operation is "safe" in that it doesn't create new conflicts outside the chain's
//    endpoints.
// 5. Update conflicts: Recalculate conflict levels for all vertices that were endpoints of edges in
// the chain.
static bool perform_kempe_chain_step_4reg(
    SimpleCVDGraph& sg, int u_conflicting_id, ConflictState4Reg& conflict_state,
    std::mt19937& g_rand
) {
    int conflicting_edge_id = -1;
    int c1 = 0;
    // Use bitmask for incident colours and a vector for counts at u_conflicting_id
    unsigned int incident_colours_mask_at_u = 0;
    std::vector<int> colour_counts_at_u_vec(DEGREE + 1, 0);

    for (int i = 0; i < DEGREE; ++i) {
        int current_edge_id = sg.adj_edge_ids[u_conflicting_id][i];
        if (current_edge_id < 0 || current_edge_id >= sg.num_edges) {
            throw std::runtime_error(
                "perform_kempe_chain_step_4reg: out-of-bounds edge_id " +
                std::to_string(current_edge_id) + " for vertex " + std::to_string(u_conflicting_id)
            );
        }
        int c_val = sg.edge_colours[current_edge_id];
        if (c_val == 0) {
            continue;
        }
        if (c_val >= 1 && c_val <= DEGREE) {
            incident_colours_mask_at_u |= (1 << (c_val - 1));
            colour_counts_at_u_vec[c_val]++;  // Count occurrences of each colour
            // If a colour appears more than once, it's a conflicting colour (c1).
            // Pick the first such colour and one of its edges.
            if (colour_counts_at_u_vec[c_val] > 1 && conflicting_edge_id == -1) {
                conflicting_edge_id = current_edge_id;
                c1 = c_val;
            }
        }
    }
    if (conflicting_edge_id == -1 || c1 == 0) {  // No conflicting colour c1 found
        return false;
    }

    // Find a candidate colour c2 for the Kempe chain.
    std::vector<int> candidate_c2_colours_list;
    for (int c = 1; c <= DEGREE; ++c) {
        if (c == c1) {
            continue;
        }
        unsigned int c_mask_bit = (1 << (c - 1));
        if (!(incident_colours_mask_at_u & c_mask_bit)) {
            candidate_c2_colours_list.push_back(c);
        } else if (colour_counts_at_u_vec[c] == 1) {
            candidate_c2_colours_list.push_back(c);
        }
    }
    // Fallback: if no ideal c2, pick any colour different from c1.
    if (candidate_c2_colours_list.empty() && DEGREE > 1) {
        for (int c = 1; c <= DEGREE; ++c) {
            if (c != c1) {
                candidate_c2_colours_list.push_back(c);
            }
        }
    }
    if (candidate_c2_colours_list.empty()) {
        return false;
    }  // No suitable c2 found

    int c2;
    std::uniform_int_distribution<> dist_c2_idx(0, candidate_c2_colours_list.size() - 1);
    c2 = candidate_c2_colours_list[dist_c2_idx(g_rand)];

    // --- Kempe Chain Construction and Swap ---
    std::vector<int> kempe_chain_edges;
    // `visited_path_vertex_ids_vec_local` tracks vertices visited *during the construction of this
    // specific chain* to detect cycles in the alternating path construction.
    std::vector<bool> visited_path_vertex_ids_vec_local(
        sg.num_vertices,
        false
    );  // Local visited set for this chain
    int kempe_path_len = 0;

    int current_path_edge = conflicting_edge_id;
    const auto& initial_endpoints = sg.edge_endpoints[conflicting_edge_id];
    // `current_path_tip_vertex` is the vertex at the "growing end" of the Kempe chain.
    int current_path_tip_vertex = (initial_endpoints.first == u_conflicting_id)
                                      ? initial_endpoints.second
                                      : initial_endpoints.first;
    int next_path_colour = c2;  // The colour we are looking for on the next edge in the chain.

    // Loop to build the Kempe chain.
    // The chain length is bounded by num_vertices + 5 as a safety measure.
    while (kempe_path_len < sg.num_vertices + 5) {
        kempe_chain_edges.push_back(current_path_edge);
        kempe_path_len++;
        // Termination conditions for chain construction:
        if (current_path_tip_vertex ==
            u_conflicting_id) {  // Path looped back to the starting conflicting vertex u
            break;
        }
        if (visited_path_vertex_ids_vec_local[current_path_tip_vertex]) {
            break;
        }
        visited_path_vertex_ids_vec_local[current_path_tip_vertex] = true;
        if (conflict_state.current_levels[current_path_tip_vertex] > 0) {
            break;
        }

        int next_path_edge = -1;
        std::vector<int> next_edge_candidates_list;
        for (int i = 0; i < DEGREE; ++i) {
            // Look for an edge incident to `current_path_tip_vertex` (that isn't
            // `current_path_edge` itself) and has the colour `next_path_colour`.
            int candidate_path_edge = sg.adj_edge_ids[current_path_tip_vertex][i];
            if (candidate_path_edge != current_path_edge &&
                sg.edge_colours[candidate_path_edge] == next_path_colour) {
                next_edge_candidates_list.push_back(candidate_path_edge);
            }
        }
        if (next_edge_candidates_list.empty()) {
            break;
        }

        // If multiple edges fit, pick one randomly (helps explore different chains).
        if (next_edge_candidates_list.size() == 1) {
            next_path_edge = next_edge_candidates_list[0];
        } else {
            std::uniform_int_distribution<> dist_edge_cand(0, next_edge_candidates_list.size() - 1);
            next_path_edge = next_edge_candidates_list[dist_edge_cand(g_rand)];
        }

        // Advance the chain: update current edge, tip vertex, and the colour to search for next.
        const auto& next_endpoints = sg.edge_endpoints[next_path_edge];
        current_path_tip_vertex = (next_endpoints.first == current_path_tip_vertex)
                                      ? next_endpoints.second
                                      : next_endpoints.first;
        current_path_edge = next_path_edge;
        next_path_colour = (next_path_colour == c1) ? c2 : c1;
    }

    // Swap colours c1 and c2 along the identified Kempe chain.
    // Edges are swapped alternatingly: first edge gets c2, second c1, third c2, etc.
    std::set<int> affected_vertices_in_swap;
    for (size_t i = 0; i < kempe_chain_edges.size(); ++i) {
        int edge_to_swap = kempe_chain_edges[i];
        int new_colour_for_e = (i % 2 == 0) ? c2 : c1;  // If edge was c1 (i = 0), it becomes c2. If
                                                        // it was c2 (i = 1), it becomes c1.
        const auto& endpoints_to_affect = sg.edge_endpoints[edge_to_swap];
        affected_vertices_in_swap.insert(endpoints_to_affect.first);
        affected_vertices_in_swap.insert(endpoints_to_affect.second);
        sg.edge_colours[edge_to_swap] = new_colour_for_e;
    }

    for (int affected_vertex : affected_vertices_in_swap) {
        // Update conflict levels for all vertices that were endpoints of edges in the chain.
        conflict_state.update_vertex_state(affected_vertex, sg);
    }
    return true;
}

// Helper function containing the main iteration loop for CVD colouring (4-regular specific).
// The algorithm performs `iteration_limit` independent attempts (outer loop).
// Each attempt starts with a new random initial colouring. This is because the
// heuristic can get stuck in local optima.
// The inner `while` loop iteratively tries to reduce `total_conflicts` by
// performing Kempe chain operations. It picks a vertex with the highest
// current conflict level and attempts a Kempe chain swap.
// If `total_conflicts` reaches 0, a valid 4-edge-colouring is found.
// Stagnation (no improvement for `repetition_limit` steps) causes the inner loop to break.
static bool cvd_main_iteration_loop_4reg(
    SimpleCVDGraph& sg, int iteration_limit, int repetition_limit, std::mt19937& g_rand
) {
    const int max_inner_loop_steps = sg.num_vertices * sg.num_vertices * DEGREE + 1000;

    // Outer loop: Each iteration is a fresh attempt to find a colouring.
    for (int iter = 0; iter < iteration_limit; ++iter) {
        initialize_random_edge_colouring_4reg(sg, g_rand);

        ConflictState4Reg conflict_state(sg.num_vertices);
        conflict_state.initialize(sg);

        if (conflict_state.total_conflicts_val == 0) {
            return true;
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
            // Iterate from max possible conflict (3 for 4-regular) down to 1.
            for (int cl_check = DEGREE - 1; cl_check >= 1; --cl_check) {
                if (cl_check < static_cast<int>(conflict_state.dict_array.size()) &&
                    !conflict_state.dict_array[cl_check].empty()) {
                    highest_cl = cl_check;
                    break;
                }
            }

            // If highest_cl is 0, it implies total_conflicts should be 0.
            // This block is a safeguard or handles potential inconsistencies.
            if (highest_cl == 0) {
                int check_conflicts = 0;
                for (int cl_val : conflict_state.current_levels) {
                    check_conflicts += cl_val;
                }
                conflict_state.total_conflicts_val =
                    check_conflicts;  // Correct the total_conflicts_val
                if (conflict_state.total_conflicts_val == 0) {
                    break;
                } else {
                    throw std::runtime_error(
                        "CVD 4-regular: conflict dictionary is empty but total_conflicts_val = " +
                        std::to_string(conflict_state.total_conflicts_val)
                    );
                }
            }

            // Select a vertex randomly from those with the `highest_cl`.
            const std::vector<int>& highest_conflict_vertices_vec =
                conflict_state.dict_array[highest_cl];
            std::uniform_int_distribution<> dist_vertex_idx(
                0, highest_conflict_vertices_vec.size() - 1
            );
            int u_conflicting_id = highest_conflict_vertices_vec[dist_vertex_idx(g_rand
            )];  // Vertex to apply Kempe chain on

            bool kempe_step_performed =
                perform_kempe_chain_step_4reg(sg, u_conflicting_id, conflict_state, g_rand);

            if (!kempe_step_performed) {
                // Kempe step failed (e.g., couldn't find c1 or c2).
                current_repetition_counter++;
                if (current_repetition_counter > repetition_limit) {  // Stuck for too long
                    break;
                }
                previous_total_conflicts =
                    conflict_state.total_conflicts_val;  // Update for next comparison
                continue;
            }

            if (conflict_state.total_conflicts_val == 0) {  // Successfully coloured
                break;
            }

            // Check for stagnation: if total conflicts haven't decreased.
            if (conflict_state.total_conflicts_val >= previous_total_conflicts) {
                current_repetition_counter++;
                // If stagnated for too long, break this inner attempt.
                if (current_repetition_counter > repetition_limit) {
                    break;
                }
            } else {
                current_repetition_counter = 0;
            }
            previous_total_conflicts = conflict_state.total_conflicts_val;
        }
        if (conflict_state.total_conflicts_val == 0) {  // Colouring found in this iteration
            return true;
        }
    }
    return false;  // No colouring found
}

}  // end namespace ba_graph_cvd_internal_4reg

// has_cvd_edge_colouring_4regular
// Attempts to find a 4-edge-colouring for a given 4-regular graph `graph` using
// the Fiol-Vilaltella CVD (conflicting vertex displacement) heuristic.
// Parameters:
//   graph: The ba_graph::Graph object to colour. Assumed to be 4-regular or have max degree <= 4.
//   iteration_limit_param: Number of independent attempts with new random initial colourings.
//                          More iterations increase the chance of finding a colouring if one
//                          exists.
//   repetition_limit_param: Max number of consecutive Kempe steps without reducing total conflicts
//   within a single attempt.
//                           Helps to escape local optima or terminate non-productive searches.
//   seed: Seed for the random number generator, for reproducible results.
inline bool has_cvd_edge_colouring_4regular(
    const ba_graph::Graph& graph, int iteration_limit_param = -1, int repetition_limit_param = -1,
    int seed = -1
) {
    if (graph.order() == 0) {
        return true;  // Empty graph is trivially coloured.
    }

    // Check for strict 4-regularity. This function is specialized.
    bool is_strictly_4_regular = true;
    for (const auto& r_it : graph) {
        if (r_it.degree() != 4) {
            is_strictly_4_regular = false;
            break;
        }
    }

    if (!is_strictly_4_regular) {
        throw std::invalid_argument("has_cvd_edge_colouring_4regular: graph must be 4-regular");
    }

    // Set default limits if not provided by the user.
    int repetition_limit = repetition_limit_param;
    if (repetition_limit == -1) {
        repetition_limit = (graph.size() == 0) ? 1 : (static_cast<int>(sqrt(graph.size())) + 1);
    }
    int iteration_limit = iteration_limit_param;
    if (iteration_limit == -1) {
        int n = graph.order();
        iteration_limit = 1 + n * n / 4;  // Default number of restarts
    }

    // Convert to internal simplified graph representation.
    ba_graph_cvd_internal_4reg::SimpleCVDGraph sg(graph);
    if (sg.num_edges == 0) {  // No edges to colour.
        return true;
    }

    std::mt19937 g_rand;
    if (seed == -1) {
        std::random_device rd;
        g_rand.seed(rd());
    } else {
        g_rand.seed(static_cast<unsigned int>(seed));
    }

    // Start the main iterative colouring process.
    return ba_graph_cvd_internal_4reg::cvd_main_iteration_loop_4reg(
        sg, iteration_limit, repetition_limit, g_rand
    );
}

}  // namespace ba_graph

#endif  // BA_GRAPH_INVARIANTS_COLOURING_CVD_4REGULAR_HPP
