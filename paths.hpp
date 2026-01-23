#ifndef BA_GRAPH_ALGORITHM_PATHS_HPP
#define BA_GRAPH_ALGORITHM_PATHS_HPP

#include <algorithm>
#include <cassert>
#include <set>
#include <unordered_set>
#include <vector>

#include "../invariants/degree.hpp"
#include "../invariants/distance.hpp"
#include "../invariants/girth.hpp"
#include "../io/print_nice.hpp"
#include "../operations/copies.hpp"
#include "../operations/undo.hpp"

namespace ba_graph {

typedef std::vector<Number>
    PFPath;

// finds all possibilities how paths can go between the given pairs of endpoints
template <typename P>
class PathsFinder {
public:
    const Graph &G;
    bool (*callback)(std::vector<PFPath> paths, P *param);
    P *callbackParam;
    std::vector<std::pair<Number, Number>> endpoints;
    std::vector<Number> destinations;
    GraphNumberLabeling<bool> isDestination;

    std::vector<PFPath> paths;
    GraphNumberLabeling<bool> used;
    bool stopRecursion;

    PathsFinder(const Graph &G, bool (*callback)(std::vector<PFPath> paths, P *param))
        : G(G),
          callback(callback),
          isDestination(false, G),
          used(false, G) {}

    bool findPaths(std::vector<std::pair<Number, Number>> endpoints_, P *callbackParam_) {
#ifdef BA_GRAPH_DEBUG
        for (auto &p : endpoints_) {
            assert(G.contains(p.first));
            assert(G.contains(p.second));
        }
#endif
        // Handle empty endpoints: invoke callback with empty solution
        if (endpoints_.empty()) {
            if (callback != NULL) {
                if (!callback({}, callbackParam_)) {
                    return false;
                }
            }
            return true;
        }

        endpoints = endpoints_;
        callbackParam = callbackParam_;
        paths.clear();
        paths.resize(endpoints.size());
        for (auto &r : G) {
            used.set(r.n(), false);
            isDestination.set(r.n(), false);
        }
        for (auto &r : G) {
            int startIndex = -1;
            for (unsigned i = 0; i < endpoints.size(); ++i) {
                if (r.n() == endpoints[i].first) {
                    startIndex = i;
                    break;
                }
            }
            if (startIndex != -1) {
                if (used[r.n()]) {
                    return false;  // no desired paths exist
                }
                used.set(r.n(), true);
                paths[startIndex] = {r.n()};
            }
        }
        destinations.clear();
        for (unsigned i = 0; i < endpoints.size(); ++i) {
            // if the end is of degree one, we can mark its neighbour
            // as destination for the path so that other paths will avoid it
            // (if it is already marked, we have a contradiction)
            Number end = endpoints[i].second;
            Number destination = (G[end].degree() == 1) ? G[end].find(IP::all())->n2() : end;
            if (isDestination[destination]) {
                return false;  // no desired paths exist
            } else {
                isDestination.set(destination, true);
            }
            destinations.push_back(destination);
        }
        stopRecursion = false;
        return r(0);
    }

    inline bool complete(unsigned i) {
        assert(i < paths.size());
        return (!paths[i].empty()) && (paths[i].back() == endpoints[i].second);
    }

    inline bool allComplete() {
        for (unsigned j = 0; j < paths.size(); ++j) {
            if (!complete(j)) {
                return false;
            }
        }
        return true;
    }

    bool r(int pathToAugment) {
        if (stopRecursion) {
            return false;
        }
        unsigned i = pathToAugment;
        if (!complete(i)) {
            // we try to augment the i-th path
            Number lastV = paths[i].back();
            bool pathsExist = false;
            for (auto &inc : G[lastV]) {
                Number v = inc.n2();
                if (used[v.to_int()]) {
                    continue;  // do not visit a vertex twice
                }
                if (isDestination[v.to_int()] && (v.to_int() != destinations[i])) {
                    continue;  // using other paths' destination leads to a contradition
                }
                if (isDestination[lastV] && (v.to_int() != endpoints[i].second)) {
                    continue;  // if we are in the destination, only go to the end, not elsewhere
                }
                paths[i].push_back(v);
                used.set(v.to_int(), true);
                int result = r((i + 1) % paths.size());
                pathsExist = pathsExist || result;
                used.set(v.to_int(), false);
                paths[i].pop_back();
            }
            return pathsExist;
        } else if (allComplete()) {
            if (callback != NULL) {
                if (!callback(paths, callbackParam)) {
                    stopRecursion = true;
                }
            }
            return true;
        } else {  // i-th path is complete, but some other path is not
            return r((i + 1) % paths.size());
        }
    }
};

namespace internal {

struct MinimumUncoveredVerticesCallbackData {
    const Graph *G;
    std::set<Number> *ignored;
    int minimumUncoveredVertices;
};

inline bool minimum_uncovered_vertices_callback(
    std::vector<PFPath> paths, struct MinimumUncoveredVerticesCallbackData *cbData
) {
    int result = cbData->G->order();
    GraphNumberLabeling<bool> covered(false, *cbData->G);
    for (auto path : paths) {
        result -= path.size();
        for (auto v : path) {
            covered.set(v, true);
        }
    }
    for (auto u : *cbData->ignored) {
        if (!covered[u]) {
            result--;
        }
    }
    cbData->minimumUncoveredVertices = std::min(cbData->minimumUncoveredVertices, result);
    return cbData->minimumUncoveredVertices > 0;  // no need to continue if we can cover all
}

}  // namespace internal

// ignored: will not be counted among uncovered, useful for terminals
inline int minimum_uncovered_vertices(
    const Graph &G, std::vector<std::pair<Number, Number>> endpoints, std::set<Number> ignored = {}
) {
#ifdef BA_GRAPH_DEBUG
    for (auto &p : endpoints) {
        assert(G.contains(p.first));
        assert(G.contains(p.second));
    }
    for (auto &v : ignored) {
        assert(G.contains(v));
    }
#endif
    struct internal::MinimumUncoveredVerticesCallbackData cbData;
    cbData.G = &G;
    cbData.ignored = &ignored;
    cbData.minimumUncoveredVertices = G.order();

    PathsFinder pf(G, internal::minimum_uncovered_vertices_callback);
    pf.findPaths(endpoints, &cbData);
    return cbData.minimumUncoveredVertices;
}

// if ignoreIsolated, we only check for Hamiltonian cycle
// in the graph obtained from G by deleting isolated vertices
inline int is_hamiltonian_basic(const Graph &G, bool ignoreIsolated = false) {
    if (G.order() == 0) {
        return true;
    }
    if (G.order() == 1) {
        return has_loop(G);
    }
    if (G.order() == 2) {
        return has_parallel_edge(G);
    }

    Number minDegV = internal::min_deg_vertex(G);
    std::set<Number> ignored;
    if (ignoreIsolated) {
        int minDeg = 2 * G.size() + 1;
        for (auto &r : G) {
            if (r.degree() == 0) {
                ignored.insert(r.n());
            } else if (r.degree() < minDeg) {
                minDeg = r.degree();
                minDegV = r.n();
            }
        }
    }
    for (Number v : G[minDegV].neighbours()) {
        if (minimum_uncovered_vertices(G, {{minDegV, v}}, ignored) == 0) {
            return true;
        }
    }
    return false;
}

inline bool is_hypohamiltonian_basic(const Graph &G, bool checkHamiltonicity = true) {
    if (checkHamiltonicity && is_hamiltonian_basic(G)) {
        return false;
    }
    Factory f;
    Graph H(copy_other_factory(G, f));
    for (auto &u : H) {
        auto clearedEdges = clear_edges(H, {u.n()}, f);
        if (is_hamiltonian_basic(H, true)) {
            return true;
        }
        restore_edges(H, clearedEdges, f);
    }
    return false;
}

// ================================ TODO fix after we have structures for paths and circuits
// ===================

// pre path bude nejaky objekt v structures
class Path {
    std::vector<Number> vertices_;

public:
    Path() {}
    Path(std::vector<Number> p)
        : vertices_(p.begin(), p.end()) {}

    std::vector<Number> vertices() const { return vertices_; }

    std::vector<Number> normalized(const Path &p) const {
        std::vector<Number> a = p.vertices();
        if (a[0] > a.back()) {
            std::reverse(a.begin(), a.end());
        }
        return a;
    }

    bool operator==(const Path &p2) const {
        auto a1 = normalized(*this);
        auto a2 = normalized(p2);
        return a1 == a2;
    };

    bool operator!=(const Path &p2) const { return !(*this == p2); }

    bool operator<(const Path &p2) const {
        auto a1 = normalized(*this);
        auto a2 = normalized(p2);
        return a1 < a2;
    }
};

// TODO pre circuit bude nejaky objekt v structures
class Circuit {
    std::vector<Number> vertices_;

public:
    Circuit() {}
    Circuit(std::vector<Number> c)
        : vertices_(c.begin(), c.end()) {}

    std::vector<Number> vertices() const { return vertices_; }

    std::vector<Number> normalized(const Circuit &c) const {
        unsigned n = c.vertices().size();
        std::vector<Number> a = c.vertices();
        int p = std::min_element(a.begin(), a.end()) - a.begin();
        int d = (a[index(p + 1, n)] > a[index(p - 1, n)]) ? 1 : -1;  // direction

        std::vector<Number> b(n);
        for (unsigned i = 0; i < n; ++i) {
            b[i] = a[index(p + d * i, n)];
        }
        return b;
    }

    bool operator==(const Circuit &c2) const {
        auto a1 = normalized(*this);
        auto a2 = normalized(c2);
        return a1 == a2;
    };

    bool operator!=(const Circuit &c2) const { return !(*this == c2); }

    bool operator<(const Circuit &c2) const {
        auto a1 = normalized(*this);
        auto a2 = normalized(c2);
        return a1 < a2;
    }

    inline unsigned index(int i, unsigned mod) const { return (i + mod) % mod; }
};

inline std::ostream &operator<<(std::ostream &out, Path p) {
    out << p.vertices();
    return out;
}

inline std::ostream &operator<<(std::ostream &out, Circuit c) {
    out << c.vertices();
    return out;
}

inline std::set<Path> all_paths(const Graph &G, int length) {
#ifdef BA_GRAPH_DEBUG
    assert(length >= 0);
#endif
    std::set<Path> result;
    if (length == 0) {
        for (auto &r : G) {
            result.insert(Path({r.n()}));
        }
        return result;
    }
    auto shorter = all_paths(G, length - 1);
    for (const Path &p : shorter) {
        auto old = p.vertices();
        for (auto &i : G[old.back()]) {
            auto pv = p.vertices();
            if (std::find(old.begin(), old.end(), i.n2()) == old.end()) {
                auto newVertices = old;
                newVertices.push_back(i.n2());
                result.insert(Path(newVertices));
            }
        }
        std::reverse(old.begin(), old.end());
        for (auto &i : G[old.back()]) {
            auto pv = p.vertices();
            if (std::find(old.begin(), old.end(), i.n2()) == old.end()) {
                auto newVertices = old;
                newVertices.push_back(i.n2());
                result.insert(Path(newVertices));
            }
        }
    }
    return result;
}

inline std::set<Path> all_paths(const Graph &G, int lengthFrom, int lengthTo) {
#ifdef BA_GRAPH_DEBUG
    assert(0 <= lengthFrom && lengthFrom <= lengthTo);
#endif
    std::set<Path> result;
    for (int i = lengthFrom; i < lengthTo; ++i) {
        auto pi = all_paths(G, i);
        result.insert(pi.begin(), pi.end());
    }
    return result;
}

inline std::set<Path> all_paths(const Graph &G) { return all_paths(G, 0, G.order()); }

namespace internal {

inline void backtrack_circuits_from(
    const Graph &G, Number start, Number current, std::vector<Number> &path,
    std::vector<bool> &visited, std::set<Circuit> &result, int maxLength
) {
    for (auto neigh : G[current].neighbours()) {
        if (neigh == start && path.size() >= 3) {
            result.insert(Circuit(path));
        } else {
            int idx = neigh.to_int();
            if (idx < (int)visited.size() && !visited[idx] && (int)path.size() < maxLength) {
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from(G, start, neigh, path, visited, result, maxLength);
                path.pop_back();
                visited[idx] = false;
            }
        }
    }
}

inline void backtrack_circuits_from_mod(
    const Graph &G, Number start, Number current, std::vector<Number> &path,
    std::vector<bool> &visited, std::set<Circuit> &result, int maxLength, int mod
) {
    for (auto neigh : G[current].neighbours()) {
        if (neigh == start && path.size() >= 3 && path.size() % mod == 0) {
            result.insert(Circuit(path));
        } else {
            int idx = neigh.to_int();
            if (idx < (int)visited.size() && !visited[idx] && (int)path.size() < maxLength) {
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from_mod(G, start, neigh, path, visited, result, maxLength, mod);
                path.pop_back();
                visited[idx] = false;
            }
        }
    }
}

}  // namespace internal

inline std::set<Circuit> all_circuits(const Graph &G, int maxLength) {
    std::set<Circuit> result;

    // Find maximum vertex number to size the visited array appropriately
    int max_vertex = 0;
    for (auto &r : G) {
        max_vertex = std::max(max_vertex, r.n().to_int());
    }

    std::vector<bool> visited(max_vertex + 1, false);
    std::vector<Number> path;

    for (auto &r : G) {
        Number start = r.n();
        int sidx = start.to_int();
        visited[sidx] = true;
        path.clear();
        path.push_back(start);

        for (auto neigh : r.neighbours()) {
            if (neigh.to_int() > start.to_int()) {
                int idx = neigh.to_int();
                visited[idx] = true;
                path.push_back(neigh);
                internal::backtrack_circuits_from(
                    G, start, neigh, path, visited, result, maxLength
                );
                path.pop_back();
                visited[idx] = false;
            }
        }

        visited[sidx] = false;
    }
    return result;
}

inline std::set<Circuit> all_circuits(const Graph &G, int lengthFrom, int lengthTo)
{
#ifdef BA_GRAPH_DEBUG
    assert(0 <= lengthFrom && lengthFrom <= lengthTo);
#endif

    std::set<Circuit> result;

    // Find maximum vertex number to size the visited array appropriately
    int max_vertex = 0;
    for (auto &r : G) {
        max_vertex = std::max(max_vertex, r.n().to_int());
    }
    
    return result;
}

inline std::set<Circuit> all_circuits(const Graph &G)
{
    return all_circuits(G, 3, G.order() + 1);
}






inline void backtrack_circuits_from(
    const Graph &G, 
    Number start,
    Number current,
    std::vector<Number> &path,
    std::vector<bool> &visited,
    std::set<Circuit> &result,
    int maxLength)
{
    for (auto neigh : G[current].neighbours()) {
        if (neigh == start && path.size() >= 3) {
            result.insert(Circuit(path));
        } else {
            int idx = neigh.to_int();
            if (idx < visited.size() && !visited[idx] && path.size() < maxLength) {
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from(G, start, neigh, path, visited, result, maxLength);
                path.pop_back();
                visited[idx] = false;
            }
        }
    }
}


inline void backtrack_circuits_from_mod(
    const Graph &G, 
    Number start,
    Number current,
    std::vector<Number> &path,
    std::vector<bool> &visited,
    std::set<Circuit> &result,
    int maxLength, 
    int mod)
{
    for (auto neigh : G[current].neighbours()) {
        if (neigh == start && path.size() >= 3 && path.size() % mod == 0) {
            result.insert(Circuit(path));
        } else {
            int idx = neigh.to_int();
            if (idx < (int)visited.size() && !visited[idx] && (int)path.size() < maxLength) {
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from_mod(G, start, neigh, path, visited, result, maxLength, mod);
                path.pop_back();
                visited[idx] = false;
            }
        }
    }
}



inline std::set<Circuit> all_circuits_fast(const Graph &G, int maxLength)
{
    std::set<Circuit> result;
    std::vector<Number> nodes;
    for (auto &r : G) nodes.push_back(r.n());
    const int n = nodes.size();

    std::vector<bool> visited(n, false);
    std::vector<Number> path;

    for (auto &r : G) {
        Number start = r.n();
        int sidx = start.to_int();
        visited[sidx] = true;
        path.clear();
        path.push_back(start);

        for (auto neigh : r.neighbours()) {
            if (neigh.to_int() > start.to_int()) {
                int idx = neigh.to_int();
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from(G, start, neigh, path, visited, result, maxLength);
                path.pop_back();
                visited[idx] = false;
            }
        }

        visited[sidx] = false;
    }
    return result;
}




inline std::set<Circuit> all_circuits_fast(const Graph &G)
{
    return all_circuits_fast(G, G.order() + 1);
}



inline std::set<Circuit> all_circuits_fast_mod(const Graph &G, int mod)
{
    int maxLength = G.order() + 1;
    std::set<Circuit> result;
    std::vector<Number> nodes;
    for (auto &r : G) nodes.push_back(r.n());
    const int n = nodes.size();

    std::vector<bool> visited(n, false);
    std::vector<Number> path;

    for (auto &r : G) {
        Number start = r.n();
        int sidx = start.to_int();
        visited[sidx] = true;
        path.clear();
        path.push_back(start);

        for (auto neigh : r.neighbours()) {
            if (neigh.to_int() > start.to_int()) {
                int idx = neigh.to_int();
                visited[idx] = true;
                path.push_back(neigh);
                backtrack_circuits_from_mod(G, start, neigh, path, visited, result, maxLength, mod);
                path.pop_back();
                visited[idx] = false;
            }
        }

        visited[sidx] = false;
    }
    
    return result;
}





} // namespace ba_graph

#endif
