#ifndef BA_GRAPH_SAT_EXEC_CIRCULAR_CPSAT_HPP
#define BA_GRAPH_SAT_EXEC_CIRCULAR_CPSAT_HPP

#include "../invariants/girth.hpp"
#include <map>
#include <vector>
#include <utility>
#include <string>
#include <ortools/sat/cp_model.h>
#include <ortools/sat/cp_model_solver.h>

namespace ba_graph {

using operations_research::Domain;
using operations_research::sat::CpModelBuilder;
using operations_research::sat::CpSolverResponse;
using operations_research::sat::IntVar;
using operations_research::sat::CpSolverStatus;
using operations_research::sat::SolutionIntegerValue;
using operations_research::sat::Solve;

inline void cpsat_build_edge_list(const Graph &G, std::vector<Number> &order, std::map<Number,int> &index, std::vector<std::pair<int,int>> &edges) {
    order.clear();
    for (auto &r : G) order.push_back(r.n());
    int n = order.size();
    index.clear();
    for (int i = 0; i < n; ++i) index[order[i]] = i;
    edges.clear();
    for (auto &r : G) {
        Number v1 = r.n();
        int u = index[v1];
        for (auto &inc : r) {
            Number v2 = inc.n2();
            int v = index[v2];
            if (v <= u) continue;
            edges.emplace_back(u, v);
        }
    }
}

inline void cpsat_add_circular_distance_constraint(CpModelBuilder &model, IntVar a, IntVar b, int p, int q, int idx, const std::string &prefix) {
    Domain d(q, p - q);
    IntVar diff = model.NewIntVar(d).WithName(prefix + "_d_" + std::to_string(idx));
    model.AddAbsEquality(diff, a - b);
}

inline bool cpsat_circular_vertex_raw(int n, const std::vector<std::pair<int,int>> &edges, int p, int q, std::vector<int> &out) {
    if (n <= 0) { out.clear(); return true; }
    if (p <= 0 || q <= 0 || 2*q > p) return false;
    CpModelBuilder m;
    Domain d(0, p - 1);
    std::vector<IntVar> x;
    x.reserve(n);
    for (int i = 0; i < n; ++i) x.push_back(m.NewIntVar(d).WithName("v_" + std::to_string(i)));
    int c = 0;
    for (auto &e : edges) cpsat_add_circular_distance_constraint(m, x[e.first], x[e.second], p, q, c++, "e");
    CpSolverResponse r = Solve(m.Build());
    if (r.status() != CpSolverStatus::OPTIMAL && r.status() != CpSolverStatus::FEASIBLE) return false;
    out.resize(n);
    for (int i = 0; i < n; ++i) out[i] = SolutionIntegerValue(r, x[i]);
    return true;
}

inline bool is_circularly_colourable_cpsat(const Graph &G, int p, int q, std::vector<int> *v = nullptr) {
    if (has_loop(G)) return false;
    std::vector<Number> order;
    std::map<Number,int> index;
    std::vector<std::pair<int,int>> edges;
    cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> out;
    bool ok = cpsat_circular_vertex_raw(order.size(), edges, p, q, out);
    if (!ok) return false;
    if (v) *v = std::move(out);
    return true;
}

inline bool cpsat_circular_edge_raw(int n, const std::vector<std::pair<int,int>> &edges, int p, int q, bool sym, std::vector<int> &out) {
    int m = edges.size();
    if (m == 0) { out.clear(); return true; }
    if (n <= 0 || p <= 0 || q <= 0 || 2*q > p) return false;
    CpModelBuilder model;
    Domain d(0, p - 1);
    std::vector<IntVar> evar;
    evar.reserve(m);
    for (int i = 0; i < m; ++i) evar.push_back(model.NewIntVar(d).WithName("e_" + std::to_string(i)));
    std::vector<std::vector<int>> inc(n);
    for (int i = 0; i < m; ++i) {
        auto [u,v] = edges[i];
        inc[u].push_back(i);
        inc[v].push_back(i);
    }
    int c = 0;
    for (int v = 0; v < n; ++v)
        for (int i = 0; i < inc[v].size(); ++i)
            for (int j = i + 1; j < inc[v].size(); ++j)
                cpsat_add_circular_distance_constraint(model, evar[inc[v][i]], evar[inc[v][j]], p, q, c++, "p");
    if (sym && m > 0) {
        model.AddEquality(evar[0], 0);
        int u0 = edges[0].first;
        int v0 = edges[0].second;
        int e1 = -1;
        for (int i = 1; i < m; ++i) {
            auto [u,v] = edges[i];
            if (u == u0 || u == v0 || v == u0 || v == v0) { e1 = i; break; }
        }
        if (e1 != -1) model.AddEquality(evar[e1], p/2);
    }
    CpSolverResponse r = Solve(model.Build());
    if (r.status() != CpSolverStatus::OPTIMAL && r.status() != CpSolverStatus::FEASIBLE) return false;
    out.resize(m);
    for (int i = 0; i < m; ++i) out[i] = SolutionIntegerValue(r, evar[i]);
    return true;
}

inline bool is_circularly_edge_colourable_cpsat(const Graph &G, int p, int q, std::vector<int> *out_colouring = nullptr, bool sym = true) {
    if (has_loop(G)) return false;
    std::vector<Number> order;
    std::map<Number,int> index;
    std::vector<std::pair<int,int>> edges;
    cpsat_build_edge_list(G, order, index, edges);
    std::vector<int> out;
    bool ok = cpsat_circular_edge_raw(order.size(), edges, p, q, sym, out);
    if (!ok) return false;
    if (out_colouring) *out_colouring = std::move(out);
    return true;
}

}

#endif
