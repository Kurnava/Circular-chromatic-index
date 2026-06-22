#ifndef BA_GRAPH_INVARIANTS_COLOURING_CVD_3REGULAR_HPP
#define BA_GRAPH_INVARIANTS_COLOURING_CVD_3REGULAR_HPP

// Project-specific C++ headers
#include "graphs/basic.hpp"  // For Graph, Factory
#include "invariants/girth.hpp"
#include "operations/basic.hpp"
#include "operations/copies.hpp"
#include "snarks/reductions.hpp"  // For reduce_digons

// ******************************** start of legacy code ********************************
//
// Created by Michal Povinsky on 04/10/16.
// Modified: Jan Karabas on 31/03/17
//

#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <random>

namespace ba_graph::legacy::cvd {

#ifdef __POPCNT__
#include <popcntintrin.h>
#endif

const int LEGACY_CVD_DEGREE = 3;
const uint32_t LEGACY_CVD_ALL_COLORS = ((1 << LEGACY_CVD_DEGREE) - 1);

typedef uint32_t colorset;

struct set {
    int elems;
    int *elem;
};

struct graph {
    int size;
    int (*nei)[LEGACY_CVD_DEGREE];
    short *deg;
    colorset (*col)[LEGACY_CVD_DEGREE];
    int *dictpos, *oldcl;
    struct set dict[LEGACY_CVD_DEGREE - 1];
    int *chain, *chain_used;
};

static struct graph graph_init(int s) {
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
    struct graph g = {
        .size = s,
        .nei =
            reinterpret_cast<int(*)[LEGACY_CVD_DEGREE]>(calloc(s, sizeof(int[LEGACY_CVD_DEGREE]))),
        .deg = static_cast<short *>(calloc(s, sizeof(short))),
        .col = reinterpret_cast<colorset(*)[LEGACY_CVD_DEGREE]>(
            calloc(s, sizeof(colorset[LEGACY_CVD_DEGREE]))
        ),
        .dictpos = static_cast<int *>(calloc(s, sizeof(int))),
        .oldcl = static_cast<int *>(calloc(s, sizeof(int))),
        .chain = static_cast<int *>(calloc(s + 1, sizeof(int))),
        .chain_used = static_cast<int *>(calloc(s, sizeof(int)))
    };
#pragma GCC diagnostic pop
    for (int i = 0; i < LEGACY_CVD_DEGREE - 1; i++) {
        g.dict[i].elem = static_cast<int *>(calloc(s, sizeof(int)));
    }
    return g;
}

static void graph_free(struct graph *g) {
    free(g->nei);
    free(g->deg);
    free(g->col);
    free(g->dictpos);
    free(g->oldcl);
    free(g->chain);
    free(g->chain_used);
    for (int i = 0; i < LEGACY_CVD_DEGREE - 1; i++) {
        free(g->dict[i].elem);
    }
}

/*static void showgraph(struct graph *g)
{
    static char *colors[] = { "black", "red", "green", NULL, "blue" };
    FILE *f = fopen("_g.dot", "w");
    fprintf(f, "graph {\n");
    fprintf(f, "overlap = false; \n splines = true; \n");
    for (int u = 0; u < g->size; u++) {
        fprintf(f, "%d\n", u);
        for (int vi = 0; vi < g->deg[u]; vi++) {
            int v = g->nei[u][vi];
            if (v > u) continue;
            fprintf(f, "%d -- %d [color=%s]\n", u, v, colors[g->col[u][vi]]);
        }
    }
    fprintf(f, "}\n");
    fclose(f);
    system("sfdp -Tpng -o _g.png _g.dot && eom _g.png");
}*/

static void add_edge(struct graph *g, int u, int v) {
    // fprintf(stderr, "adding edge %d,%d\n", u, v);
    assert(g->deg[u] < LEGACY_CVD_DEGREE && g->deg[v] < LEGACY_CVD_DEGREE);
    g->nei[u][g->deg[u]++] = v;
    g->nei[v][g->deg[v]++] = u;
}

static int random_int(std::mt19937 &rng, int upper_bound) {
    assert(upper_bound > 0);
    return std::uniform_int_distribution<int>(0, upper_bound - 1)(rng);
}

static int set_random(struct set *s, std::mt19937 &rng) {
    assert(s->elems > 0);
    return s->elem[random_int(rng, s->elems)];
}

static int popcount(colorset a) {
#if defined(__POPCNT__)
    return _mm_popcnt_u32(a);
#else
    a = a - ((a >> 1) & 0x55555555);
    a = (a & 0x33333333) + ((a >> 2) & 0x33333333);
    return (((a + (a >> 4)) & 0xF0F0F0F) * 0x1010101) >> 24;
#endif
}

static int conflict_level(struct graph *g, int v) {
    colorset colors = 0;
    for (int i = 0; i < g->deg[v]; i++) {
        colors |= g->col[v][i];
    }
    return g->deg[v] - popcount(colors);
}

/*static void printdict(struct graph *g)
{
    for (int i=1; i<LEGACY_CVD_DEGREE; i++) {
        fprintf(stderr, "CL[%d]={", i);
        for (int j=0; j<g->dict[i-1].elems; j++) {
            fprintf(stderr, "%d,", g->dict[i-1].elem[j]);
        }
        fprintf(stderr, "}\n");
    }
}*/

static void update_conflict_level(struct graph *g, int v) {
    int newcl = conflict_level(g, v);
    int oldcl = g->oldcl[v];
    if (oldcl == newcl) {
        return;
    }
    // fprintf(stderr, "Updating conflict level for vertex %d from %d to %d\n", v, oldcl, newcl);
    if (oldcl > 0) {
        struct set *odict = &g->dict[oldcl - 1];
        int odictpos = g->dictpos[v];
        // fprintf(stderr, "Removing %d from position %d\n", v, odictpos);
        assert(odictpos < odict->elems);
        assert(odict->elem[odictpos] == v);
        odict->elems--;
        if (odict->elems >= odictpos + 1) {
            // fprintf(stderr, "Had to update odictpos on %d to %d\n", odict->elem[odict->elems],
            // odictpos);
            odict->elem[odictpos] = odict->elem[odict->elems];
            g->dictpos[odict->elem[odictpos]] = odictpos;
        }
    }
    if (newcl > 0) {
        struct set *ndict = &g->dict[newcl - 1];
        ndict->elem[ndict->elems] = v;
        g->dictpos[v] = ndict->elems;
        ndict->elems++;
    }
    g->oldcl[v] = newcl;
    // printdict(g);
}

static colorset used_colors(struct graph *g, int u) {
    colorset used = 0;
    for (int vi = 0; vi < g->deg[u]; vi++) {
        used |= g->col[u][vi];
    }
    return used;
}

static colorset conflicting_colors(struct graph *g, int u) {
    colorset used = 0, confl = 0;
    for (int i = 0; i < g->deg[u]; i++) {
        colorset c = g->col[u][i];
        if (used & c) {
            confl |= c;
        } else {
            used |= c;
        }
    }
    return confl;
}

static colorset random_color(colorset avail, std::mt19937 &rng) {
    if (avail == 0 || avail == LEGACY_CVD_ALL_COLORS) {
        return 1 << random_int(rng, LEGACY_CVD_DEGREE);
    }
    if (popcount(avail) == 1) {
        return avail;
    }
    while (1) {
        colorset c_bit = 1 << random_int(rng, LEGACY_CVD_DEGREE);
        if (c_bit & avail) {
            return c_bit;
        }
    }
}

static colorset edge_color(struct graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->nei[u][i] == v) {
            return g->col[u][i];
        }
    }
    throw std::runtime_error("colourising_cvd_3regular: edge doesn't exist");
}

static void color_single(struct graph *g, int u, int v, colorset c) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->nei[u][i] == v) {
            g->col[u][i] = c;
            return;
        }
    }
}

static void color(struct graph *g, int u, int v, colorset c) {
    color_single(g, u, v, c);
    color_single(g, v, u, c);
}

static int highest_conflict_level(struct graph *g) {
    for (int i = LEGACY_CVD_DEGREE - 1; i > 0; i--) {
        if ((g->dict[i - 1].elems)) {
            return i;
        }
    }
    return 0;
}

static int total_number_of_conflicts(struct graph *g) {
    int sum = 0;
    for (int i = 1; i < LEGACY_CVD_DEGREE; i++) {
        sum += i * g->dict[i - 1].elems;
    }
    return sum;
}

static void precolor(struct graph *g, std::mt19937 &rng) {
    for (int u = 0; u < g->size; u++) {
        for (int vi = 0; vi < g->deg[u]; vi++) {
            if (g->col[u][vi] != 0) {
                continue;
            }
            int v = g->nei[u][vi];
            colorset avail = LEGACY_CVD_ALL_COLORS ^ (used_colors(g, u) | used_colors(g, v));
            color(g, u, v, random_color(avail, rng));
        }
    }
}

static int random_neigh_of_color(struct graph *g, int v, colorset col, std::mt19937 &rng) {
    assert(used_colors(g, v) & col);
    int candidates[LEGACY_CVD_DEGREE];
    int candidate_count = 0;
    for (int i = 0; i < g->deg[v]; i++) {
        if (col & g->col[v][i]) {
            candidates[candidate_count++] = g->nei[v][i];
        }
    }
    if (candidate_count == 0) {
        throw std::runtime_error("colourising_cvd_3regular: no neighbour has requested colour");
    }
    if (candidate_count == 1) {
        return candidates[0];
    }
    return candidates[random_int(rng, candidate_count)];
}

static void kempe(struct graph *g, int start, std::mt19937 &rng) {
    colorset cused = used_colors(g, start);
    colorset cconfl = conflicting_colors(g, start);
    colorset cfree = LEGACY_CVD_ALL_COLORS ^ cused;
    int *chain = g->chain, *chain_used = g->chain_used;
    int chain_length;
    colorset colors[2];
    chain[0] = start;
    // fprintf(stderr, "cused=%d cconfl=%d cfree=%d\n", cused, cconfl, cfree);
    chain[1] = random_neigh_of_color(g, start, cconfl, rng);
    colors[0] = edge_color(g, start, chain[1]);
    colors[1] = random_color(cfree, rng);
    chain_used[start] = chain_used[chain[1]] = 1;
    // fprintf(stderr, "chain start %d,%d colors %d,%d\n", chain[0], chain[1], colors[0],
    // colors[1]);
    for (int i = 1;; i++) {
        colorset next_used = used_colors(g, chain[i]);
        colorset next_color = colors[i % 2];
        // fprintf(stderr, "chain %d next_used=%d next_color=%d\n", chain[i], next_used,
        // next_color);
        if (!(next_used & next_color)) {
            chain_length = i;
            break;
        }
        chain[i + 1] = random_neigh_of_color(g, chain[i], next_color, rng);
        // fprintf(stderr, "next chain step %d -> %d\n", chain[i], chain[i+1]);
        if (chain_used[chain[i + 1]]) {
            chain_length = i + 1;
            break;
        }
        chain_used[chain[i + 1]] = 1;
    }
    /*    fprintf(stderr, "Chain [");
        for (int i = 0; i <= chain_length; i++) {
            fprintf(stderr, "%d%c", chain[i], i==chain_length ? ']' : ' ');
        }
        fprintf(stderr, " with colors %d %d\n", colors[0], colors[1]);
        showgraph(g);*/
    for (int i = 0; i < chain_length; i++) {
        color(g, chain[i], chain[i + 1], colors[(i + 1) % 2]);
    }
    for (int i = 0; i <= chain_length; i++) {
        update_conflict_level(g, chain[i]);
    }
    for (int i = 0; i <= chain_length; i++) {
        chain_used[chain[i]] = 0;
    }
}

static int heuristic(struct graph *g, int replimit, std::mt19937 &rng) {
    // fprintf(stderr, "****************************** new iteration\n");
    for (int i = 0; i < LEGACY_CVD_DEGREE - 1; i++) {
        g->dict[i].elems = 0;
    }
    for (int i = 0; i < g->size; i++) {
        g->oldcl[i] = 0;
        for (int j = 0; j < g->deg[i]; j++) {
            g->col[i][j] = 0;
        }
    }
    precolor(g, rng);
    for (int i = 0; i < g->size; i++) {
        update_conflict_level(g, i);
    }
    // printdict(g);
    int step = 0, repcount = 0, previous, current;
    current = total_number_of_conflicts(g);
    while (1) {
        /*fprintf(stderr, "step=%d rep=%d conflicts=%d [", step, repcount, current);
        for (int i = 0; i < LEGACY_CVD_DEGREE - 1; i++) fprintf(stderr, "%d ", g->dict[i].elems);
        fprintf(stderr, "]\n");*/
        if (current == 0) {
            return 1;
        }

        previous = current;
        int clevel = highest_conflict_level(g);
        struct set *dict = &(g->dict[clevel - 1]);
        int chain_start = set_random(dict, rng);
        // printdict(g);
        // fprintf(stderr, "highest_conflict_level = %d, %d conflicts, picked vertex %d with cl
        // %d\n", clevel, dict->elems, chain_start, conflict_level(g, chain_start));
        kempe(g, chain_start, rng);
        current = total_number_of_conflicts(g);
        if (current < previous) {
            repcount = 0;
        } else {
            repcount++;
            if (repcount > replimit) {
                return 0;
            }
        }
        step++;
    }
}

static int do_heuristic(struct graph *g, int iterlimit, int replimit, std::mt19937 &rng) {
    int ret = 0;
    // TODO fine-tune these limits maybe?
    if (replimit == -1) {
        replimit = static_cast<int>(sqrt(g->size)) + 1;
    }
    if (iterlimit == -1) {
        iterlimit = 64;
    }

    // printf("Graph size: %d\n",g->size);
    for (int i = 0; i < iterlimit; i++) {
        ret = heuristic(g, replimit, rng);
        if (ret) {
            ret = i + 1;
            break;
        }
    }
    return ret;
}

/* ======= not needed now ==============

// LCOV_EXCL_START — only called from legacy C API (color_cvd_param/color_cvd_adjlist), both dead
static int core_heuristic(struct graph *g, int iterlimit, int replimit, std::mt19937 &rng) {
    int ret = 0;  //, replimit = (int)(sqrt(g->size))+1, iterlimit = 64;;

    // printf("Graph size: %d\n",g->size);
    for (int i = 0; i < iterlimit; i++) {
        ret = heuristic(g, replimit, rng);
        if (ret) {
            ret = i + 1;
            break;
        }
    }
    return ret;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START — only called from legacy C API (color_cvd_param/color_cvd_adjlist), both dead
static int color_to_idx(colorset c) {
    int ci = 0;
    while (c && !(c & 1)) {
        ci++;
        c >>= 1;
    }
    assert(c == 1);
    return ci + 1;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START — legacy C API, superseded by has_cvd_edge_colouring_3regular
inline int color_cvd_param(char *mat, int size, int iterlimit, int replimit) {
    int ret;
    std::random_device rd;
    std::mt19937 rng(rd());
    struct graph g = graph_init(size);
    for (int u = 0; u < size; u++) {
        for (int v = 0; v < u; v++) {
            if (mat[u * size + v]) {
                add_edge(&g, u, v);
            }
        }
    }
    ret = core_heuristic(&g, iterlimit, replimit, rng);
    if (ret) {
        for (int u = 0; u < size; u++) {
            for (int vi = 0; vi < g.deg[u]; vi++) {
                int v = g.nei[u][vi];
                mat[u * size + v] = mat[v * size + u] = color_to_idx(edge_color(&g, u, v));
            }
        }
    }
    graph_free(&g);
    return ret;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START — legacy C API, superseded by has_cvd_edge_colouring_3regular
inline int color_cvd_adjlist(int *mat, int *colormat, int size) {
    int ret;
    std::random_device rd;
    std::mt19937 rng(rd());
    struct graph g = graph_init(size);
    for (int u = 0; u < size; u++) {
        for (int vi = 0; vi < LEGACY_CVD_DEGREE; vi++) {
            int v = mat[2 * LEGACY_CVD_DEGREE * u + vi];
            if (v >= 0) {
                add_edge(&g, u, v);
            }
        }
    }
    ret = do_heuristic(&g, -1, -1, rng);
    if (ret) {
        for (int u = 0; u < size; u++) {
            for (int vi = 0; vi < LEGACY_CVD_DEGREE; vi++) {
                int v = mat[LEGACY_CVD_DEGREE * u + vi];
                colormat[LEGACY_CVD_DEGREE * u + vi] =
                    (v < 0) ? -1 : color_to_idx(edge_color(&g, u, v));
            }
        }
    }
    graph_free(&g);
    return ret;
}
// LCOV_EXCL_STOP

======= not needed now ============== */

}  // namespace ba_graph::legacy::cvd
// ******************************** end of legacy code ********************************

namespace ba_graph {

inline bool has_cvd_edge_colouring_3regular(
    const Graph &G, int iterationLimit = -1, int repetitionLimit = -1, int seed = -1
) {
    Factory f;
    Graph H(copy_other_factory(G, f));
    reduce_digons(H, f);
    if (H.order() == 0) {
        return true;
    }
    if (has_loop(H)) {
        return false;
    }
#ifdef BA_GRAPH_DEBUG
    // LCOV_EXCL_START
    if (has_parallel_edge(H)) {
        throw std::runtime_error(
            "has_cvd_edge_colouring_3regular: digon reduction left parallel edges"
        );
    }
// LCOV_EXCL_STOP
#endif
    renumber_consecutive(H, f);

    struct legacy::cvd::graph g = legacy::cvd::graph_init(H.order());
    for (auto &ii : H.list(RP::all(), IP::primary())) {
        legacy::cvd::add_edge(&g, ii->n1().to_int(), ii->n2().to_int());
    }

    std::mt19937 rng;
    if (seed >= 0) {
        rng.seed(static_cast<unsigned>(seed));
    } else {
        std::random_device rd;
        rng.seed(rd());
    }
    int ret = legacy::cvd::do_heuristic(&g, iterationLimit, repetitionLimit, rng);
    // if (ret) {
    //     for (int u = 0; u < size; u++) {
    //         for (int vi = 0; vi < g.deg[u]; vi++) {
    //             int v = g.nei[u][vi];
    //             mat[u*size+v] = mat[v*size+u] = color_to_idx(edge_color(&g, u, v));
    //         }
    //     }
    // }
    legacy::cvd::graph_free(&g);
    return ret;
}

}  // namespace ba_graph

#endif  // BA_GRAPH_INVARIANTS_COLOURING_CVD_3REGULAR_HPP
