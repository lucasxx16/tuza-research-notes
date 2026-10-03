#!/usr/bin/env python3
"""Independent exact verification of two literal Tuza-type certificates.

E certificate (mad8/round1/E/mixed_fano_and_density.txt):
  graph G0 = K9 minus edge 01, reducible pair {0,2},
  7 packed triangles, 14 cover edges (Lemma F instance).
D certificate (mad8/round1/D/dense_pair_certificate.txt):
  graph J4 (hubs 0,1; core 2..5; A 6,7; B 8,9), pair {0,1},
  8 packed triangles, 16 cover edges.
All arithmetic uses Fraction; mad computed exactly over all vertex subsets.
Graph definitions do not depend on the witnesses.
"""
import json
import itertools
from fractions import Fraction
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this checker uses assertions")

BASE = Path(__file__).resolve().parent
OUT = {}


def edge_set(n, edges):
    E = set()
    for a, b in edges:
        assert a != b and 0 <= a < n and 0 <= b < n
        E.add((min(a, b), max(a, b)))
    return E


def k(n, verts=None):
    verts = list(range(n)) if verts is None else list(verts)
    return [(a, b) for a, b in itertools.combinations(sorted(verts), 2)]


def graph_K9_minus_01():
    """K9 minus edge 01 (E-file density obstruction G0)."""
    edges = k(9)
    edges.remove((0, 1))
    return 9, edge_set(9, edges)


def graph_J4():
    """Maximal codegree-four patch: hubs 0,1; core 2..5; A 6,7; B 8,9.
    All allowed hub/core/side edges, all A-C and B-C edges, no A-B edges."""
    edges = [(0, 1)]
    edges += k(4, [2, 3, 4, 5])            # core K4
    for h in (0, 1):
        edges += [(h, c) for c in (2, 3, 4, 5)]   # hub-core
    edges += [(0, 6), (0, 7)]              # hub0 - A
    edges += [(1, 8), (1, 9)]              # hub1 - B
    edges += [(6, 7)]                      # a0a1
    edges += [(8, 9)]                      # b0b1
    for a in (6, 7):
        edges += [(a, c) for c in (2, 3, 4, 5)]   # A-C
    for b in (8, 9):
        edges += [(b, c) for c in (2, 3, 4, 5)]   # B-C
    # no A-B edges (6,7 to 8,9 excluded)
    return 10, edge_set(10, edges)


def graph_K7_join_I3():
    """Join of a 7-clique (0..6) and an independent 3-set (7,8,9)."""
    edges = k(7, [0, 1, 2, 3, 4, 5, 6])
    edges += [(i, j) for i in range(7) for j in (7, 8, 9)]
    return 10, edge_set(10, edges)


def triangles(n, E):
    return [t for t in itertools.combinations(range(n), 3)
            if all((min(a, b), max(a, b)) in E for a, b in itertools.combinations(t, 2))]


def tedges(t):
    return {tuple(sorted(p)) for p in itertools.combinations(t, 2)}


def degrees(n, E):
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    return deg


def mad_exact(n, E):
    """mad over all nonempty vertex subsets, exact Fractions."""
    best = None
    best_sub = None
    for r in range(1, n + 1):
        for sub in itertools.combinations(range(n), r):
            s = set(sub)
            m = sum(1 for a, b in E if a in s and b in s)
            val = Fraction(2 * m, r)
            if best is None or val > best:
                best, best_sub = val, sub
    return best, list(best_sub)


def check_packing(name, n, E, S, pair, X, expected_len_S):
    """Full reducibility-certificate audit for V0 = pair."""
    res = {"graph": name, "pair": list(pair)}
    V0 = set(pair)
    # 1. packing triangles are actual triangles of the graph
    res["triangles_well_formed"] = all(
        len(t) == 3 and len(set(t)) == 3 and all(0 <= v < n for v in t)
        for t in S)
    res["all_triangles_exist"] = all(tedges(t) <= E for t in S)
    # 2. edge-disjointness of the packing
    all_e = [e for t in S for e in sorted(tedges(t))]
    res["packing_size"] = len(S)
    res["expected_packing_size_ok"] = len(S) == expected_len_S
    res["edge_disjoint"] = len(all_e) == len(set(all_e))
    res["packed_edges"] = len(set(all_e))
    # 3. cover set X consists of real edges and meets the size bound
    res["X_edges_exist"] = all(e in E for e in X)
    res["X_size"] = len(set(X))
    res["X_size_bound_ok"] = len(set(X)) <= 2 * len(S)
    # 4. every triangle containing a vertex of V0 is met by X
    XS = set(X)
    tri = triangles(n, E)
    hit = [t for t in tri if V0 & set(t)]
    res["triangles_through_pair"] = len(hit)
    res["all_pair_triangles_hit"] = all(tedges(t) & XS for t in hit)
    # 5. every packed edge outside the pair lies in X
    outside = [e for e in set(all_e) if not (V0 & set(e))]
    res["packed_edges_outside_pair"] = len(outside)
    res["all_outside_packed_edges_in_X"] = all(e in XS for e in outside)
    res["ok"] = all(v for k_, v in res.items()
                    if isinstance(v, bool))
    return res


def main():
    # ---------- graph instances and exact degrees / mad ----------
    graphs = {
        "K9_minus_edge01": graph_K9_minus_01(),
        "J4_maximal_codegree4_patch": graph_J4(),
        "K7_join_I3": graph_K7_join_I3(),
    }
    mads = {}
    for name, (n, E) in graphs.items():
        deg = degrees(n, E)
        val, sub = mad_exact(n, E)
        mads[name] = {
            "n": n, "m": len(E), "degrees": deg,
            "mad": str(val), "mad_is_exact_fraction": True,
            "witness_subset": sub,
        }
    OUT["mad"] = mads
    # sanity: G0 mad should be 70/9; join graph mad 42/5
    OUT["sanity"] = {
        "G0_mad_is_70_9": Fraction(mads["K9_minus_edge01"]["mad"]) == Fraction(70, 9),
        "J4_mad_is_37_5": Fraction(mads["J4_maximal_codegree4_patch"]["mad"]) == Fraction(37, 5),
        "join_mad_is_42_5": Fraction(mads["K7_join_I3"]["mad"]) == Fraction(42, 5),
    }

    # ---------- E certificate: K9 - 01, pair (0,2) ----------
    n, E = graphs["K9_minus_edge01"]
    u, v = 0, 2
    c0, c1, c2, c3, c4 = 3, 4, 5, 6, 7
    z = 8
    S_E = [(u, v, c0), (u, c1, c2), (u, c3, c4), (v, c1, c3),
           (v, c2, c4), (c0, c1, c4), (c0, c2, c3)]
    core = {c0, c1, c2, c3, c4}
    X_E = sorted(e for e in E if e[0] in core and e[1] in core)
    X_E += [(u, v), (u, z), (v, z)]
    # external neighbours of u,v outside K={0,2,3,4,5,6,7,8}: only vertex 1
    K_E = {u, v, c0, c1, c2, c3, c4, z}
    for w in range(n):
        if w not in K_E:
            for h in (u, v):
                e = (min(h, w), max(h, w))
                if e in E:
                    X_E.append(e)
    OUT["E_certificate"] = check_packing(
        "K9_minus_edge01", n, E, S_E, (u, v), X_E, 7)
    OUT["E_certificate"]["X_size_is_14"] = len(set(X_E)) == 14

    # ---------- D certificate: J4, pair (0,1) ----------
    n, E = graphs["J4_maximal_codegree4_patch"]
    u, v = 0, 1
    c0, c1, c2, c3 = 2, 3, 4, 5
    a0, a1, b0, b1 = 6, 7, 8, 9
    C = (c0, c1, c2, c3)
    S_D = [(u, c0, c1), (u, c2, c3), (u, a0, a1),
           (a1, c0, c3), (a1, c1, c2),
           (v, c0, c2), (v, c1, c3), (v, b0, b1)]
    R = sorted(e for e in E if e[0] in C and e[1] in C)   # E(G[C])
    R += edge_set(n, [(a0, a1), (b0, b1), (a1, c0),
                      (a1, c1), (a1, c2), (a1, c3)])
    X_D = sorted(set(R + [(u, v), (u, a0), (v, b0), (v, b1)]))
    OUT["D_certificate"] = check_packing(
        "J4_maximal_codegree4_patch", n, E, S_D, (u, v), X_D, 8)
    OUT["D_certificate"]["R_size_is_12"] = len(set(R)) == 12
    OUT["D_certificate"]["X_size_is_16"] = len(set(X_D)) == 16
    OUT["D_certificate"]["R_subset_X"] = set(R) <= set(X_D)

    OUT["all_ok"] = (
        all(v for key in ("E_certificate", "D_certificate")
            for v in OUT[key].values() if isinstance(v, bool))
        and all(OUT["sanity"].values()))

    with open(BASE / "named_graph_results.json", "w", encoding="utf-8") as f:
        json.dump(OUT, f, indent=2)

    lines = []
    for name, info in mads.items():
        lines.append("%s: n=%d m=%d degrees=%s mad=%s (witness %s)"
                     % (name, info["n"], info["m"], info["degrees"],
                        info["mad"], info["witness_subset"]))
    for key in ("E_certificate", "D_certificate"):
        c = OUT[key]
        lines.append("%s: ok=%s triangles=%d edge_disjoint=%s "
                     "pair_tris=%d all_hit=%s outside_in_X=%s |X|=%d<=%d"
                     % (key, c["ok"], c["packing_size"], c["edge_disjoint"],
                        c["triangles_through_pair"], c["all_pair_triangles_hit"],
                        c["all_outside_packed_edges_in_X"], c["X_size"],
                        2 * c["packing_size"]))
    lines.append("ALL_OK=%s" % OUT["all_ok"])
    print("\n".join(lines))
    return 0 if OUT["all_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
