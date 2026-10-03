#!/usr/bin/env python3
"""Standalone exact numerical verifier (standard library only) for two candidate
graphs of the Westlake-type triangle packing / covering problem.

Baseline : K4 Cartesian K4,4   vertices (i,s,j), i,j in 0..3, s in 0..1  (n=32)
Primary  : K4 Cartesian K5     vertices (i,j),    i in 0..3, j in 0..4   (n=20)

Computes: edge set (sorted), degree check, connectivity, triangle count by
full triple enumeration, edges in zero triangles, explicit packing/cover, and
exact nu (max edge-disjoint triangle packing) / tau (min triangle edge-hitting
set) via connected components of the triangle-edge-incidence hypergraph with
exhaustive search per small component. No external solvers, no all-graph
enumeration. Output is computational evidence only (no proof claims).
"""

import hashlib
import itertools
import json
import sys
import time

RESULTS = {}


def vertex_label(v):
    return "-".join(map(str, v))


# ---------------------------------------------------------------- graph build

def build_edges(vertices, adjacent):
    edges = []
    idx = {v: k for k, v in enumerate(vertices)}
    for a, b in itertools.combinations(vertices, 2):
        if adjacent(a, b):
            edges.append((idx[a], idx[b]))  # index pairs, a before b in list
    edges.sort()
    return edges, idx


def graph_32():
    # K4 [] K4,4. (i,s,j); edge iff same (s,j) & i differs, or same i & s differs.
    verts = [(i, s, j) for i in range(4) for s in range(2) for j in range(4)]
    def adj(a, b):
        i1, s1, j1 = a
        i2, s2, j2 = b
        if (s1, j1) == (s2, j2) and i1 != i2:
            return True
        if i1 == i2 and s1 != s2:
            return True
        return False
    return verts, adj


def graph_20():
    # K4 [] K5. (i,j); edge iff exactly one coordinate agrees.
    verts = [(i, j) for i in range(4) for j in range(5)]
    def adj(a, b):
        agree = (a[0] == b[0]) + (a[1] == b[1])
        return agree == 1
    return verts, adj


# ------------------------------------------------------------------ utilities

def degree_list(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return deg


def is_connected(n, edges):
    if n == 0:
        return False
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = [False] * n
    stack = [0]
    seen[0] = True
    cnt = 1
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if not seen[y]:
                seen[y] = True
                cnt += 1
                stack.append(y)
    return cnt == n


def enumerate_triangles(vertices, edgeset):
    """Full vertex-triple enumeration; membership test via edge set of idx pairs."""
    tris = []
    n = len(vertices)
    for a, b, c in itertools.combinations(range(n), 3):
        ab = (a, b) if a < b else (b, a)
        ac = (a, c) if a < c else (c, a)
        bc = (b, c) if b < c else (c, b)
        if ab in edgeset and ac in edgeset and bc in edgeset:
            tris.append((a, b, c))
    return tris


# ------------------------------------------------ incidence components + search

class DSU:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[rb] = ra


def triangle_edge_ids(tri):
    a, b, c = tri
    return [(a, b), (a, c), (b, c)]  # normalized (tri sorted ascending)


def component_optima(tris_in_comp):
    """Exact nu (max set of edge-disjoint triangles) and tau (min edge hitting
    set of triangles) within one connected component by exhaustive search.
    Components here are tiny (<=10 edges); brute force is trivial."""
    edge_ids = sorted({e for t in tris_in_comp for e in triangle_edge_ids(t)})
    m = len(edge_ids)
    tsets = [frozenset(triangle_edge_ids(t)) for t in tris_in_comp]

    # nu: backtracking over triangles, edge-disjointness (component has <= C(6..7,3) tris)
    best_pack = []

    def search_pack(start, chosen, used):
        nonlocal best_pack
        if len(chosen) > len(best_pack):
            best_pack = list(chosen)
        for k in range(start, len(tsets)):
            if tsets[k] & used:
                continue
            chosen.append(k)
            search_pack(k + 1, chosen, used | tsets[k])
            chosen.pop()

    search_pack(0, [], frozenset())

    # tau: smallest edge subset meeting every triangle (subset enumeration by size)
    best_cover = None
    for r in range(0, m + 1):
        found = False
        for combo in itertools.combinations(edge_ids, r):
            cs = set(combo)
            if all(cs & t for t in tsets):
                best_cover = sorted(cs)
                found = True
                break
        if found:
            break
    nu_c, tau_c = len(best_pack), len(best_cover)
    assert nu_c <= tau_c, "Erdos-Posa sanity within component violated"
    return nu_c, tau_c, best_pack, best_cover, edge_ids


def analyze(name, vertices, edges, check_degree, zero_tri_expected):
    t0 = time.time()
    n = len(vertices)
    eset = set(edges)
    eid = {e: k for k, e in enumerate(edges)}
    deg = degree_list(n, edges)
    conn = is_connected(n, edges)
    tris = enumerate_triangles(vertices, eset)

    # edges lying in zero triangles
    in_tri = set()
    for t in tris:
        in_tri.update(triangle_edge_ids(t))
    zero_tri = [e for e in edges if e not in in_tri]

    # connected components of triangle-edge incidence hypergraph (on edge-ids)
    dsu = DSU(len(edges))
    for t in tris:
        e = triangle_edge_ids(t)
        dsu.union(eid[e[0]], eid[e[1]])
        dsu.union(eid[e[0]], eid[e[2]])
    comp_tris = {}
    for t in tris:
        root = dsu.find(eid[triangle_edge_ids(t)[0]])
        comp_tris.setdefault(root, []).append(t)

    nu_total, tau_total = 0, 0
    packing, cover = [], []
    comp_summary = []
    for root in sorted(comp_tris):
        ct = sorted(comp_tris[root])
        nu_c, tau_c, bp, bc, ce = component_optima(ct)
        nu_total += nu_c
        tau_total += tau_c
        packing.extend(ct[k] for k in bp)
        cover.extend(bc)
        comp_summary.append({
            "triangles": len(ct),
            "edges": len(ce),
            "nu": nu_c,
            "tau": tau_c,
        })
    packing.sort()
    cover.sort()

    res = {
        "name": name,
        "n": n,
        "m": len(edges),
        "degree_check": {"expected": check_degree, "min": min(deg), "max": max(deg), "regular": len(set(deg)) == 1 and deg[0] == check_degree},
        "connected": conn,
        "triangles": len(tris),
        "edges_in_zero_triangles": len(zero_tri),
        "incidence_components": len(comp_summary),
        "component_summary": comp_summary,
        "nu_exact": nu_total,
        "tau_exact": tau_total,
        "packing_size": len(packing),
        "cover_size": len(cover),
        "runtime_sec": round(time.time() - t0, 4),
    }
    data = {
        "vertices": [list(v) for v in vertices],
        "vertex_labels": [vertex_label(v) for v in vertices],
        "edges_sorted": [list(e) for e in edges],
        "edges_by_label": sorted([sorted([vertex_label(vertices[u]), vertex_label(vertices[v])]) for u, v in edges]),
        "triangles_by_label": sorted(tuple(sorted(vertex_label(vertices[x]) for x in t)) for t in tris),
        "packing": [sorted([vertex_label(vertices[x]) for x in t]) for t in packing],
        "cover": sorted([sorted([vertex_label(vertices[u]), vertex_label(vertices[v])]) for u, v in cover]),
    }

    # sanity: packing really edge-disjoint, cover really hits all triangles
    used = set()
    for t in packing:
        for e in triangle_edge_ids(t):
            assert e not in used
            used.add(e)
    cset = set(cover)
    for t in tris:
        assert cset & set(triangle_edge_ids(t))
    return res, data


def verify_explicit_constructions(res32, data32, vertices32, eset32):
    """Baseline extras: explicit packing one triangle (i=0,1,2) per fixed (s,j);
    explicit cover via internal pairs (0,1),(2,3) per fixed (s,j) fiber."""
    idx = {v: k for k, v in enumerate(vertices32)}
    pack = []
    cov = []
    for s in range(2):
        for j in range(4):
            tri = tuple(sorted([idx[(0, s, j)], idx[(1, s, j)], idx[(2, s, j)]]))
            pack.append(tri)
            cov.append(tuple(sorted([idx[(0, s, j)], idx[(1, s, j)]])))
            cov.append(tuple(sorted([idx[(2, s, j)], idx[(3, s, j)]])))
    pack.sort(); cov.sort()
    # validate packing edge-disjoint & triangles valid
    es = set()
    for a, b, c in pack:
        assert (a, b) in eset32 and (a, c) in eset32 and (b, c) in eset32
        for e in [(a, b), (a, c), (b, c)]:
            assert e not in es
            es.add(e)
    cs = set(cov)
    assert all(cs & {(min(x, y), max(x, y)) for x, y in itertools.combinations(t, 2)}
               for t in enumerate_triangles(vertices32, eset32))
    return len(pack), len(cov)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def dump(path, obj):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1, sort_keys=False)
        f.write("\n")


def main():
    # ---- baseline n=32
    verts32, adj32 = graph_32()
    edges32, _ = build_edges(verts32, adj32)
    eset32 = set(edges32)
    res32, data32 = analyze("K4xK44_baseline_n32", verts32, edges32, 7, None)
    pk, cv = verify_explicit_constructions(res32, data32, verts32, eset32)
    res32["explicit_packing_per_fiber_size"] = pk
    res32["explicit_cover_per_fiber_size"] = cv
    res32["explicit_matches_optimum"] = (pk == res32["nu_exact"] and cv == res32["tau_exact"])
    dump("graph_32.json", data32)
    dump("result_32.json", res32)

    # ---- primary n=20
    verts20, adj20 = graph_20()
    edges20, _ = build_edges(verts20, adj20)
    res20, data20 = analyze("K4xK5_primary_n20", verts20, edges20, 7, None)
    dump("graph_20.json", data20)
    dump("result_20.json", res20)

    lines = []
    lines.append("Role B exact numerical verification (computational evidence only, no proof)")
    lines.append("Run command: python verify_candidate.py")
    lines.append("Python: " + sys.version.split()[0])
    lines.append("")
    for r in (res32, res20):
        lines.append(f"[{r['name']}] n={r['n']} m={r['m']} degree7_regular={r['degree_check']['regular']} "
                     f"connected={r['connected']} triangles={r['triangles']} "
                     f"edges_in_zero_triangles={r['edges_in_zero_triangles']}")
        lines.append(f"  incidence_components={r['incidence_components']} summary={r['component_summary']}")
        lines.append(f"  exact nu={r['nu_exact']} exact tau={r['tau_exact']} runtime={r['runtime_sec']}s")
        if "explicit_packing_per_fiber_size" in r:
            lines.append(f"  explicit fiber packing={r['explicit_packing_per_fiber_size']} "
                         f"cover={r['explicit_cover_per_fiber_size']} matches_optimum={r['explicit_matches_optimum']}")
        lines.append("")
    files = ["verify_candidate.py", "graph_32.json", "result_32.json", "graph_20.json", "result_20.json"]
    lines.append("sha256:")
    for fn in files:
        try:
            lines.append(f"  {fn}: {sha256(fn)}")
        except OSError as e:
            lines.append(f"  {fn}: <missing: {e}>")
    report = "\n".join(lines) + "\n"
    with open("report.txt", "w", encoding="utf-8") as f:
        f.write(report)
    # report.txt cannot contain its own final hash; append it after writing
    selfhash = sha256("report.txt")
    with open("report.txt", "a", encoding="utf-8") as f:
        f.write(f"  report.txt(body): {selfhash} (hash of all lines above)\n")
    report += f"  report.txt(body): {selfhash} (hash of all lines above)\n"
    print(report)


if __name__ == "__main__":
    main()
