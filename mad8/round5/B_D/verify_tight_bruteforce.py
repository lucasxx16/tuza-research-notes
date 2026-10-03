#!/usr/bin/env python3
"""Independent exact re-check of scan_tight_atlas.py (role B_D, bounded range:
connected atlas graphs, order <= 7, at least one triangle).  Uses a completely
different enumeration (no bitset memoisation, no branch-and-bound incumbent):
  bnu  : DFS over triangle subsets with a counting bound
  btau : increasing-size edge-subset enumeration (first hit is optimal)
Also recomputes tau(H-e) for every triangle edge e of every tight graph.
Zero reported mismatches means the scan's exact values are reproduced.
Computational cross-check, not a proof.
"""
import itertools, json, os, time
import networkx as nx
from networkx.generators.atlas import graph_atlas_g
from scan_tight_atlas import Ctx

OUT = os.path.dirname(os.path.abspath(__file__))


def tri_edges(G):
    return [frozenset((frozenset(p) for p in ((a, b), (a, c), (b, c))))
            for a, b, c in itertools.combinations(G.nodes(), 3)
            if G.has_edge(a, b) and G.has_edge(a, c) and G.has_edge(b, c)]


def btau(T, E):
    if not T:
        return 0
    for k in range(len(E) + 1):
        for c in itertools.combinations(E, k):
            s = set(c)
            if all(t & s for t in T):
                return k


def bnu(T):
    best = [0]

    def dfs(i, used, cnt):
        if cnt + (len(T) - i) <= best[0]:
            return
        best[0] = max(best[0], cnt)
        for j in range(i, len(T)):
            if not used & T[j]:
                dfs(j + 1, used | T[j], cnt + 1)

    dfs(0, frozenset(), 0)
    return best[0]


def main():
    t0, mism, tight, free = time.time(), [], [], 0
    for gi, G in enumerate(graph_atlas_g()):
        if G.order() > 7 or G.order() < 3 or not nx.is_connected(G):
            continue
        cx = Ctx(G, getattr(G, "name", "G%d" % gi))
        E = [frozenset(e) for e in G.edges()]
        T = tri_edges(G)
        if not T:
            continue
        bt, bn = btau(T, E), bnu(T)
        if bt != cx.tau(cx.full):
            mism.append({"graph": cx.name, "what": "tau", "brute": bt, "scan": cx.tau(cx.full)})
        if bn != cx.nu(cx.full):
            mism.append({"graph": cx.name, "what": "nu", "brute": bn, "scan": cx.nu(cx.full)})
        fr = 0
        if bn > 0 and bt == 2 * bn:
            for i, e in enumerate(E):
                if not any(e in t for t in T):
                    continue
                t2 = btau([t for t in T if e not in t], [x for x in E if x != e])
                if t2 != cx.tau(cx.full ^ (1 << i)):
                    mism.append({"graph": cx.name, "what": "tau(H-e)", "edge": sorted(map(sorted, e)),
                                 "brute": t2, "scan": cx.tau(cx.full ^ (1 << i))})
                if t2 == bt:
                    fr += 1
            tight.append({"graph": cx.name, "order": G.order(), "nu": bn, "tau": bt, "free_edges": fr})
            free += fr
    res = {"wall_s": round(time.time() - t0, 2), "range": "connected atlas, order<=7, triangles>0",
           "mismatches": mism, "n_mismatches": len(mism), "tight_graphs": tight,
           "n_tight": len(tight), "free_edge_positives": free,
           "status": ("scan values reproduced by independent enumeration"
                      if not mism else "MISMATCHES against scan, see mismatches list")}
    sp = os.path.join(OUT, "scan_tight_summary.json")
    if os.path.exists(sp):
        sg = json.load(open(sp))
        res["agreement_with_saved_scan_metadata"] = {
            "same_tight_graphs": [t["graph"] for t in tight] == [c["graph"] for c in sg["tight_census"]],
            "same_free_edge_counts": [t["free_edges"] for t in tight] == [c["free_edges"] for c in sg["tight_census"]],
            "scan_status": sg["status"], "scan_wall_s": sg["wall_s"], "scan_counts": sg["counts"]}
    json.dump(res, open(os.path.join(OUT, "verify_tight_bruteforce.json"), "w"),
              indent=1, default=list)
    print(json.dumps({k: res[k] for k in
                      ("wall_s", "n_mismatches", "n_tight", "free_edge_positives", "status")}))


if __name__ == "__main__":
    main()
