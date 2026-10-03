#!/usr/bin/env python3
"""Bounded exact scan (role B_D, round 5). Connected NetworkX graph_atlas_g()
entries of order 3..7 (orders 0-2 cannot hold a triangle) with >= 1 triangle.
No upstream census/finder, no order-8 extension; wall cap WALL below.

Exact ordinary Tuza parameters by memoised combinatorial branching on edge
bitsets:  nu(H) = max # pairwise edge-disjoint triangles,
          tau(H) = min # edges meeting every triangle (0 if triangle-free).
Retain tight graphs (nu>0 and tau == 2*nu). For each triangle edge e test
tau(H-e) == tau(H); equality => e lies in NO minimum triangle cover. For each
positive (H,e), inspect 4-sets S with H[S] == P4 or K1,3 whose three induced
edges F are all free; for J <= F put H(J) = H - (F minus J), k = nu(H), and
test nu(H(empty)) = k-1, nu(H(J)) = k (J nonempty), tau(H(J)) = 2k-2+min(|J|,2).
Bounded computational evidence only; NOT a mathematical proof.
"""
import itertools, json, os, time
import networkx as nx
from networkx.generators.atlas import graph_atlas_g

T0 = time.time()
WALL = 215.0          # self-imposed budget inside the 240 s cap
SOFT = T0 + WALL - 6  # per-computation guard -> flagged as timeout
OUT = os.path.dirname(os.path.abspath(__file__))
os.makedirs(OUT, exist_ok=True)


class Timeout(Exception):
    pass


def tick():
    if time.time() > SOFT:
        raise Timeout()


def B(x):
    return bin(x).count("1")


class Ctx:
    """One atlas graph; edge-indexed bitmasks, nu/tau memoised."""

    def __init__(self, G, name):
        self.name, self.G = name, G
        self.V = sorted(G.nodes())
        self.E = [tuple(sorted(e)) for e in G.edges()]
        self.m = len(self.E)
        ix = {frozenset(e): i for i, e in enumerate(self.E)}
        self.tri, self.emask = [], {}
        for a, b, c in itertools.combinations(self.V, 3):
            s = [frozenset(p) for p in ((a, b), (a, c), (b, c))]
            if all(p in ix for p in s):
                self.tri.append(sum(1 << ix[p] for p in s))
        for i, e in enumerate(self.E):
            self.emask[e] = 1 << i
        self.full = (1 << self.m) - 1
        self._nu, self._tau = {}, {}

    def acts(self, key):
        return tuple(t for t in self.tri if t & ~key == 0)

    def nu(self, key):
        def rec(ms):
            tick()
            if not ms:
                return 0
            if ms in self._nu:
                return self._nu[ms]
            t = max(ms, key=lambda x: sum(1 for y in ms if y is not x and x & y))
            rest = tuple(y for y in ms if y is not t)
            keep = tuple(y for y in rest if not t & y)
            v = max(1 + rec(keep), rec(rest))
            self._nu[ms] = v
            return v

        return rec(self.acts(key))

    def tau(self, key):
        ms = self.acts(key)
        if not ms:
            return 0
        if key in self._tau:
            return self._tau[key]
        best = B(key)

        def lb(rem):
            g = n = 0
            for t in rem:
                if not t & g:
                    g |= t
                    n += 1
            return n

        def rec(rem, used):
            nonlocal best
            tick()
            if not rem:
                best = used
                return
            if used + lb(rem) >= best:
                return
            t = min(rem, key=lambda x: B(x & key))
            for i in (i for i in range(self.m) if (t >> i) & 1 and (key >> i) & 1):
                e = 1 << i
                rec([x for x in rem if not x & e], used + 1)
                if used + 1 >= best:
                    return

        rec(list(ms), 0)
        self._tau[key] = best
        return best


def free_edges(cx, tau_full):
    """Triangle edges e with tau(H-e) == tau(H) (e in no minimum cover)."""
    ontri = 0
    for t in cx.tri:
        ontri |= t
    return [i for i in range(cx.m)
            if (ontri >> i) & 1 and cx.tau(cx.full ^ (1 << i)) == tau_full]


def check_profile(cx, k, fset):
    """Fan F = fset (3 free edges). Return (ok, rows) for the 8 deletions."""
    fm = sum(1 << i for i in fset)
    rows, ok = [], True
    for r in range(8):
        J = [fset[b] for b in range(3) if (r >> b) & 1]   # kept edges of F
        key = cx.full & ~(fm & ~sum(1 << i for i in J))
        nu_j, tau_j = cx.nu(key), cx.tau(key)
        want_nu = k - 1 if not J else k
        want_tau = 2 * k - 2 + min(len(J), 2)
        good = (nu_j == want_nu and tau_j == want_tau)
        ok = ok and good
        rows.append({"J": [cx.E[i] for i in J], "nu": nu_j, "tau": tau_j,
                     "want_nu": want_nu, "want_tau": want_tau, "ok": good})
    return ok, rows


def fans(cx, free):
    """4-sets inducing P4 or K1,3 with all three induced edges in `free`."""
    fs = set(free)
    for S in itertools.combinations(cx.V, 4):
        idx = [i for i, (u, v) in enumerate(cx.E) if u in S and v in S]
        if len(idx) != 3 or not set(idx) <= fs:
            continue
        deg = sorted(sum(1 for i in idx if v in cx.E[i]) for v in S)
        if deg in ([1, 1, 2, 2], [1, 1, 1, 3]):     # P4 or K1,3
            yield S, idx, ("P4" if deg[0] == 1 and deg[2] == 2 else "K13")


def main():
    atlas = graph_atlas_g()
    st = {"atlas_entries_order_3_to_7": 0, "connected": 0, "scanned_with_triangles": 0, "timeouts": 0,
          "tight_tau_eq_2nu": 0, "positive_free_edge": 0, "profile_witnesses": 0, "deadline_hit": False}
    positives, profiles, slow, tight_census = [], [], [], []
    for gi, G in enumerate(atlas):
        if time.time() - T0 > WALL:
            st["deadline_hit"] = True
            break
        if G.order() > 7 or G.order() < 3:
            continue
        st["atlas_entries_order_3_to_7"] += 1
        if not nx.is_connected(G):
            continue
        st["connected"] += 1
        cx = Ctx(G, getattr(G, "name", "G%d" % gi))
        if not cx.tri:
            continue
        st["scanned_with_triangles"] += 1
        try:
            nu, tau = cx.nu(cx.full), cx.tau(cx.full)
        except Timeout:
            st["timeouts"] += 1
            slow.append({"graph": cx.name, "stage": "nu/tau"})
            continue
        if nu <= 0 or tau != 2 * nu:
            continue
        st["tight_tau_eq_2nu"] += 1
        try:
            fr = free_edges(cx, tau)
        except Timeout:
            st["timeouts"] += 1
            slow.append({"graph": cx.name, "stage": "free_edges"})
            continue
        tight_census.append({"graph": cx.name, "order": cx.G.order(), "nu": nu, "tau": tau,
                             "free_edges": len(fr), "each_triangle_edge_in_some_minimum_cover": not fr})
        if not fr:
            continue
        st["positive_free_edge"] += 1
        rec = {"graph": cx.name, "order": cx.G.order(), "edges": cx.E, "nu": nu, "tau": tau,
               "free_edges": [{"index": i, "edge": cx.E[i], "tau_H_minus_e": cx.tau(cx.full ^ (1 << i))}
                              for i in fr], "exact_method": "exact memoised bitset branching, completed", "fans": []}
        for S, idx, kind in fans(cx, fr):
            try:
                ok, rows = check_profile(cx, nu, idx)
            except Timeout:
                st["timeouts"] += 1
                slow.append({"graph": cx.name, "stage": "profile", "fan": list(S)})
                ok, rows = False, []
            if ok:
                st["profile_witnesses"] += 1
                rec["fans"].append({"S": list(S), "type": kind,
                                    "F": [cx.E[i] for i in idx],
                                    "rows": rows})
        positives.append(rec)
        if len(rec["fans"]):
            profiles.append(rec["graph"])
    def done(stage):
        return all(s["stage"] != stage for s in slow)
    ph = {"enumeration": not st["deadline_hit"], "nu_tau_exact": done("nu/tau"),
          "free_edge_test": done("free_edges"),
          "fan_profile_stage": done("profile") if st["positive_free_edge"] else None}
    complete = all(v is not False for v in ph.values())   # None = phase not applicable
    summary = {"role": "B_D", "task": "bounded exact atlas scan (order<=7, connected, triangles>0)",
               "status": "COMPLETE within budget" if complete else "PARTIAL (deadline or timeout)",
               "phases": ph, "budget_s": 240, "self_cap_s": WALL,
               "wall_s": round(time.time() - T0, 2), "counts": st, "tight_census": tight_census,
               "graphs_with_profile_witness": profiles, "timed_out_or_aborted": slow,
               "note": "exact per-graph branch-and-bound completions only; no scipy/MILP used; "
                       "bounded computational evidence, not a proof"}
    with open(os.path.join(OUT, "scan_tight_summary.json"), "w") as f:
        json.dump(summary, f, indent=1, default=list)
    with open(os.path.join(OUT, "scan_tight_witnesses.json"), "w") as f:
        concl = ("no triangle edge e of any tight atlas graph in the scanned range satisfies "
                 "tau(H-e)=tau(H); fan/profile stage not triggered"
                 if (complete and not st["positive_free_edge"]) else
                 "n_positives=%d, exported=%d; no negative conclusion, see positives"
                 % (st["positive_free_edge"], len(positives)))
        json.dump({"positives": positives, "n_positives": len(positives), "export_truncated": False,
                   "scan_status": summary["status"], "profile_witnesses": st["profile_witnesses"],
                   "conclusion": concl}, f, indent=1, default=list)
    print(json.dumps(summary, indent=1, default=list))


if __name__ == "__main__":
    main()
