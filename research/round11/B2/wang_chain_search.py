#!/usr/bin/env python3
"""ROUND 11 / B2 -- independent numerical attack on the inequality a+b+c <= n
inside Wang's triangle-packing chain.  Nothing here is a proof or a theorem:
every number is a certified fact about the printed instance only.

THE CHAIN UNDER TEST (every stage MAXIMUM, exactly as imposed by the parent):
  P      maximum edge-disjoint triangle packing of G;  n = |P|;  O = E(P)
         ("old" edge = edge of O;  type(t) = #edges of t lying in O)
  A      maximum packing of ALL type-1 triangles of G (exactly 1 old edge), a=|A|
  G'     = G - E(A)
  P'     packing of G' maximizing FIRST b = #type-2 triangles (exactly 2 old
         edges), THEN total size m = |P'|        (lexicographic, in that order)
  B(P')  = all old edges used by triangles of P'
  H      = G' - B(P')
  Q      maximum packing of ALL triangles of H, c = |Q|
  violation test: a + b + c > n  (reported as the exact integer margin a+b+c-n)

ENGINES (deliberately doubled, no shared code path):
  A  exact integer bitset branch & bound, memoised on (candidate index,
     used-edge bitmask).  Exhaustive iff it returned without the deadline.
  B  scipy.optimize.milp (HiGHS): accepted ONLY if status == 0 and success,
     the solution is integral to 1e-6, and the decoded triangle set passes an
     independent literal disjointness / type / count / equality-row re-check.
  A stage is certified only when A (exhaustive) and B agree on the value and
  the printed witness is literally valid.  The lexicographic stage is certified
  by (i) exact max-b, (ii) exact scalarised max(W*b+m) with W > max size, and
  (iii) a two-stage MILP: max b, then max m subject to the equality b = b*.

Tie policy: at each stage the optimum set is enumerated only up to a cap and a
seeded random SUBSET of the enumerated optima is expanded further.  A found
violation therefore refutes the "for ALL legal choices" reading of a+b+c<=n; it
says nothing about the "there EXISTS a good choice" reading.  A clean run is a
bounded search and does not prove the inequality.

Usage:
  python wang_chain_search.py search  [--budget 110] [--max-graphs 200] [--seed 1102]
                                      [--only-complete] [--keep-going]
                                      [--cap 60 --kP 4 --kA 3 --kPP 3]
                                      [--out certificate.json]
  python wang_chain_search.py reverify [--file certificate.json] [--chain 0]
        READ-ONLY: re-parses the printed graph + printed chain, recomputes every
        stage with both engines and compares with the stored checks.  Writes
        nothing.
Exit codes: search 0 = run completed and written;
            reverify 0 = all checks pass and match the stored certificate,
                     1 = a literal/optimality check failed,
                     2 = something is not certified / does not match.
"""

import argparse
import json
import os
import random
import sys
import time

import networkx as nx

W_TYPES = ("type_of_P_triangles", "type_of_A_triangles",
           "type_of_Pprime_triangles", "type_of_Q_triangles")


class Deadline(Exception):
    pass


def pc(x):
    return bin(x).count("1")


def bits_of(mask, length):
    return [e for e in range(length) if (mask >> e) & 1]


# --------------------------------------------------------------------------- #
# graph bookkeeping: every set of edges is a bitmask over this graph's edges
# --------------------------------------------------------------------------- #
class Ctx:
    def __init__(self, nv, edge_pairs):
        self.nv = int(nv)
        edges, seen = [], set()
        for u, v in edge_pairs:
            u, v = int(u), int(v)
            assert 0 <= u < self.nv and 0 <= v < self.nv and u != v, "bad edge"
            if u > v:
                u, v = v, u
            if (u, v) in seen:
                continue
            seen.add((u, v))
            edges.append((u, v))
        self.edges = edges
        self.eidx = {e: i for i, e in enumerate(edges)}
        adj = [set() for _ in range(self.nv)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        tris = []
        for a in range(self.nv):
            for b in adj[a]:
                if b <= a:
                    continue
                for c in adj[b]:
                    if c <= b:
                        continue
                    if c in adj[a]:
                        tris.append((a, b, c))
        self.tris = tris
        self.tmask, self.tedges = [], []
        for (a, b, c) in tris:
            es = [self.eidx[(a, b)], self.eidx[(a, c)], self.eidx[(b, c)]]
            m = 0
            for e in es:
                m |= 1 << e
            self.tmask.append(m)
            self.tedges.append(es)
        self.allmask = (1 << len(edges)) - 1

    # --- helpers ---------------------------------------------------------
    def present_tris(self, present):
        return [i for i, m in enumerate(self.tmask) if m & ~present == 0]

    def edges_of(self, idxs):
        out = set()
        for i in idxs:
            out.update(self.tedges[i])
        return out

    def mask_of(self, idxs):
        m = 0
        for i in idxs:
            m |= self.tmask[i]
        return m

    def mask_of_edges(self, es):
        m = 0
        for e in es:
            m |= 1 << e
        return m

    def pairs(self, edge_idxs):
        return [list(self.edges[e]) for e in sorted(edge_idxs)]

    def tri_index(self, tri):
        k = tuple(sorted(int(x) for x in tri))
        assert len(k) == 3, "not a triangle: %s" % (tri,)
        try:
            return self.tris.index(k)
        except ValueError:
            raise AssertionError("printed triangle %s is not a triangle of G" % (k,))

    def typ(self, i, Omask):
        return pc(self.tmask[i] & Omask)


# --------------------------------------------------------------------------- #
# engine A -- exact integer bitset branch & bound (memoised)
# --------------------------------------------------------------------------- #
class Exact:
    """maximise sum weights[i] over pairwise EDGE-disjoint selections of masks"""

    def __init__(self, masks, weights, deadline, stats):
        self.c = list(masks)
        self.w = list(weights)
        self.n = len(self.c)
        self.dl = deadline
        self.st = stats
        self.memo = {}
        self.best = None

    def _tick(self):
        self.st["nodes"] += 1
        if self.st["nodes"] >= self.st["next_check"]:
            self.st["next_check"] = self.st["nodes"] + 4096
            if time.monotonic() > self.dl:
                raise Deadline()

    def val(self, i, avail):
        if i >= self.n:
            return 0
        key = (i, avail)
        got = self.memo.get(key)
        if got is not None:
            return got
        self._tick()
        m, w = self.c[i], self.w[i]
        best = self.val(i + 1, avail)
        if (m & avail) == 0:
            cand = w + self.val(i + 1, avail | m)
            if cand > best:
                best = cand
        self.memo[key] = best
        return best

    def optimum(self):
        if self.best is None:
            self.best = self.val(0, 0)
        return self.best

    def optima(self, cap):
        """return up to `cap` optimal selections (indices into self.c) and
        truncated=True if more than cap exist (enumeration stopped early)."""
        if self.best is None:
            self.optimum()
        sols, trunc = [], [False]

        def walk(i, avail, cur, chosen):
            if len(sols) >= cap:
                trunc[0] = True
                return
            if cur == self.best:                     # weights are >= 0
                sols.append(tuple(chosen))
                return
            if i >= self.n:
                return
            self._tick()
            if cur + self.val(i, avail) < self.best:
                return
            m, w = self.c[i], self.w[i]
            if (m & avail) == 0 and cur + w + self.val(i + 1, avail | m) >= self.best:
                chosen.append(i)
                walk(i + 1, avail | m, cur + w, chosen)
                chosen.pop()
            if cur + self.val(i + 1, avail) >= self.best:
                walk(i + 1, avail, cur, chosen)

        walk(0, 0, 0, [])
        return sols, trunc[0]


# --------------------------------------------------------------------------- #
# engine B -- scipy.optimize.milp (HiGHS)
# --------------------------------------------------------------------------- #
def milp_pack(tedges, weights, deadline, eq=None):
    """tedges: list of edge-index lists (one per candidate triangle).
    maximise sum weights[j] x_j s.t. each edge used at most once, x binary,
    and (optionally) sum eq[0][j] x_j == eq[1].  Never guesses."""
    out = {"engine": "scipy.optimize.milp(HiGHS)", "certified": False}
    nt = len(tedges)
    if nt == 0:
        out.update(certified=True, status="no_candidates", value=0, sel=[])
        return out
    try:
        import numpy as np
        from scipy.optimize import Bounds, LinearConstraint, milp
    except Exception as exc:
        out["error"] = repr(exc)
        return out
    ne = 1 + max((e for es in tedges for e in es), default=0)
    A = np.zeros((ne, nt), dtype=int)
    for j, es in enumerate(tedges):
        for e in es:
            A[e, j] = 1
    cons = [LinearConstraint(A, np.full(ne, -np.inf), np.ones(ne, dtype=float))]
    if eq is not None:
        row = np.asarray(eq[0], dtype=float).reshape(1, nt)
        cons.append(LinearConstraint(row, [float(eq[1])], [float(eq[1])]))
    left = deadline - time.monotonic()
    if left <= 0.05:
        out["error"] = "no_time_left"
        return out
    try:
        res = milp(c=-np.asarray(weights, dtype=float), constraints=cons,
                   integrality=np.ones(nt, dtype=int), bounds=Bounds(0, 1),
                   options={"time_limit": float(left), "mip_rel_gap": 0.0,
                            "primal_feasibility_tolerance": 1e-9,
                            "dual_feasibility_tolerance": 1e-9})
    except Exception as exc:
        out["error"] = repr(exc)
        return out
    out["status"] = int(res.status)
    out["success"] = bool(getattr(res, "success", False))
    out["message"] = str(getattr(res, "message", ""))
    if res.status != 0 or not out["success"] or res.x is None:
        return out
    x = [float(v) for v in res.x]
    if any(abs(v - round(v)) > 1e-6 for v in x):
        out["error"] = "non_integral"
        return out
    sel = [j for j, v in enumerate(x) if round(v) == 1]
    used = set()
    for j in sel:
        for e in tedges[j]:
            if e in used:
                out["error"] = "solver_witness_not_edge_disjoint"
                return out
            used.add(e)
    val = int(sum(weights[j] for j in sel))
    if abs((-res.fun) - val) > 1e-6:
        out["error"] = "objective_mismatch"
        return out
    if eq is not None and int(sum(eq[0][j] for j in sel)) != int(eq[1]):
        out["error"] = "equality_row_violated"
        return out
    out.update(certified=True, value=val, sel=sel, milp_size=len(sel))
    return out


# --------------------------------------------------------------------------- #
# one complete legal chain, printed literally
# --------------------------------------------------------------------------- #
def chain_literal(ctx, Psel, Asel, Ppsel, Qsel, Omask):
    trip = lambda i: list(ctx.tris[i])
    Bmask = ctx.mask_of_edges(e for i in Ppsel for e in ctx.tedges[i]
                              if (ctx.tmask[i] & Omask) >> e & 1)
    present = ctx.allmask & ~ctx.mask_of(Asel)      # G' = G - E(A)
    present &= ~Bmask                               # H = G' - B(P')  (old edges only)
    return {
        "vertices": list(range(ctx.nv)),
        "edges": ctx.pairs(range(len(ctx.edges))),
        "P": [trip(i) for i in Psel],
        "O_edges": ctx.pairs(ctx.edges_of(Psel)),
        "A": [trip(i) for i in Asel],
        "E_A_edges": ctx.pairs(ctx.edges_of(Asel)),
        "Pprime": [trip(i) for i in Ppsel],
        "E_Pprime_edges": ctx.pairs(ctx.edges_of(Ppsel)),
        "B_edges": ctx.pairs(bits_of(Bmask, len(ctx.edges))),
        "H_edges": ctx.pairs(bits_of(present, len(ctx.edges))),
        "Q": [trip(i) for i in Qsel],
        "types_relative_to_O": {
            "P": [3 for _ in Psel],
            "A": [ctx.typ(i, Omask) for i in Asel],
            "Pprime": [ctx.typ(i, Omask) for i in Ppsel],
            "Q": [ctx.typ(i, Omask) for i in Qsel]},
    }


def analyse_graph(name, ctx, rng, cfg, deadline, stats):
    res = {"id": name, "nv": ctx.nv, "ne": len(ctx.edges), "triangles": len(ctx.tris),
           "n": None, "skipped": None, "chains": 0, "margin_max": None,
           "best_chain": None, "violations": [], "timeouts": 0, "margin_hist": {},
           "P_optima_enumerated": 0, "P_optima_truncated": False,
           "A_optima_truncated": False, "Pprime_optima_truncated": False}
    if not ctx.tris:
        res["skipped"] = "triangle_free"
        res["margin_max"] = 0
        return res
    # ---------------- stage P: maximum packing of all triangles -----------
    ex = Exact(ctx.tmask, [1] * len(ctx.tris), deadline, stats)
    try:
        n = ex.optimum()
        P_sols, P_trunc = ex.optima(cfg["cap"])
    except Deadline:
        res.update(skipped="deadline_stageP", timeouts=res["timeouts"] + 1)
        return res
    res["n"], res["P_optima_enumerated"], res["P_optima_truncated"] = n, len(P_sols), P_trunc
    if n == 0 or not P_sols:
        res["skipped"] = "empty_packing"
        res["margin_max"] = 0
        return res
    res["margin_max"] = -10 ** 9
    for Psel in rng.sample(P_sols, min(cfg["kP"], len(P_sols))):
        if res.get("chain_cap_reached"):
            break
        Omask = 0
        for i in Psel:
            Omask |= ctx.tmask[i]
        # ------------- stage A: maximum packing of type-1 triangles -------
        A_cand = [i for i in range(len(ctx.tris)) if ctx.typ(i, Omask) == 1]
        if A_cand:
            exA = Exact([ctx.tmask[i] for i in A_cand], [1] * len(A_cand), deadline, stats)
            try:
                a = exA.optimum()
                A_sols, A_trunc = exA.optima(cfg["cap"])
            except Deadline:
                res["timeouts"] += 1
                continue
            A_sets = [tuple(A_cand[j] for j in s) for s in A_sols]
            res["A_optima_truncated"] = A_trunc
        else:
            a, A_sets, A_trunc = 0, [()], False
        for Asel in rng.sample(A_sets, min(cfg["kA"], len(A_sets))):
            if res.get("chain_cap_reached"):
                break
            present_g = ctx.allmask & ~ctx.mask_of(Asel)
            # ---------- stage P': lexicographic max (b then m) in G' ------
            PP_cand = ctx.present_tris(present_g)
            if PP_cand:
                W = len(PP_cand) + 1
                is2 = [1 if ctx.typ(i, Omask) == 2 else 0 for i in PP_cand]
                exB = Exact([ctx.tmask[i] for i in PP_cand], is2, deadline, stats)
                exL = Exact([ctx.tmask[i] for i in PP_cand], [W * v + 1 for v in is2],
                            deadline, stats)
                try:
                    bmax = exB.optimum()
                    lex = exL.optimum()
                    L_sols, L_trunc = exL.optima(cfg["cap"])
                except Deadline:
                    res["timeouts"] += 1
                    continue
                res["Pprime_optima_truncated"] = L_trunc
                res["bmax_at_this_A"] = bmax
                res["mmax_at_bmax"] = lex - W * bmax
                PP_sets = []
                for s in L_sols:
                    idx = tuple(PP_cand[j] for j in s)
                    PP_sets.append((idx, sum(is2[j] for j in s), len(idx)))
            else:
                PP_sets, L_trunc = [((), 0, 0)], False
            for (Ppsel, bb, mm) in rng.sample(PP_sets, min(cfg["kPP"], len(PP_sets))):
                # ---------------- stage Q: max packing of H = G' - B(P') ---
                # B(P') = the OLD edges used by P'; the new edges of P' stay in H
                Bmask = ctx.mask_of_edges(e for i in Ppsel for e in ctx.tedges[i]
                                          if (ctx.tmask[i] & Omask) >> e & 1)
                present_h = present_g & ~Bmask
                Q_cand = ctx.present_tris(present_h)
                if Q_cand:
                    exQ = Exact([ctx.tmask[i] for i in Q_cand], [1] * len(Q_cand),
                                deadline, stats)
                    try:
                        c = exQ.optimum()
                        Q_sols, _ = exQ.optima(1)
                    except Deadline:
                        res["timeouts"] += 1
                        continue
                    Qsel = tuple(Q_cand[j] for j in Q_sols[0]) if Q_sols else ()
                else:
                    c, Qsel = 0, ()
                res["chains"] += 1
                margin = a + bb + c - n
                res["h_tri_pos"] = res.get("h_tri_pos", 0) + (1 if Q_cand else 0)
                res["h_type_hist"] = res.setdefault("h_type_hist", {})
                for i in Q_cand:
                    t = str(ctx.typ(i, Omask))
                    res["h_type_hist"][t] = res["h_type_hist"].get(t, 0) + 1
                res["a_max"] = max(res.get("a_max", 0), a)
                res["b_max"] = max(res.get("b_max", 0), bb)
                res["c_max"] = max(res.get("c_max", 0), c)
                res["ab_max"] = max(res.get("ab_max", 0), a + bb)
                if c > 0:
                    res["chains_c_pos"] = res.get("chains_c_pos", 0) + 1
                res["margin_hist"][margin] = res["margin_hist"].get(margin, 0) + 1
                rec = {"name": name, "nv": ctx.nv, "edges": [list(e) for e in ctx.edges],
                       "n": n, "a": a, "b": bb, "m": mm, "c": c, "margin": margin,
                       "lex_optima_truncated": L_trunc,
                       "literal": chain_literal(ctx, Psel, Asel, Ppsel, Qsel, Omask)}
                if margin > res["margin_max"]:
                    res["margin_max"], res["best_chain"] = margin, rec
                if margin > 0:
                    res["violations"].append(rec)
                pool = cfg.get("pool")
                if pool is not None:                       # reservoir sample of chains
                    pool["n"] += 1
                    if len(pool["res"]) < pool["k"]:
                        pool["res"].append(rec)
                    else:
                        j = pool["rng"].randrange(pool["n"])
                        if j < pool["k"]:
                            pool["res"][j] = rec
                if res["chains"] >= cfg["max_chains"]:
                    res["chain_cap_reached"] = True
                    break
    return res


# --------------------------------------------------------------------------- #
# full dual certification of one printed chain
# --------------------------------------------------------------------------- #
def certify_chain(ctx, chain, deadline):
    cert = {"all_pass": True, "certified": True, "checks": {}}
    note = cert["checks"]
    lit = chain["literal"]
    try:
        Psel = [ctx.tri_index(t) for t in lit["P"]]
        Asel = [ctx.tri_index(t) for t in lit["A"]]
        Ppsel = [ctx.tri_index(t) for t in lit["Pprime"]]
        Qsel = [ctx.tri_index(t) for t in lit["Q"]]
    except AssertionError as exc:
        cert.update(all_pass=False, certified=False, fatal=str(exc))
        return cert
    Omask = ctx.mask_of(Psel)

    def disjoint(idxs):
        used = set()
        for i in idxs:
            for e in ctx.tedges[i]:
                if e in used:
                    return False
                used.add(e)
        return True

    stats = {"nodes": 0, "next_check": 4096}
    try:
        # ---- stage P: n = maximum packing size of G ----
        n_dfs = Exact(ctx.tmask, [1] * len(ctx.tris), deadline, stats).optimum()
        mP = milp_pack(ctx.tedges, [1] * len(ctx.tris), deadline)
        note["stageP_n_maximum"] = {
            "dfs": n_dfs, "milp_certified": mP.get("certified"), "milp_status": mP.get("status"),
            "milp_value": mP.get("value"), "milp_error": mP.get("error"),
            "claimed": chain["n"], "printed_witness_size": len(Psel),
            "printed_witness_edge_disjoint": disjoint(Psel),
            "all_three_agree": n_dfs == chain["n"] == len(Psel) and
            bool(mP.get("certified")) and mP.get("value") == chain["n"]}
        # ---- stage A: a = maximum packing among ALL type-1 triangles ----
        A_cand = [i for i in range(len(ctx.tris)) if ctx.typ(i, Omask) == 1]
        a_dfs = Exact([ctx.tmask[i] for i in A_cand], [1] * len(A_cand),
                      deadline, stats).optimum() if A_cand else 0
        mA = milp_pack([ctx.tedges[i] for i in A_cand], [1] * len(A_cand), deadline) \
            if A_cand else milp_pack([], [], deadline)
        note["stageA_a_maximum_among_type1"] = {
            "type1_candidates": [list(ctx.tris[i]) for i in A_cand],
            "n_candidates": len(A_cand), "dfs": a_dfs,
            "milp_certified": mA.get("certified"), "milp_status": mA.get("status"),
            "milp_value": mA.get("value"), "milp_error": mA.get("error"),
            "claimed": chain["a"], "printed_witness_size": len(Asel),
            "printed_witness_edge_disjoint": disjoint(Asel),
            "printed_witness_all_type1": all(ctx.typ(i, Omask) == 1 for i in Asel),
            "all_three_agree": a_dfs == chain["a"] == len(Asel) and
            bool(mA.get("certified")) and mA.get("value") == chain["a"]}
        # ---- stage P': lex (b then m) in G' = G - E(A) ----
        present_g = ctx.allmask & ~ctx.mask_of(Asel)
        PP_cand = ctx.present_tris(present_g)
        W = len(PP_cand) + 1
        is2 = [1 if ctx.typ(i, Omask) == 2 else 0 for i in PP_cand]
        b_dfs = Exact([ctx.tmask[i] for i in PP_cand], is2, deadline, stats).optimum() \
            if PP_cand else 0
        lex_dfs = Exact([ctx.tmask[i] for i in PP_cand], [W * v + 1 for v in is2],
                        deadline, stats).optimum() if PP_cand else 0
        mB = milp_pack([ctx.tedges[i] for i in PP_cand], is2, deadline) if PP_cand \
            else milp_pack([], [], deadline)
        mC = milp_pack([ctx.tedges[i] for i in PP_cand], [1] * len(PP_cand), deadline,
                       eq=([is2[j] for j in range(len(PP_cand))], chain["b"])) \
            if PP_cand else milp_pack([], [], deadline)
        b_of_pp = sum(1 for i in Ppsel if ctx.typ(i, Omask) == 2)
        m_given_b_dfs = lex_dfs - W * b_dfs
        note["stagePprime_b_maximality"] = {
            "Gprime_edges": ctx.pairs(e for e in range(len(ctx.edges))
                                      if (present_g >> e) & 1),
            "candidate_triangles": [list(ctx.tris[i]) for i in PP_cand],
            "types": {str(ctx.tris[i]): ctx.typ(i, Omask) for i in PP_cand},
            "dfs_b_max": b_dfs, "milp_certified": mB.get("certified"),
            "milp_status": mB.get("status"), "milp_value": mB.get("value"),
            "milp_error": mB.get("error"), "claimed_b": chain["b"],
            "printed_witness_b": b_of_pp,
            "printed_witness_edge_disjoint": disjoint(Ppsel),
            "printed_witness_inside_Gprime": all(
                ctx.tmask[i] & ~present_g == 0 for i in Ppsel),
            "all_agree": b_dfs == chain["b"] == b_of_pp and bool(mB.get("certified"))
            and mB.get("value") == chain["b"]}
        note["stagePprime_m_maximality_given_b"] = {
            "lex_scalar_weight_W": W, "dfs_lex_value": lex_dfs,
            "dfs_m_given_bmax": m_given_b_dfs,
            "expected_lex": W * chain["b"] + chain["m"],
            "milp_certified_b_fixed": mC.get("certified"), "milp_status": mC.get("status"),
            "milp_value_m_given_b": mC.get("value"), "milp_error": mC.get("error"),
            "claimed_m": chain["m"], "printed_witness_size": len(Ppsel),
            "lex_order_proof_note": "b maximised first (stage above); m then maximised "
                                    "under the equality b=b*; scalarised exact run agrees",
            "all_agree": m_given_b_dfs == chain["m"] == len(Ppsel) and
            lex_dfs == W * chain["b"] + chain["m"] and
            bool(mC.get("certified")) and mC.get("value") == chain["m"]}
        # ---- stage Q: c = maximum packing of all triangles of H=G'-B(P') ----
        Bmask = 0
        for i in Ppsel:
            for e in ctx.tedges[i]:
                if (ctx.tmask[i] & Omask) >> e & 1:
                    Bmask |= 1 << e
        present_h = present_g & ~Bmask
        Q_cand = ctx.present_tris(present_h)
        c_dfs = Exact([ctx.tmask[i] for i in Q_cand], [1] * len(Q_cand), deadline,
                      stats).optimum() if Q_cand else 0
        mQ = milp_pack([ctx.tedges[i] for i in Q_cand], [1] * len(Q_cand), deadline) \
            if Q_cand else milp_pack([], [], deadline)
        recomp_H = ctx.pairs(e for e in range(len(ctx.edges)) if (present_h >> e) & 1)
        note["stageQ_c_maximum"] = {
            "B_edges_recomputed": ctx.pairs(e for e in range(len(ctx.edges))
                                            if (Bmask >> e) & 1),
            "H_edges_recomputed": recomp_H,
            "H_edges_printed": lit["H_edges"],
            "H_edges_match": sorted(map(tuple, recomp_H)) == sorted(map(tuple, lit["H_edges"])),
            "triangles_of_H": [list(ctx.tris[i]) for i in Q_cand],
            "dfs": c_dfs, "milp_certified": mQ.get("certified"),
            "milp_status": mQ.get("status"), "milp_value": mQ.get("value"),
            "milp_error": mQ.get("error"), "claimed": chain["c"],
            "printed_witness_size": len(Qsel),
            "printed_witness_edge_disjoint": disjoint(Qsel),
            "printed_witness_inside_H": all(ctx.tmask[i] & ~present_h == 0 for i in Qsel),
            "all_three_agree": c_dfs == chain["c"] == len(Qsel) and
            bool(mQ.get("certified")) and mQ.get("value") == chain["c"]
            and sorted(map(tuple, recomp_H)) == sorted(map(tuple, lit["H_edges"]))}
        # ---- printed sets vs recomputed sets (graph identity, O, E(A), B, types)
        srt = lambda pl: sorted(tuple(sorted(p)) for p in pl)
        recomp_O = ctx.pairs(ctx.edges_of(Psel))
        recomp_EA = ctx.pairs(ctx.edges_of(Asel))
        recomp_B = ctx.pairs(e for e in range(len(ctx.edges)) if (Bmask >> e) & 1)
        recomp_types = {"P": [ctx.typ(i, Omask) for i in Psel],
                        "A": [ctx.typ(i, Omask) for i in Asel],
                        "Pprime": [ctx.typ(i, Omask) for i in Ppsel],
                        "Q": [ctx.typ(i, Omask) for i in Qsel]}
        note["printed_sets_consistency"] = {
            "graph_edges_match": srt(lit["edges"]) == srt(ctx.pairs(range(len(ctx.edges)))),
            "O_edges_match": srt(lit["O_edges"]) == srt(recomp_O),
            "E_A_edges_match": srt(lit["E_A_edges"]) == srt(recomp_EA),
            "B_edges_match": srt(lit["B_edges"]) == srt(recomp_B),
            "types_match": all(lit["types_relative_to_O"][k] == recomp_types[k]
                               for k in recomp_types),
            "P_types_all_3": all(t == 3 for t in recomp_types["P"]),
            "A_types_all_1": all(t == 1 for t in recomp_types["A"]),
            "recomputed_types": recomp_types,
            "all_three_agree": (srt(lit["edges"]) == srt(ctx.pairs(range(len(ctx.edges))))
                                and srt(lit["O_edges"]) == srt(recomp_O)
                                and srt(lit["E_A_edges"]) == srt(recomp_EA)
                                and srt(lit["B_edges"]) == srt(recomp_B)
                                and all(lit["types_relative_to_O"][k] == recomp_types[k]
                                        for k in recomp_types)
                                and all(t == 3 for t in recomp_types["P"])
                                and all(t == 1 for t in recomp_types["A"]))}
        # ---- arithmetic ----
        note["arithmetic"] = {
            "a": chain["a"], "b": chain["b"], "m": chain["m"], "c": chain["c"],
            "n": chain["n"], "a_plus_b_plus_c": chain["a"] + chain["b"] + chain["c"],
            "margin_a+b+c-n": chain["a"] + chain["b"] + chain["c"] - chain["n"],
            "violation_a+b+c_greater_than_n":
                chain["a"] + chain["b"] + chain["c"] > chain["n"],
            "recorded_margin_consistent": chain["margin"] ==
            chain["a"] + chain["b"] + chain["c"] - chain["n"]}
    except Deadline:
        cert["fatal"] = "deadline during certification"
    except AssertionError as exc:
        cert["fatal"] = str(exc)
    for k, v in note.items():
        if "all_three_agree" in v and not v["all_three_agree"]:
            cert["all_pass"] = False
        if "all_agree" in v and not v["all_agree"]:
            cert["all_pass"] = False
    if not note.get("arithmetic", {}).get("recorded_margin_consistent", False):
        cert["all_pass"] = False
    cert["violation"] = bool(note.get("arithmetic", {})
                             .get("violation_a+b+c_greater_than_n", False))
    return cert


# --------------------------------------------------------------------------- #
# independent brute-force reference (literal subset enumeration, no bitsets)
# --------------------------------------------------------------------------- #
def brute_all_chains(ctx, tri_cap=18):
    """Enumerate EVERY legal chain by literal subset enumeration and return
    (max_margin, n_chains, max_a_plus_b, any_c_positive, skipped_reason).
    Independent code path from Exact/milp_pack: pure Python subsets + lists."""
    nt = len(ctx.tris)
    if nt == 0:
        return 0, 0, 0, False, None
    if nt > tri_cap:
        return None, None, None, None, "too_many_triangles(%d>%d)" % (nt, tri_cap)
    tris = list(range(nt))
    edge_of = {i: [ctx.edges[e] for e in ctx.tedges[i]] for i in tris}

    def packings(cands):
        """all pairwise edge-disjoint subsets of `cands` (as sorted tuples)"""
        out = [()]
        for i in cands:
            ei = set(edge_of[i])
            news = []
            for p in out:
                ok = True
                for j in p:
                    if ei & set(edge_of[j]):
                        ok = False
                        break
                if ok:
                    news.append(p + (i,))
            out += news
        return out

    allP = packings(tris)
    n = max(len(p) for p in allP)
    Ps = [p for p in allP if len(p) == n]
    margins, nchains, ab_max, cpos = [], 0, 0, False
    for P in Ps:
        Oset = set(e for i in P for e in edge_of[i])
        typ = lambda i: sum(1 for e in edge_of[i] if e in Oset)
        cand1 = [i for i in tris if typ(i) == 1]
        Aall = packings(cand1) if cand1 else [()]
        a = max(len(p) for p in Aall)
        As = [p for p in Aall if len(p) == a]
        for A in As:
            EA = set(e for i in A for e in edge_of[i])
            gprime = [t for t in (set(ctx.edges) - EA)]
            egi = set(gprime)
            cand2 = [i for i in tris if set(edge_of[i]) <= egi]
            PPall = packings(cand2) if cand2 else [()]
            def lm(p):
                return (sum(1 for i in p if typ(i) == 2), len(p))
            bestlm = max(lm(p) for p in PPall)
            PPs = [p for p in PPall if lm(p) == bestlm]
            b, m = bestlm
            for Pp in PPs:
                Bset = set(e for i in Pp for e in edge_of[i] if e in Oset)
                Hedges = set(gprime) - Bset
                cand3 = [i for i in tris if set(edge_of[i]) <= Hedges]
                Qall = packings(cand3) if cand3 else [()]
                c = max(len(p) for p in Qall)
                margins.append(a + b + c - n)
                nchains += 1
                ab_max = max(ab_max, a + b)
                cpos = cpos or c > 0
    return (max(margins) if margins else None), nchains, ab_max, cpos, None


# --------------------------------------------------------------------------- #
# exhaustive ALL-legal-choices check for one graph (used when a violation is hit)
# --------------------------------------------------------------------------- #
def exhaustive_chain_check(ctx, cfg, allcap, deadline, report_first=None):
    """Expand EVERY legal optimum at every stage (capped), return
    {status, chains, max_margin, min_margin, n_violating_chains, violating_chains,
     truncated_stages}.  status='ok' only if no stage cap was hit."""
    out = {"status": "ok", "chains": 0, "max_margin": None, "n_violating": 0,
           "violating_chains": [], "truncated_stages": [], "candidates": {}}
    if not ctx.tris:
        out["status"] = "no_triangles"
        return out

    def enum(masks, weights, stage):
        ex = Exact(masks, weights, deadline, {"nodes": 0, "next_check": 8192})
        ex.optimum()
        sols, trunc = ex.optima(allcap)
        if trunc:
            out["truncated_stages"].append(stage)
        return sols, ex.best

    def stage_c(Psel, Asel, Ppsel):
        Omask = ctx.mask_of(Psel)
        Bmask = ctx.mask_of_edges(e for i in Ppsel for e in ctx.tedges[i]
                                  if (ctx.tmask[i] & Omask) >> e & 1)
        present_h = (ctx.allmask & ~ctx.mask_of(Asel)) & ~Bmask
        Qc = ctx.present_tris(present_h)
        if not Qc:
            return 0
        return Exact([ctx.tmask[i] for i in Qc], [1] * len(Qc), deadline,
                     {"nodes": 0, "next_check": 8192}).optimum()

    try:
        P_sols, n = enum(ctx.tmask, [1] * len(ctx.tris), "P")
        out["candidates"]["n"] = n
        out["candidates"]["P_optima"] = len(P_sols)
        for Psel in P_sols:
            Omask = ctx.mask_of(Psel)
            A_cand = [i for i in range(len(ctx.tris)) if ctx.typ(i, Omask) == 1]
            if A_cand:
                A_sols, a = enum([ctx.tmask[i] for i in A_cand], [1] * len(A_cand), "A")
                A_sols = [tuple(A_cand[j] for j in s) for s in A_sols]
            else:
                A_sols, a = [()], 0
            out["candidates"]["A_optima"] = out["candidates"].get("A_optima", 0) + len(A_sols)
            for Asel in A_sols:
                present_g = ctx.allmask & ~ctx.mask_of(Asel)
                PP_cand = ctx.present_tris(present_g)
                if PP_cand:
                    W = len(PP_cand) + 1
                    is2 = [1 if ctx.typ(i, Omask) == 2 else 0 for i in PP_cand]
                    L_sols, lex = enum([ctx.tmask[i] for i in PP_cand],
                                       [W * v + 1 for v in is2], "Pprime")
                    PP_sets = [(tuple(PP_cand[j] for j in s), sum(is2[j] for j in s),
                                len(s)) for s in L_sols]
                else:
                    PP_sets = [((), 0, 0)]
                out["candidates"]["Pprime_optima"] = \
                    out["candidates"].get("Pprime_optima", 0) + len(PP_sets)
                for (Ppsel, bb, mm) in PP_sets:
                    c = stage_c(Psel, Asel, Ppsel)
                    margin = a + bb + c - n
                    out["chains"] += 1
                    if out["max_margin"] is None or margin > out["max_margin"]:
                        out["max_margin"] = margin
                    if margin > 0:
                        out["n_violating"] += 1
                        if len(out["violating_chains"]) < 6:
                            out["violating_chains"].append(
                                {"name": report_first, "nv": ctx.nv,
                                 "edges": [list(e) for e in ctx.edges],
                                 "n": n, "a": a, "b": bb, "m": mm, "c": c,
                                 "margin": margin,
                                 "literal": chain_literal(ctx, Psel, Asel, Ppsel,
                                                          (), Omask)})
        if out["truncated_stages"]:
            out["status"] = "stage_cap_hit"
    except Deadline:
        out["status"] = "deadline"
    return out


# --------------------------------------------------------------------------- #
# graph sources
# --------------------------------------------------------------------------- #
def source_graphs(max_graphs, only_complete, log):
    out = []
    for k in (3, 4, 5, 6, 7):
        g = nx.complete_graph(k)
        out.append(("K%d" % k, k, sorted(g.edges()), None))
    if only_complete or max_graphs <= 0:
        return out
    t0 = time.monotonic()
    atlas = nx.graph_atlas_g()
    cand = []
    for g in atlas:
        nv = g.number_of_nodes()
        ne = g.number_of_edges()
        if nv < 3 or ne == 0 or ne == nv * (nv - 1) // 2:
            continue
        es = sorted(g.edges())
        ctx = Ctx(nv, es)
        if not ctx.tris:
            continue
        dens = 2.0 * ne / (nv * (nv - 1))
        cand.append((-dens, -nv, ne, str(getattr(g, "name", "?")), nv, es, len(ctx.tris)))
    cand.sort(key=lambda r: (r[0], r[1], r[2], r[3]))
    take = cand[:max_graphs]
    for (nd, _nnv, ne, gname, nv, es, ntri) in take:
        out.append(("atlas:%s:nv=%d:ne=%d:dens=%.4f:tri=%d" % (gname, nv, ne, -nd, ntri),
                    nv, es, None))
    log("atlas load+screen %.2fs: %d non-complete triangle-bearing entries, taking %d "
        "densest" % (time.monotonic() - t0, len(cand), len(take)))
    return out


# --------------------------------------------------------------------------- #
# modes
# --------------------------------------------------------------------------- #
def compactify(out, args, one_cert):
    """Small public certificate: counters + per-graph attempt list + ONE chain
    with its five stage optima, instead of the full raw dump."""
    v = out["verdict"]
    chain = None
    if out["certified_violations"]:
        chain = out["certified_violations"][0]["chain"]
    elif out["dual_certified_chains"]:
        chain = out["dual_certified_chains"][0]["chain"]
    elif v.get("best_observed_chain"):
        chain = v["best_observed_chain"]
    return {
        "meta": dict(out["meta"], mode="compact certificate (counters + one chain)",
                     reproduction={
                         "search": "python research/round11/B2/wang_chain_search.py "
                                   "search --max-graphs %d --budget %g --all-ties "
                                   "--cap %d --max-chains %d --seed %d --compact "
                                   "--out research/round11/B2/certificate.json"
                                   % (args.max_graphs, args.budget, args.cap,
                                      args.max_chains, args.seed),
                         "reverify_read_only": "python research/round11/B2/"
                                               "wang_chain_search.py reverify --file "
                                               "research/round11/B2/certificate.json",
                         "selftest_vs_literal_bruteforce":
                             "python research/round11/B2/wang_chain_search.py selftest "
                             "--max-graphs 200 --budget 90 --tri-cap 22",
                         "dcheck_recompute_under_D_protocol":
                             "python research/round11/B2/wang_chain_search.py dcheck "
                             "--file research/round11/B2/certificate.json --budget 90 "
                             "(add --patch <same file> to store the block)"}),
        "verdict": {
            "violation_found_and_certified": v["violation_found_and_certified"],
            "n_certified_violations": v["n_certified_violations"],
            "max_margin_observed": v["max_margin_observed"],
            "graphs_queued": v["graphs_queued"], "graphs_attempted": v["graphs_attempted"],
            "chains_examined": v["chains_examined"],
            "chains_with_c_positive": v["chains_with_c_positive"],
            "chains_where_H_has_triangles": v["chains_where_H_has_triangles"],
            "triangle_types_seen_in_H": v["triangle_types_seen_in_H"],
            "stage_deadline_timeouts": v["stage_deadline_timeouts"],
            "margin_hist_by_chain": v["margin_hist_by_chain"],
            "tight_margin0_chains_count": len(v["tight_margin0_chains_sample"]),
            "anomaly_count": len(v["anomalies"]),
            "all_legal_choices_scan_of_witness_graph":
                v["all_legal_choices_scan_of_witness_graph"],
            "scope": v["scope"],
            "definition_history_note":
                "earlier private probes computed H as G'-E(P') (removing ALL edges of "
                "P'); the stated object is H=G'-B(P') (only the OLD edges of P'), which "
                "is what this certificate uses; the old probes' c=0 pattern was an "
                "artefact of that bug",
        },
        "one_certified_chain": {"chain": chain,
                                "checks": None if one_cert is None else one_cert["checks"],
                                "all_pass": None if one_cert is None else one_cert["all_pass"],
                                "violation": None if one_cert is None else one_cert.get("violation"),
                                "five_stage_values": None if chain is None else
                                {"n": chain["n"], "a": chain["a"], "b": chain["b"],
                                 "m": chain["m"], "c": chain["c"],
                                 "a_plus_b_plus_c_minus_n": chain["margin"]}},
        "graphs_attempted": [{k: g.get(k) for k in
                              ("id", "nv", "ne", "triangles", "n", "chains", "margin_max",
                               "a_max", "b_max", "c_max", "ab_max", "skipped", "timeouts",
                               "P_optima_truncated", "A_optima_truncated",
                               "Pprime_optima_truncated", "chain_cap_reached")}
                             for g in out["graphs_attempted"]],
    }


# --------------------------------------------------------------------------- #
# D-protocol recheck: recompute the SAVED witness under D/protocol.txt wording
# (S = surviving TYPE-2 triangles only; plus D's scope ranking). Deterministic,
# operates on the one printed instance -- not a new search.
# --------------------------------------------------------------------------- #
def d_scope_rank(nv, ne, edges):
    """Position of the printed graph in D's ordered list:
    connected, triangle-bearing atlas entries, order <=7, >=12 edges, sorted by
    decreasing edge count then existing atlas order (complete graphs excluded,
    K5/K6/K7 being D's fixed starting controls)."""
    atlas = nx.graph_atlas_g()
    lst = []
    for g in atlas:
        v = g.number_of_nodes()
        e = g.number_of_edges()
        if v < 3 or v > 7 or e < 12 or e == v * (v - 1) // 2:
            continue
        if not nx.is_connected(g):
            continue
        if not any(t > 0 for t in nx.triangles(g).values()):
            continue
        lst.append((-e, str(getattr(g, "name", "?")), v, e, sorted(g.edges())))
    lst.sort(key=lambda r: (r[0], int(r[1][1:] if r[1][1:].isdigit() else 10 ** 9)))
    tgt = (nv, ne, tuple(sorted(tuple(x) for x in edges)))
    rank = None
    for i, (me, gname, v, e, es) in enumerate(lst):
        if (v, e, tuple(sorted(es))) == tgt:
            rank = i + 1
            break
    return {"d_list_size": len(lst), "witness_rank_in_d_order": rank,
            "within_d_32": (rank is not None and rank <= 32),
            "d_first32": [{"atlas": lst[i][1], "nv": lst[i][2], "ne": lst[i][3]}
                          for i in range(min(32, len(lst)))]}


def d_recheck(ctx, chain, deadline):
    out = {"protocol": "research/round11/D/protocol.txt", "all_pass": True}
    lit = chain["literal"]
    idx = lambda t: ctx.tri_index(t)
    Psel = [idx(t) for t in lit["P"]]
    Asel = [idx(t) for t in lit["A"]]
    Ppsel = [idx(t) for t in lit["Pprime"]]
    Qsel = [idx(t) for t in lit["Q"]]
    Omask = ctx.mask_of(Psel)
    n = len(Psel)
    stats = {"nodes": 0, "next_check": 4096}

    def nu(cands):
        if not cands:
            return 0, milp_pack([], [], deadline)
        v = Exact([ctx.tmask[i] for i in cands], [1] * len(cands),
                  deadline, stats).optimum()
        return v, milp_pack([ctx.tedges[i] for i in cands], [1] * len(cands), deadline)

    # step 1: n = nu(G)
    n_dfs, n_milp = nu(range(len(ctx.tris)))
    out["step1_nu_G"] = {"claimed": chain["n"], "bitset": n_dfs,
                         "milp_status": n_milp.get("status"),
                         "milp": n_milp.get("value"),
                         "no_type0_triangle": all(ctx.typ(i, Omask) >= 1
                                                  for i in range(len(ctx.tris))),
                         "ok": n_dfs == chain["n"] == n_milp.get("value") == n}
    # step 2: a = nu(all type-1 triangles)
    A_c = [i for i in range(len(ctx.tris)) if ctx.typ(i, Omask) == 1]
    a_dfs, a_milp = nu(A_c)
    out["step2_nu_type1"] = {"claimed": chain["a"], "bitset": a_dfs,
                             "milp_status": a_milp.get("status"),
                             "milp": a_milp.get("value"),
                             "n_type1_candidates": len(A_c),
                             "ok": a_dfs == chain["a"] == a_milp.get("value")}
    # step 3: G' = G - E(A); every triangle of G' has type 2 or 3
    present_g = ctx.allmask & ~ctx.mask_of(Asel)
    gprime = ctx.present_tris(present_g)
    types_gprime = sorted({ctx.typ(i, Omask) for i in gprime})
    out["step3_Gprime_types"] = {"claimed_no_type1_survives": True,
                                "observed_types": types_gprime,
                                "ok": all(t in (2, 3) for t in types_gprime)}
    # step 4: lex max (b, m); D's scalar (n+1)*b+m and my (|cand|+1)*b+m
    is2 = [1 if ctx.typ(i, Omask) == 2 else 0 for i in gprime]
    b_dfs, b_milp = nu([i for i, w in zip(gprime, is2) if w == 1])
    Wd = n + 1
    lex_d_dfs = Exact([ctx.tmask[i] for i in gprime], [Wd * v + 1 for v in is2],
                      deadline, stats).optimum()
    eq = (is2, chain["b"])
    m_milp = milp_pack([ctx.tedges[i] for i in gprime], [1] * len(gprime), deadline,
                       eq=eq) if gprime else milp_pack([], [], deadline)
    b_pr = sum(1 for i in Ppsel if ctx.typ(i, Omask) == 2)
    out["step4_lex_b_then_m"] = {
        "claimed_b": chain["b"], "bitset_b": b_dfs, "milp_status": b_milp.get("status"),
        "milp_b": b_milp.get("value"), "witness_b": b_pr,
        "claimed_m": chain["m"], "d_scalar_W": Wd, "d_scalar_value": lex_d_dfs,
        "d_scalar_expected": Wd * chain["b"] + chain["m"],
        "milp_m_given_b": m_milp.get("value"), "witness_m": len(Ppsel),
        "m_le_n": len(Ppsel) <= n,
        "ok": (b_dfs == chain["b"] == b_pr == b_milp.get("value")
               and lex_d_dfs == Wd * chain["b"] + chain["m"]
               and m_milp.get("value") == chain["m"] == len(Ppsel) and len(Ppsel) <= n)}
    # step 5: OldPrime = O & E(P'); S = surviving TYPE-2 triangles; c = nu(S)
    OldPrime = ctx.mask_of(Ppsel) & Omask
    present_s = present_g & ~OldPrime
    S = [i for i in gprime if ctx.typ(i, Omask) == 2
         and ctx.tmask[i] & ~present_s == 0]
    c_dfs, c_milp = nu(S)
    # my earlier (broader) family: all triangles of H = G' - OldPrime
    H_c = ctx.present_tris(present_s)
    c_broad, _ = nu(H_c)
    out["step5_S_and_c"] = {
        "OldPrime_edges": ctx.pairs(bits_of(OldPrime, len(ctx.edges))),
        "n_S_type2_survivors": len(S), "S_triangles": [list(ctx.tris[i]) for i in S],
        "claimed_c": chain["c"], "bitset_nu_S": c_dfs, "milp_status": c_milp.get("status"),
        "milp_nu_S": c_milp.get("value"),
        "printed_Q_inside_S": all(i in S for i in Qsel),
        "printed_Q_size": len(Qsel),
        "broader_family_all_H_triangles": len(H_c), "nu_all_H_triangles": c_broad,
        "ok": (c_dfs == chain["c"] == c_milp.get("value") == len(Qsel)
               and all(i in S for i in Qsel))}
    # step 6: the test + D's consistency checks
    out["step6_test"] = {
        "a+b+c_under_D": chain["a"] + chain["b"] + c_dfs, "n": chain["n"],
        "violation": chain["a"] + chain["b"] + c_dfs > chain["n"],
        "a_plus_m_le_n": chain["a"] + chain["m"] <= chain["n"],
        "a_plus_m": chain["a"] + chain["m"],
        "a_plus_b_le_n": chain["a"] + chain["b"] <= chain["n"],
        "a_plus_b": chain["a"] + chain["b"]}
    # optional diagnostics h and d (after the positive witness)
    h = 0
    for i in Qsel:
        ne = [e for e in ctx.tedges[i] if not (ctx.tmask[i] & Omask) >> e & 1]
        cnt = sum(1 for j in S if set(ne) & set(ctx.tedges[j]))
        h += 1 if cnt == 1 else 0
    Qold = ctx.mask_of(Qsel) & Omask
    S2 = [i for i in S if ctx.tmask[i] & Qold == 0]
    d_val, d_milp = nu(S2)
    out["optional_diagnostics"] = {
        "h_Q_triangles_with_private_new_edge_in_S": h,
        "d_nu_S_after_deleting_Q_old_edges": d_val,
        "d_milp_status": d_milp.get("status"), "d_milp": d_milp.get("value"),
        "n_S2": len(S2),
        "note": "not required to refute a+b+c<=n"}
    for k in ("step1_nu_G", "step2_nu_type1", "step3_Gprime_types",
              "step4_lex_b_then_m", "step5_S_and_c"):
        if not out[k].get("ok"):
            out["all_pass"] = False
    out["all_pass"] = out["all_pass"] and out["step6_test"]["violation"]
    return out


def run_dcheck(args, log):
    with open(args.file, "r", encoding="utf-8") as fh:
        cert = json.load(fh)
    ch = (cert["one_certified_chain"] or {}).get("chain") or \
        cert["certified_violations"][0]["chain"]
    ctx = Ctx(ch["nv"], ch["edges"])
    deadline = time.monotonic() + args.budget
    res = d_recheck(ctx, ch, deadline)
    res["scope_reconciliation"] = d_scope_rank(ch["nv"], len(ctx.edges), ch["edges"])
    log(json.dumps(res, indent=1))
    if args.patch:
        cert["d_protocol_recheck"] = res
        with open(args.patch, "w", encoding="utf-8") as fh:
            json.dump(cert, fh, indent=1)
        log("patched %s with d_protocol_recheck (chain checks unchanged)" % args.patch)
    else:
        log("(dcheck wrote no file)")
    log("dcheck all_pass=%s violation_under_D_definitions=%s"
        % (res["all_pass"], res["step6_test"]["violation"]))
    return 0 if res["all_pass"] else 1


def run_search(args, log):
    t0 = time.monotonic()
    graphs = source_graphs(args.max_graphs, args.only_complete, log)
    deadline = t0 + args.budget
    cfg = {"cap": args.cap, "kP": args.kP, "kA": args.kA, "kPP": args.kPP,
           "max_chains": args.max_chains}
    if args.all_ties:
        cfg.update(kP=10 ** 9, kA=10 ** 9, kPP=10 ** 9)
    stats = {"nodes": 0, "next_check": 0}
    rng = random.Random(args.seed)
    cfg["pool"] = {"res": [], "k": args.pool, "n": 0,
                   "rng": random.Random(args.seed + 1)}
    log("graphs queued: %d" % len(graphs))
    attempted, violations, anomalies = [], [], []
    best_global, nchains, tmo, cert_time = None, 0, 0, 0.0
    cpos, hist, tight = 0, {}, []
    htri, htypes = 0, {}
    stop = False
    for (name, nv, es, _x) in graphs:
        if time.monotonic() > deadline:
            log("BUDGET reached before %s -- bounded search stops here" % name)
            attempted.append({"id": name, "skipped": "budget_not_attempted"})
            break
        ctx = Ctx(nv, es)
        try:
            r = analyse_graph(name, ctx, rng, cfg, deadline, stats)
        except Deadline:
            log("DEADLINE inside %s" % name)
            attempted.append({"id": name, "skipped": "deadline"})
            break
        tmo += r["timeouts"]
        nchains += r["chains"]
        attempted.append({k: r.get(k) for k in
                          ("id", "nv", "ne", "triangles", "n", "chains", "margin_max",
                           "skipped", "timeouts", "P_optima_enumerated",
                           "P_optima_truncated", "A_optima_truncated",
                           "Pprime_optima_truncated", "a_max", "b_max", "c_max",
                           "ab_max", "chains_c_pos", "chain_cap_reached")})
        cpos += r.get("chains_c_pos", 0)
        htri += r.get("h_tri_pos", 0)
        for kk, vv in (r.get("h_type_hist") or {}).items():
            htypes[kk] = htypes.get(kk, 0) + vv
        for kk, vv in r.get("margin_hist", {}).items():
            hist[str(kk)] = hist.get(str(kk), 0) + vv
        log("%-52s n=%-3s chains=%-3d margin_max=%-4s a_max=%-3s b_max=%-3s c_max=%-3s%s" %
            (name, r["n"], r["chains"], r["margin_max"], r.get("a_max"),
             r.get("b_max"), r.get("c_max"), " " + (r["skipped"] or "")))
        if r["best_chain"] and (best_global is None or
                                r["best_chain"]["margin"] > best_global["margin"]):
            best_global = r["best_chain"]
        if r["margin_max"] == 0 and r["best_chain"] and len(tight) < 20:
            tight.append(r["best_chain"])
        for v in r["violations"]:
            if deadline - time.monotonic() < 3.0:
                anomalies.append({"chain": v, "note": "no_time_to_certify"})
                continue
            tc = time.monotonic()
            cc = certify_chain(Ctx(v["nv"], v["edges"]), v, deadline)
            cc["wall_s"] = round(time.monotonic() - tc, 3)
            cert_time += cc["wall_s"]
            cc["chain"] = v
            if cc["all_pass"] and cc["certified"] and cc["violation"]:
                violations.append(cc)
                log("!!! CERTIFIED VIOLATION %s a=%d b=%d c=%d > n=%d (margin %d)"
                    % (name, v["a"], v["b"], v["c"], v["n"], v["margin"]))
                if not args.keep_going:
                    stop = True
                    break
            else:
                anomalies.append({"chain": v, "cert": cc})
                log("!!! violation candidate %s NOT certified (see anomalies)" % name)
        if r["violations"]:
            for v in r["violations"]:
                log("    chain %s: n=%d a=%d b=%d m=%d c=%d margin=%d"
                    % (name, v["n"], v["a"], v["b"], v["m"], v["c"], v["margin"]))
        if stop:
            break
    # ---- follow-up on the witness graph: does EVERY legal choice violate? ----
    all_choice_scan = None
    if violations and deadline - time.monotonic() > 3.0:
        w = violations[0]["chain"]
        tc = time.monotonic()
        all_choice_scan = exhaustive_chain_check(Ctx(w["nv"], w["edges"]), cfg,
                                                 args.cap, deadline, w["name"])
        all_choice_scan["wall_s"] = round(time.monotonic() - tc, 3)
        log("ALL-legal-choices re-scan of %s: status=%s chains=%d max_margin=%s "
            "violating=%d truncated_stages=%s"
            % (w["name"], all_choice_scan["status"], all_choice_scan["chains"],
               all_choice_scan["max_margin"], all_choice_scan["n_violating"],
               all_choice_scan["truncated_stages"]))
    # ---- dual-engine certification of representative chains ----
    reps, seen = [], set()

    def add_rep(c):
        if not c:
            return
        k = (c["name"], json.dumps(c["literal"], sort_keys=True))
        if k in seen:
            return
        seen.add(k)
        reps.append(c)
    add_rep(best_global)
    for t in tight:
        add_rep(t)
    for t in cfg["pool"]["res"]:
        add_rep(t)
    dual, dual_fail, dual_unverified = [], 0, 0
    for c in reps:
        if deadline - time.monotonic() < 1.0:
            dual_unverified += 1
            continue
        tc = time.monotonic()
        cc = certify_chain(Ctx(c["nv"], c["edges"]), c, deadline)
        cc["wall_s"] = round(time.monotonic() - tc, 4)
        cert_time += cc["wall_s"]
        cc["chain"] = c
        if not cc["all_pass"]:
            dual_fail += 1
        dual.append(cc)
    log("dual-engine certification: %d representative chains, %d failed, %d not "
        "reached" % (len(dual), dual_fail, dual_unverified))
    out = {
        "meta": {
            "role": "round11/B2", "kind": "bounded numerical search -- no proof claim",
            "object": "Wang chain P->A->P'->Q, violation test a+b+c > n",
            "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "python": sys.version.split()[0], "networkx": nx.__version__,
            "seed": args.seed, "all_ties": bool(args.all_ties),
            "config": {k: v for k, v in cfg.items() if k != "pool"},
            "budget_s": args.budget,
            "wall_s": round(time.monotonic() - t0, 2),
            "engines": {"A": "exact integer bitset branch&bound, memoised on "
                             "(index, used-edge bitmask), exhaustive iff no deadline",
                        "B": "scipy.optimize.milp HiGHS; accepted only at status==0 + "
                             "success + integral(1e-6) + literal witness re-check"},
            "tie_policy": "optima enumerated up to cap=%d then a seeded subset "
                          "(kP=%d,kA=%d,kPP=%d) expanded: truncated=True means legal "
                          "choices were NOT expanded" %
                          (args.cap, args.kP, args.kA, args.kPP),
        },
        "verdict": {
            "violation_found_and_certified": bool(violations),
            "n_certified_violations": len(violations),
            "max_margin_observed": None if best_global is None else best_global["margin"],
            "best_observed_chain": best_global,
            "graphs_queued": len(graphs), "graphs_attempted": len(attempted),
            "chains_examined": nchains, "stage_deadline_timeouts": tmo,
            "chains_with_c_positive": cpos, "margin_hist_by_chain": hist,
            "chains_where_H_has_triangles": htri,
            "triangle_types_seen_in_H": htypes,
            "tight_margin0_chains_sample": tight,
            "exact_solve_timeouts": tmo,
            "all_legal_choices_scan_of_witness_graph": all_choice_scan,
            "anomalies": anomalies,
            "scope": "bounded search over the printed graph list and printed tie "
                     "samples only; a clean run does NOT prove a+b+c<=n",
        },
        "certified_violations": violations,
        "dual_certification_summary": {
            "representative_chains": len(reps), "certified": len(dual),
            "failed_checks": dual_fail, "not_reached_in_budget": dual_unverified,
            "note": "every stage (P, A, lex P', Q) of each listed chain recomputed by "
                    "the exact bitset engine AND by scipy MILP (status 0 + integral + "
                    "literal re-check); all_agree flags in the checks must be True",
        },
        "dual_certified_chains": dual,
        "graphs_attempted": attempted,
    }
    one_cert = violations[0] if violations else (dual[0] if dual else None)
    to_write = compactify(out, args, one_cert) if args.compact else out
    if args.raw_out:
        with open(args.raw_out, "w", encoding="utf-8") as fh:
            json.dump(out, fh, indent=1)
        log("raw full dump -> %s (%.1f KB)" % (args.raw_out,
            os.path.getsize(args.raw_out) / 1024.0))
    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(to_write, fh, indent=1)
    log("wrote %s%s wall=%.1fs certification=%.2fs search_nodes=%d violations=%d"
        % (args.out, " (compact)" if args.compact else "", time.monotonic() - t0,
           cert_time, stats["nodes"], len(violations)))
    return 0


def run_selftest(args, log):
    """READ-ONLY cross-validation: engine chain semantics vs literal subset
    brute force over every legal choice, on every queued graph small enough."""
    graphs = source_graphs(args.max_graphs, False, log)
    cfg = {"cap": 10 ** 9, "kP": 10 ** 9, "kA": 10 ** 9, "kPP": 10 ** 9,
           "max_chains": 10 ** 9}
    deadline = time.monotonic() + args.budget
    rng = random.Random(args.seed)
    stats = {"nodes": 0, "next_check": 0}
    rows, fails, skipped = [], 0, 0
    for (name, nv, es, _x) in graphs:
        ctx = Ctx(nv, es)
        if not ctx.tris:
            continue
        bmm, bch, bab, bcp, sk = brute_all_chains(ctx, args.tri_cap)
        if sk:
            skipped += 1
            continue
        try:
            r = analyse_graph(name, ctx, rng, cfg, deadline, stats)
        except Deadline:
            log("selftest deadline at %s" % name)
            break
        emm, ech, ecp = r["margin_max"], r["chains"], (r.get("c_max") or 0) > 0
        ok = (emm == bmm) and (ech == bch) and (ecp == bool(bcp))
        fails += 0 if ok else 1
        rows.append(name)
        log("%-50s tri=%-3d margin eng=%-4s brute=%-4s chains=%-6s/%-6s c>0 %s/%s %s"
            % (name, len(ctx.tris), emm, bmm, ech, bch, ecp, bool(bcp),
               "OK" if ok else "*** MISMATCH ***"))
    log("selftest: %d graphs cross-checked, %d skipped (tri>cap=%d), %d mismatches"
        % (len(rows), skipped, args.tri_cap, fails))
    log("(selftest wrote no file)")
    return 0 if fails == 0 else 1


def run_reverify(args, log):
    with open(args.file, "r", encoding="utf-8") as fh:
        cert = json.load(fh)
    if "one_certified_chain" in cert:            # compact public format
        occ = cert["one_certified_chain"]
        pool = [{"chain": occ["chain"], "checks": occ["checks"]}]
    else:
        pool = cert["certified_violations"] or \
            ([{"chain": cert["verdict"]["best_observed_chain"]}]
             if cert["verdict"].get("best_observed_chain") else [])
    if not pool:
        log("certificate prints no chain to reverify")
        return 2
    c = pool[min(args.chain, len(pool) - 1)]
    ch = c["chain"]
    ctx = Ctx(ch["nv"], ch["edges"])
    deadline = time.monotonic() + args.budget
    fresh = certify_chain(ctx, ch, deadline)
    ok = fresh["all_pass"]
    match = ("checks" in c) and (c["checks"] == fresh["checks"])
    log(json.dumps({"id": ch["name"], "nv": ch["nv"], "ne": len(ch["edges"]),
                    "n": ch["n"], "a": ch["a"], "b": ch["b"], "m": ch["m"],
                    "c": ch["c"], "margin": ch["margin"]}, indent=1))
    for k in sorted(fresh["checks"]):
        v = fresh["checks"][k]
        flag = v.get("all_agree", v.get("all_three_agree", "-"))
        log("  %-40s agree=%-5s %s" % (k, flag,
            json.dumps({kk: vv for kk, vv in v.items()
                        if kk in ("dfs", "dfs_b_max", "dfs_m_given_bmax", "milp_value",
                                  "milp_value_m_given_b", "claimed", "claimed_b",
                                  "claimed_m", "milp_status", "milp_certified",
                                  "printed_witness_size", "milp_error",
                                  "margin_a+b+c-n", "violation_a+b+c_greater_than_n",
                                  "fatal")}, sort_keys=True)))
    if "fatal" in fresh:
        log("  FATAL %s" % fresh["fatal"])
    log("reverify: all_pass=%s  violation=%s  matches_stored_certificate=%s"
        % (ok, fresh.get("violation"), match))
    log("(reverify wrote no file)")
    if not ok:
        return 1
    return 0 if match else 2


def main():
    ap = argparse.ArgumentParser(description="round11/B2 Wang-chain a+b+c>n search")
    ap.add_argument("mode", choices=["search", "reverify", "selftest", "dcheck"])
    ap.add_argument("--budget", type=float, default=110.0)
    ap.add_argument("--max-graphs", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1102)
    ap.add_argument("--cap", type=int, default=60)
    ap.add_argument("--kP", type=int, default=4)
    ap.add_argument("--kA", type=int, default=3)
    ap.add_argument("--kPP", type=int, default=3)
    ap.add_argument("--max-chains", type=int, default=4000)
    ap.add_argument("--pool", type=int, default=40)
    ap.add_argument("--all-ties", action="store_true",
                    help="expand EVERY enumerated optimum at every stage (kP=kA=kPP=all)")
    ap.add_argument("--tri-cap", type=int, default=22, help="selftest only")
    ap.add_argument("--only-complete", action="store_true")
    ap.add_argument("--keep-going", action="store_true")
    ap.add_argument("--out", default="certificate.json")
    ap.add_argument("--compact", action="store_true",
                    help="write counters + ONE certified chain instead of the raw dump")
    ap.add_argument("--raw-out", default=None, help="also write the full dump here")
    ap.add_argument("--file", default="certificate.json")
    ap.add_argument("--chain", type=int, default=0)
    ap.add_argument("--patch", default=None,
                    help="dcheck only: write the recheck block into this certificate")
    args = ap.parse_args()
    t_start = time.monotonic()

    def log(*a):
        print("[%7.2fs]" % (time.monotonic() - t_start), *a, flush=True)

    if args.mode == "search":
        sys.exit(run_search(args, log))
    if args.mode == "selftest":
        sys.exit(run_selftest(args, log))
    if args.mode == "dcheck":
        sys.exit(run_dcheck(args, log))
    sys.exit(run_reverify(args, log))


if __name__ == "__main__":
    main()
