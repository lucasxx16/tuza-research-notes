#!/usr/bin/env python3
"""Round11 / Role B -- STANDALONE literal verifier for red/blue triangle instances.

Genuinely standalone: it imports NOTHING from research/round10 and NOTHING from
targeted_search.py. It re-parses the colourstring, re-enumerates every triangle,
re-checks every triangle constraint, and re-derives p, p_private, tau, r, s with its
own solvers. Its only external dependency is scipy.optimize.milp (optional).

Setting checked (never assumed):
  H finite simple graph on vertices 0..n-1, each present edge coloured R or B,
  EVERY triangle of H contains EXACTLY ONE red edge.
    p          = max # pairwise EDGE-disjoint triangles of H
    p_private  = max # pairwise edge-disjoint triangles whose red edge lies in exactly
                 ONE triangle of H (globally private). Premise p_private == p > 0 is the
                 "there exists a maximum packing Q whose red edges are globally private"
                 premise; Q is returned and re-checked literally.
    tau        = min # graph EDGES meeting every triangle (Tuza EDGE transversal)
    r          = # red edges lying in >= 1 triangle          (premise r <= 3p)
    s          = # participating red edges lying in >= 2 triangles ("multipage" red)

Two independent exact methods (never a heuristic value):
  * exhaustive subset enumeration over triangles / over candidate edges, exact by
    construction, with an explicit subset cap (2**k <= BRUTE_CAP);
  * scipy.optimize.milp (HiGHS) ILP, ACCEPTED ONLY when status == 0 (Optimized), the
    solution is integral, and the decoded set is re-checked literally
    (edge-disjointness for the packing, hitting for the cover).
A bound alone -- LP relaxation, incumbent without optimality proof, timeout, or the
value returned with any other status -- is NEVER read as an exact optimum. When both
methods are unavailable for a quantity, the instance is reported NOT CERTIFIED.

Read-only CLI: --verify never writes to disk.
  python verify_witness.py --n 6 --colorstring BRBB...            (single instance)
  python verify_witness.py --file instances.json --all            (saved inputs)
  python verify_witness.py --file instances.json --id <name>
Exit code: 0 all premises hold, quantities certified, claims agree (or no claims);
           1 a premise fails, or a saved claim disagrees with this verifier;
           2 a quantity could not be certified exactly.
No theorem or proof is claimed anywhere in this file.
"""
import argparse, itertools, json, sys, time
from pathlib import Path

BRUTE_CAP = 1 << 20          # max subsets enumerated per brute-force problem
INTEG_TOL = 1e-6
TIME_LIMIT = [None]          # seconds per scipy.milp solve; set by the caller (search).
                             # None = solver default (used for one-off CLI verification).
ABS_DEADLINE = [None]        # optional shared wall-clock deadline for the caller.


def _opts():
    limit = TIME_LIMIT[0]
    if ABS_DEADLINE[0] is not None:
        remaining = max(0.01, ABS_DEADLINE[0] - time.time())
        limit = remaining if limit is None else min(limit, remaining)
    return {"time_limit": limit} if limit is not None else {}


def pairs_of(n):
    return list(itertools.combinations(range(n), 2))


def decode(n, cs):
    pl = pairs_of(n)
    if len(cs) != len(pl):
        raise ValueError(f"colorstring for n={n} must have {len(pl)} chars, got {len(cs)}")
    if any(ch not in "0BR" for ch in cs):
        raise ValueError("colorstring characters must be 0 (absent), B (blue), R (red)")
    ed = {e for e, ch in zip(pl, cs) if ch in "BR"}
    rd = {e for e, ch in zip(pl, cs) if ch == "R"}
    return pl, ed, rd


def encode(n, pl, ed, rd):
    return "".join("R" if e in rd else ("B" if e in ed else "0") for e in pairs_of(n))


def triangles_of(n, pl, ed, rd):
    """every triangle, re-enumerated from the pair list. Returns
    (tri_verts, tri_edge_masks[over pair indices], tri_red[red pair index or None],
     violations)"""
    idx = {e: i for i, e in enumerate(pl)}
    verts, masks, reds, viol = [], [], [], []
    for (a, b, c) in itertools.combinations(range(n), 3):
        es = [(a, b), (a, c), (b, c)]
        if all(e in ed for e in es):
            m = 0
            for e in es:
                m |= 1 << idx[e]
            rr = [b2 for b2 in _bits(m) if pl[b2] in rd]
            verts.append((a, b, c))
            masks.append(m)
            if len(rr) != 1:
                reds.append(None)
                viol.append({"triangle": [a, b, c],
                             "red_edges": [list(pl[x]) for x in rr],
                             "n_red": len(rr)})
            else:
                reds.append(rr[0])
    return verts, masks, reds, viol


def _bits(m):
    out = []
    while m:
        lb = m & -m
        out.append(lb.bit_length() - 1)
        m ^= lb
    return out


def connected(n, ed):
    adj = {v: set() for v in range(n)}
    for a, b in ed:
        adj[a].add(b)
        adj[b].add(a)
    if n == 0:
        return False
    seen, fr = {0}, [0]
    while fr:
        u = fr.pop()
        for w in adj[u] - seen:
            seen.add(w)
            fr.append(w)
    return len(seen) == n


# ---------------------------------------------------------------- brute force
def brute_packing(masks, cap=BRUTE_CAP):
    """exact max set of pairwise edge-disjoint triangles by subset enumeration."""
    t = len(masks)
    if t == 0:
        return 0, [], "brute"
    if (1 << t) > cap:
        return None, None, "skipped_cap"
    disj = bytearray(b"\x01") * (1 << t)
    union = [0] * (1 << t)
    best, bestm = 0, 0
    for m in range(1, 1 << t):
        lb = m & -m
        i = lb.bit_length() - 1
        prev = m ^ lb
        if disj[prev] and not (union[prev] & masks[i]):
            disj[m] = 1
            union[m] = union[prev] | masks[i]
            k = bin(m).count("1")
            if k > best:
                best, bestm = k, m
        else:
            disj[m] = 0
            union[m] = union[prev] | masks[i]
    return best, [i for i in range(t) if bestm >> i & 1], "brute"


def brute_cover(masks, cand, cap=BRUTE_CAP):
    """exact min edge set hitting every triangle, by subset enumeration over cand."""
    t = len(masks)
    if t == 0:
        return 0, [], "brute"
    if (1 << len(cand)) > cap:
        return None, None, "skipped_cap"
    full = (1 << t) - 1
    hits = []
    for e in cand:
        h = 0
        for j, m in enumerate(masks):
            if m >> e & 1:
                h |= 1 << j
        hits.append(h)
    size = 1 << len(cand)
    cov = [0] * size
    pop = [0] * size
    best, bestm = None, 0
    for m in range(1, size):
        lb = m & -m
        i = lb.bit_length() - 1
        prev = m ^ lb
        cov[m] = cov[prev] | hits[i]
        pop[m] = pop[prev] + 1
        if cov[m] == full and (best is None or pop[m] < best):
            best, bestm = pop[m], m
    if best is None:
        return t + 1, None, "brute"          # no cover within candidates (cannot happen)
    return best, [cand[i] for i in range(len(cand)) if bestm >> i & 1], "brute"


# ---------------------------------------------------------------- ILP (scipy/HiGHS)
def _milp():
    try:
        from scipy.optimize import milp, LinearConstraint, Bounds      # noqa
        import numpy as np                                             # noqa
        import scipy.sparse as sp                                      # noqa
    except Exception as e:                                             # pragma: no cover
        return None, f"scipy_unavailable:{type(e).__name__}:{e}"
    return (milp, LinearConstraint, Bounds, np, sp), None


def ilp_packing(masks, nedges):
    """max sum x_i s.t. for each edge, sum_{i: e in T_i} x_i <= 1, x binary."""
    api, err = _milp()
    if api is None:
        return None, None, err
    milp, LinearConstraint, Bounds, np, sp = api
    t = len(masks)
    if t == 0:
        return 0, [], "ilp_empty"
    rows, cols, ridx = [], [], 0
    for e in range(nedges):
        for i, m in enumerate(masks):
            if m >> e & 1:
                rows.append(ridx)
                cols.append(i)
        ridx += 1
    A = sp.csr_matrix((np.ones(len(rows), dtype=float), (rows, cols)), shape=(ridx, t))
    res = milp(c=-np.ones(t), constraints=LinearConstraint(A, -np.inf, 1.0),
               integrality=np.ones(t), bounds=Bounds(0, 1), options=_opts())
    st = int(res.status)
    if st != 0 or res.x is None:
        return None, None, f"ilp_status_{st}:{getattr(res,'message','')}"
    x = [int(v) for v in res.x]
    if any(abs(a - b) > INTEG_TOL for a, b in zip(res.x, x)):
        return None, None, "ilp_nonintegral"
    pick = [i for i in range(t) if x[i]]
    return int(round(-res.fun)), pick, "ilp_optimal"


def ilp_cover(masks, cand):
    """min sum y_e s.t. for each triangle, sum_{e in T} y_e >= 1, y binary."""
    api, err = _milp()
    if api is None:
        return None, None, err
    milp, LinearConstraint, Bounds, np, sp = api
    t, m = len(masks), len(cand)
    if t == 0:
        return 0, [], "ilp_empty"
    rows, cols = [], []
    for j, mk in enumerate(masks):
        for k, e in enumerate(cand):
            if mk >> e & 1:
                rows.append(j)
                cols.append(k)
    A = sp.csr_matrix((np.ones(len(rows), dtype=float), (rows, cols)), shape=(t, m))
    res = milp(c=np.ones(m), constraints=LinearConstraint(A, 1.0, np.inf),
               integrality=np.ones(m), bounds=Bounds(0, 1), options=_opts())
    st = int(res.status)
    if st != 0 or res.x is None:
        return None, None, f"ilp_status_{st}:{getattr(res,'message','')}"
    y = [int(v) for v in res.x]
    if any(abs(a - b) > INTEG_TOL for a, b in zip(res.x, y)):
        return None, None, "ilp_nonintegral"
    return int(round(res.fun)), [cand[i] for i in range(m) if y[i]], "ilp_optimal"


def solve_max_packing(masks, nedges, prefer="brute"):
    """returns (value, indices, method, certified_bool, note). Brute when it fits,
    ILP otherwise; if both run they must agree."""
    b, bi, bn = brute_packing(masks)
    i, ii, inm = ilp_packing(masks, nedges)
    if b is not None and i is not None:
        ok = (b == i)
        return b, (bi if ok else None), f"brute+ilp_agree={ok}", ok, bn + "/" + inm
    if b is not None:
        return b, bi, "brute_only", True, f"ilp_unusable:{inm}"
    if i is not None:
        return i, ii, "ilp_optimal_only", True, f"brute:{bn}"
    return None, None, "none", False, f"brute:{bn}; ilp:{i if i is not None else inm}"


def solve_min_cover(masks, cand, prefer="brute"):
    b, bi, bn = brute_cover(masks, cand)
    i, ii, inm = ilp_cover(masks, cand)
    if b is not None and i is not None:
        ok = (b == i)
        return b, (bi if ok else None), f"brute+ilp_agree={ok}", ok, bn + "/" + inm
    if b is not None:
        return b, bi, "brute_only", True, f"ilp_unusable:{inm}"
    if i is not None:
        return i, ii, "ilp_optimal_only", True, f"brute:{bn}"
    return None, None, "none", False, f"brute:{bn}; ilp:{i if i is not None else inm}"


# ---------------------------------------------------------------- main verify
def verify(n, colorstring, claims=None):
    pl, ed, rd = decode(n, colorstring)
    verts, masks, reds, viol = triangles_of(n, pl, ed, rd)
    out = {"engine": "round11/B/verify_witness.py (standalone)",
           "n": n, "colorstring": colorstring,
           "vertices": list(range(n)),
           "edges_present": sorted([list(e) for e in ed]),
           "red_edges": sorted([list(e) for e in rd]),
           "triangles": [list(t) for t in verts],
        "red_edge_of_triangle": [[[t[0], t[1], t[2]], [pl[rr][0], pl[rr][1]]]
                                 for t, rr in zip(verts, reds) if rr is not None],
           "triangle_edge_indices": [_bits(m) for m in masks],
           "n_triangles": len(masks),
           "triangle_constraints": {"every_triangle_exactly_one_red": not viol,
                                    "violations": viol}}
    if not masks:
        out.update({"eligible": False, "rejection_reason": "no_triangle",
                    "certified": True, "verified": False,
                    "exit_code": 1})
        return out

    # red-edge participation counts (only red edges that are THE red edge of a triangle)
    redcount = {}
    for m, rr in zip(masks, reds):
        if rr is None:
            continue
        redcount[rr] = redcount.get(rr, 0) + 1
    r = len(redcount)
    s = sum(1 for c in redcount.values() if c >= 2)
    priv_idx = [j for j, (m, rr) in enumerate(zip(masks, reds))
                if rr is not None and redcount[rr] == 1]

    cand = sorted({b for m in masks for b in _bits(m)})
    p, pick, pmeth, pok, pnote = solve_max_packing(masks, len(pl))
    tau, cov, cmeth, cok, cnote = solve_min_cover(masks, cand)
    pp, ppick, ppmeth, ppok, ppnote = (
        solve_max_packing([masks[j] for j in priv_idx], len(pl)) if priv_idx else (0, [], "brute", True, "no_private_triangle"))

    certified = bool(pok and cok and ppok and p is not None and tau is not None and pp is not None)
    # literal re-checks of the returned witnesses
    def _disjoint(idx_list):
        seen = set()
        for j in idx_list or []:
            bs = _bits(masks[j])
            if seen & set(bs):
                return False
            seen |= set(bs)
        return True
    checks = {
        "packing_value_matches_witness_length": (pick is None or len(pick) == p),
        "packing_is_edge_disjoint": _disjoint(pick),
        "private_packing_value_matches_length": (ppick is None or len(ppick) == pp),
        "private_packing_is_edge_disjoint": _disjoint([priv_idx[j] for j in (ppick or [])]),
        "private_packing_red_edges_globally_private":
            all(redcount[reds[priv_idx[j]]] == 1 for j in (ppick or [])),
        "cover_size_matches_witness_length": (cov is None or len(cov) == tau),
        "cover_hits_every_triangle": all(set(cov or []) & set(_bits(m)) for m in masks),
        "cover_edges_are_present_edges": all(pl[c] in ed for c in (cov or [])),
        "nu_le_tau": (p is not None and tau is not None and p <= tau),
        "tau_le_3nu": (p is not None and tau is not None and tau <= 3 * p),
        "r_le_3nu": p is not None and r <= 3 * p,
    }
    premises = {
        "every_triangle_exactly_one_red": not viol,
        "p_positive": (p is not None and p > 0),
        "p_private_equals_p": (p is not None and pp == p),
        "r_le_3p": (p is not None and r <= 3 * p),
        "connected": connected(n, ed),
        "simple_finite_graph_by_construction": True,
    }
    eligible = all(premises.values())
    out.update({
        "p": p, "p_private": pp, "tau": tau, "r": r, "s": s,
        "nonprivate_red_edges": [[list(pl[b]), redcount[b]] for b in sorted(redcount)
                                 if redcount[b] >= 2],
        "private_red_edge_count": sum(1 for c in redcount.values() if c == 1),
        "tau_over_p": (None or tau / p) if (p and tau) else None,
        "witness_test_tau_gt_199p_over_100": (p is not None and tau is not None
                                              and 100 * tau > 199 * p),
        "margin_100tau_minus_199p": (None if tau is None or p is None else 100 * tau - 199 * p),
        "packing_Q_triangles": [list(verts[j]) for j in (pick or [])],
        "packing_Q_red_edges": [[pl[reds[j]][0], pl[reds[j]][1]] for j in (pick or [])],
        "private_packing_Q_triangles": [list(verts[priv_idx[j]]) for j in (ppick or [])],
        "edge_cover_certificate": [[pl[c][0], pl[c][1]] for c in sorted(cov or [])],
        "methods": {"p": pmeth, "p_note": pnote, "p_private": ppmeth, "pp_note": ppnote,
                    "tau": cmeth, "tau_note": cnote},
        "premises": premises, "eligible": eligible,
        "literal_checks": checks,
    })
    mismatch = {}
    if claims:
        keymap = {"p": "p", "nu": "p", "p_private": "p_private", "nu_private": "p_private",
                  "tau": "tau", "r": "r", "s": "s", "eligible": "eligible"}
        for k, v in claims.items():
            if k in keymap and v is not None and out.get(keymap[k]) is not None:
                if out[keymap[k]] != v:
                    mismatch[k] = {"claimed": v, "verified": out[keymap[k]]}
    out["claim_mismatches"] = mismatch
    out["certified"] = certified
    out["verified"] = bool(certified and eligible and all(checks.values()) and not mismatch)
    out["exit_code"] = 2 if not certified else (1 if not (eligible and all(checks.values())
                                                          and not mismatch) else 0)
    return out


def _claim_keys(d):
    return {k: d[k] for k in ("p", "nu", "p_private", "nu_private", "tau", "r", "s",
                              "eligible") if k in d}


def _load_inputs(path):
    obj = json.loads(Path(path).read_text(encoding="utf-8"))
    items = []
    if isinstance(obj, dict):
        for field in ("instances", "inputs", "retained", "witnesses", "top_examples",
                      "controls", "examples"):
            if isinstance(obj.get(field), list):
                for it in obj[field]:
                    if isinstance(it, dict):
                        items.append(it)
                if items:
                    return obj, items
        if "colorstring" in obj or "key" in obj:
            items.append(obj)
    elif isinstance(obj, list):
        items = [it for it in obj if isinstance(it, dict)]
    return obj, items


def main(argv=None):
    ap = argparse.ArgumentParser(description="standalone literal verifier (read-only)")
    ap.add_argument("--n", type=int)
    ap.add_argument("--colorstring", "--color", dest="colorstring")
    ap.add_argument("--file")
    ap.add_argument("--id", dest="iid")
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args(argv)
    reports, codes = [], []
    if a.file:
        _, items = _load_inputs(a.file)
        sel = []
        for it in items:
            cs = it.get("colorstring") or it.get("key")
            if not cs or "n" not in it:
                continue
            nm = str(it.get("name") or it.get("id") or it.get("control") or "?")
            if a.iid and nm != a.iid:
                continue
            sel.append((nm, int(it["n"]), cs,
                        _claim_keys(it) or _claim_keys(it.get("expected") or {})))
        if not sel:
            print(json.dumps({"error": f"no verifiable inputs with n+colorstring in {a.file}"}))
            return 1
        if not a.all and a.iid is None:
            sel = sel[:1]
        for nm, n, cs, cl in sel:
            rep = verify(n, cs, cl)
            rep["source_file"] = a.file
            rep["instance_name"] = nm
            reports.append(rep)
            codes.append(rep["exit_code"])
    elif a.n is not None and a.colorstring:
        rep = verify(a.n, a.colorstring)
        reports, codes = [rep], [rep["exit_code"]]
    else:
        ap.error("need --n and --colorstring, or --file")
    if len(reports) == 1:
        print(json.dumps(reports[0], indent=1, default=str))
    else:
        print(json.dumps({"verified_count": sum(1 for c in codes if c == 0),
                          "results": reports}, indent=1, default=str))
    return max(codes)


if __name__ == "__main__":
    sys.exit(main())
