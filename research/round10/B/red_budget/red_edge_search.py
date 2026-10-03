#!/usr/bin/env python3
"""Round10 / Role B (v4, REPAIRED): exact search for a witness to E: tau <= 199p/100.

WITHDRAWN: the first red_budget run (its tau was a triangle VERTEX cover, its greedy Q was
not a certified maximum packing, and its per-n quota never decremented so the cap was spent
before n=6..8). No count from it is cited here.

Setting (parent's premises, imposed not derived): H finite simple, each edge red/blue, EVERY
triangle of H has EXACTLY ONE red edge.
  nu          = max # pairwise EDGE-disjoint triangles (exact bitset branch and bound) + witness
  nu_private  = same, over triangles whose red edge lies in exactly ONE triangle of H (globally
                private).  Premise nu_private == nu > 0, witnessed by a returned packing Q.
  tau         = TUZA EDGE transversal: min #edges meeting every triangle (exact) + witness cover.
  r           = #red edges lying in >= 1 triangle.  Premise r <= 3 nu.
Checked invariants on every eligible instance: nu <= tau <= 3 nu, and tau <= 2 nu under the
all-private premise (violations are REPORTED, never assumed away).
Witness test: 100*tau > 199*nu with nu <= 9 (given tau <= 2 nu this means tau == 2 nu).
tau/nu are exact GLOBAL optima; nu_private only restricts which packing family is admitted.
No theorem or proof is claimed anywhere in these files.

Run:  python red_edge_search.py
      python red_edge_search.py --verify <n> <colorstring>     (independent exact recompute)
colorstring: one char per vertex pair (i,j), i<j, lexicographic: 0 absent, B blue, R red.
"""
import itertools, json, random, sys, time
from pathlib import Path

OUT = Path(__file__).resolve().parent
SELF_LIMIT = 95.0                 # hard budget is 120 s wall
MAX_ATTEMPTS = 20000
ELIG_PER_N = 200
NS = (5, 6, 7, 8)
NODE_CAP = 400000
T0 = time.time()
RANDOM = {}


class Over(Exception):
    pass


def tick():
    if time.time() - T0 > SELF_LIMIT:
        raise Over()


def bits(m):
    out = []
    while m:
        b = m & -m
        out.append(b.bit_length() - 1)
        m ^= b
    return out


def pairs_of(n):
    return list(itertools.combinations(range(n), 2))


def key_of(n, ed, rd):
    return "".join("R" if e in rd else ("B" if e in ed else "0") for e in pairs_of(n))


def connected(n, ed):
    adj = {v: set() for v in range(n)}
    for a, b in ed:
        adj[a].add(b)
        adj[b].add(a)
    if not adj:
        return False
    seen, fr = {0}, [0]
    while fr:
        u = fr.pop()
        for w in adj[u] - seen:
            seen.add(w)
            fr.append(w)
    return len(seen) == n


def tri_masks(n, ed):
    eid = {e: i for i, e in enumerate(pairs_of(n))}
    out = []
    for (a, b, c) in itertools.combinations(range(n), 3):
        es = [(a, b), (a, c), (b, c)]
        if all(e in ed for e in es):
            m = 0
            for e in es:
                m |= 1 << eid[e]
            out.append(((a, b, c), m))
    return out


def _pack_rec(ms, i, used, memo, nodes):
    if i == len(ms):
        return 0
    key = (i, used)
    v = memo.get(key)
    if v is not None:
        return v
    nodes[0] += 1
    if nodes[0] > NODE_CAP:
        raise Over()
    best = _pack_rec(ms, i + 1, used, memo, nodes)
    if not (used & ms[i]):
        cand = 1 + _pack_rec(ms, i + 1, used | ms[i], memo, nodes)
        if cand > best:
            best = cand
    memo[key] = best
    return best


def max_packing(masks):
    """exact maximum pairwise-edge-disjoint triangle packing + witness; None if not certified"""
    ms = tuple(masks)
    memo, nodes = {}, [0]
    try:
        p = _pack_rec(ms, 0, 0, memo, nodes)
        if p == 0:
            return 0, []
        res, used, need = [], 0, p
        for i, m in enumerate(ms):
            if need == 0:
                break
            if not (used & m) and 1 + _pack_rec(ms, i + 1, used | m, memo, nodes) == need:
                used |= m
                res.append(m)
                need -= 1
        return p, res
    except Over:
        return None


def edge_cover(masks, cap_size):
    """exact Tuza EDGE transversal over triangle edge masks, with witness; None if not certified"""
    ms = tuple(sorted(masks, key=lambda m: bin(m).count("1")))
    hit = {}
    for m in ms:
        for b in bits(m):
            hit[b] = hit.get(b, 0) + 1
    cap_hit = max(hit.values())
    memo, nodes = {}, [0]

    def rec(rem, k):
        if not rem:
            return ()
        if k == 0:
            return None
        key = (rem, k)
        if key in memo:
            return memo[key]
        if (len(rem) + cap_hit - 1) // cap_hit > k:
            memo[key] = None
            return None
        nodes[0] += 1
        if nodes[0] > NODE_CAP:
            raise Over()
        t = min(rem, key=lambda m: sum(hit.get(b, 0) for b in bits(m)))
        rest = tuple(m for m in rem if m != t)
        res = None
        for b in sorted(bits(t), key=lambda x: -hit.get(x, 0)):
            r2 = rec(tuple(m for m in rest if not (m >> b) & 1), k - 1)
            if r2 is not None:
                res = (b,) + r2
                break
        memo[key] = res
        return res

    try:
        for s in range(1, cap_size + 1):
            r = rec(ms, s)
            if r is not None:
                return s, list(r)
        return None
    except Over:
        return None


def analyse(n, ed, rd):
    """recompute everything from scratch; returns dict, or (None, reason) when a premise fails"""
    pl = pairs_of(n)
    tris = tri_masks(n, ed)
    if not tris:
        return None, "no_triangle"
    redcount = {}
    for (t, m) in tris:
        rr = [b for b in bits(m) if pl[b] in rd]
        if len(rr) != 1:
            return None, "not_exactly_one_red"
        redcount[rr[0]] = redcount.get(rr[0], 0) + 1
    r = len(redcount)
    masks = [m for _, m in tris]
    mp = max_packing(masks)
    if mp is None:
        return None, "packing_not_exact"
    nu, _ = mp
    if nu == 0:
        return None, "nu_zero"
    priv = [m for (t, m) in tris
            if redcount[next(b for b in bits(m) if pl[b] in rd)] == 1]
    mq = max_packing(priv)
    if mq is None:
        return None, "private_packing_not_exact"
    nu_priv, Q = mq
    if nu_priv != nu or len(Q) != nu:
        return None, "private_premise_fails"
    if r > 3 * nu:
        return None, "r_gt_3nu"
    if not connected(n, ed):
        return None, "disconnected"
    ec = edge_cover(masks, 3 * nu)
    if ec is None:
        return None, "cover_not_exact"
    tau, cover = ec
    return {"n": n, "key": key_of(n, ed, rd), "nu": nu, "nu_private": nu_priv, "tau": tau,
            "r": r, "cover": cover, "Q": Q, "tris": tris, "masks": masks, "pl": pl,
            "ed": set(ed), "rd": set(rd), "redcount": redcount, "ntri": len(tris)}


def dump(a):
    n, pl, red, masks = a["n"], a["pl"], a["rd"], a["masks"]
    qe = [b for m in a["Q"] for b in bits(m)]
    cov = set(a["cover"])
    redb = lambda m: next(b for b in bits(m) if pl[b] in red)
    return {
        "n": n, "colorstring": a["key"], "pair_order": [list(x) for x in pl],
        "edges": [[[pl[b][0], pl[b][1]], "red" if pl[b] in red else "blue"]
                  for b in sorted(i for i, e in enumerate(pl) if e in a["ed"])],
        "triangles": [[[list(t)], [[pl[x][0], pl[x][1]] for x in bits(m)]] for t, m in a["tris"]],
        "red_edge_per_triangle": [{"triangle": list(t), "red_edge": [pl[redb(m)][0], pl[redb(m)][1]]}
                                  for t, m in a["tris"]],
        "nu": a["nu"], "nu_private": a["nu_private"], "tau": a["tau"], "r": a["r"],
        "tau_over_nu": a["tau"] / a["nu"], "margin_100tau_minus_199nu": 100 * a["tau"] - 199 * a["nu"],
        "edge_cover_certificate": [[pl[b][0], pl[b][1]] for b in sorted(cov)],
        "packing_Q_certificates": [[[pl[x][0], pl[x][1]] for x in bits(m)] for m in a["Q"]],
        "checks": {"nu_le_tau": a["nu"] <= a["tau"], "tau_le_3nu": a["tau"] <= 3 * a["nu"],
                   "tau_le_2nu_under_private_premise": a["tau"] <= 2 * a["nu"],
                   "cover_size_eq_tau": len(cov) == a["tau"],
                   "cover_hits_every_triangle": all(cov & set(bits(m)) for m in masks),
                   "Q_length_eq_nu": len(a["Q"]) == a["nu"],
                   "Q_edge_disjoint": len(qe) == len(set(qe)),
                   "Q_red_globally_private": all(a["redcount"][redb(m)] == 1 for m in a["Q"]),
                   "r_le_3nu": a["r"] <= 3 * a["nu"]},
        "verifier_cmd": "python red_edge_search.py --verify %d %s" % (n, a["key"]),
    }


def consider(a, st, best, wit):
    """account for one eligible instance; returns True when a certified witness was found"""
    n = a["n"]
    b = st["per_n"][n]
    b["eligible"] += 1
    b["exact_solved"] += 1
    st["eligible_total"] += 1
    b["hist_nu"][str(a["nu"])] = b["hist_nu"].get(str(a["nu"]), 0) + 1
    rat = f"{a['tau']}/{a['nu']}"
    b["hist_tau_over_nu"][rat] = b["hist_tau_over_nu"].get(rat, 0) + 1
    if a["tau"] > 2 * a["nu"]:
        b["tau_gt_2nu"] += 1
    if a["tau"] / a["nu"] > b["best_tau_over_nu"]:
        b["best_tau_over_nu"] = a["tau"] / a["nu"]
    if a["tau"] / a["nu"] > best[0]:
        best[0] = a["tau"] / a["nu"]
        best[1] = dump(a)
    if 100 * a["tau"] > 199 * a["nu"] and a["nu"] <= 9:
        d = dump(a)
        wit[a["key"]] = d
        if all(d["checks"].values()):
            st["stop"] = "WITNESS accepted, all literal checks True"
            return True
        st.setdefault("bad_witness_checks", {})[a["key"]] = d["checks"]
    return False


def g_random(n, q, rho, rng):
    ed, rd = set(), set()
    for e in pairs_of(n):
        if rng.random() < q:
            ed.add(e)
            if rng.random() < rho:
                rd.add(e)
    return ed, rd


def g_assign_red(n, rng, q):
    """random graph, then put exactly one red edge on each triangle (consistency re-checked)"""
    ed = {e for e in pairs_of(n) if rng.random() < q}
    tris = tri_masks(n, ed)
    if not tris:
        return None
    pl = pairs_of(n)
    rd = set()
    for (t, m) in tris:
        rd.add(pl[rng.choice(bits(m))])
    return ed, ed & rd


def g_books(n, rng, t=None):
    """several edge-disjoint books sharing only vertex 0; each book = triangles through one spine.
       red edges are placed on non-spine edges so they can be globally private."""
    spines = rng.sample(range(1, n), t or rng.randint(2, max(2, (n - 1) // 2)))
    ed, rd = set(), set()
    used = set(spines)
    for s in spines:
        ed.add((0, s))
        rim = [v for v in range(1, n) if v != s and v not in used]
        for _ in range(rng.randint(1, 2)):
            if not rim:
                break
            v = rim.pop(rng.randrange(len(rim)))
            used.add(v)
            ed |= {(0, v), (min(s, v), max(s, v))}
    tris = tri_masks(n, ed)
    if not tris:
        return None
    pl = pairs_of(n)
    for (t_, m) in tris:
        opts = [pl[b] for b in bits(m) if pl[b] != (0, min(t_[1], t_[2])) and pl[b] != (0, max(t_[1], t_[2]))]
        rd.add(rng.choice(opts) if opts else pl[bits(m)[0]])
    return ed, ed & rd


def g_tripartite(n, rng):
    vs = list(range(n))
    rng.shuffle(vs)
    c = sorted(rng.sample(range(1, n), 2))
    A, B, C = vs[:c[0]], vs[c[0]:c[1]], vs[c[1]:]
    if not (A and B and C):
        return None
    ed, rd = set(), set()
    for x, y in itertools.product(A, B):
        if rng.random() < 0.8:
            e = (min(x, y), max(x, y))
            ed.add(e)
            rd.add(e)
    for x, y in list(itertools.product(A, C)) + list(itertools.product(B, C)):
        if rng.random() < 0.45:
            ed.add((min(x, y), max(x, y)))
    return ed, rd


STRATA = [("assign", q) for q in (0.5, 0.6, 0.7, 0.8, 0.9)] + \
         [("rand", q, rho) for q, rho in ((0.55, .33), (0.7, .4), (0.8, .3))] + \
         [("books", 0), ("tripartite", 0)]


def generate(n, s, rng):
    if s[0] == "assign":
        return g_assign_red(n, rng, s[1])
    if s[0] == "rand":
        return g_random(n, s[1], s[2], rng)
    if s[0] == "books":
        return g_books(n, rng)
    return g_tripartite(n, rng)


def systematic(st, best, wit):
    """Edge-coloured graphs on n=3,4,5; record truncation at the eligible quota."""
    for n in (3, 4, 5):
        pl = pairs_of(n)
        m = len(pl)
        b = st["per_n"][n]
        b["systematic_scanned"] = 0
        b["systematic_total"] = 3 ** m
        for code in range(3 ** m):
            tick()
            b["systematic_scanned"] += 1
            x, ed, rd = code, set(), set()
            for i in range(m):
                d = x % 3
                x //= 3
                if d:
                    ed.add(pl[i])
                if d == 2:
                    rd.add(pl[i])
            b["attempts"] += 1
            st["attempts_total"] += 1
            a = analyse(n, ed, rd)
            if isinstance(a, tuple):
                b["reject"][a[1]] = b["reject"].get(a[1], 0) + 1
                st["reasons"][a[1]] = st["reasons"].get(a[1], 0) + 1
                if a[1].endswith("not_exact"):
                    b["not_exact_skips"] += 1
                continue
            b["systematic_eligible"] = b.get("systematic_eligible", 0) + 1
            if consider(a, st, best, wit):
                st["stop"] += f" (systematic n={n})"
                return True
            if b["eligible"] >= ELIG_PER_N:
                b["systematic_truncated_at_cap"] = True
                break
        b["systematic_complete"] = b["systematic_scanned"] == b["systematic_total"]


def randoms(st, best, wit):
    for rnd in range(600):
        alive = [n for n in (6, 7, 8)
                 if st["per_n"][n]["eligible"] < ELIG_PER_N and st["per_n"][n]["attempts"] < MAX_ATTEMPTS // 3]
        if not alive:
            st["stop"] = "per-n eligible caps / attempt caps reached for n=6,7,8"
            return False
        for n in alive:
            for s in STRATA:
                b = st["per_n"][n]
                if b["eligible"] >= ELIG_PER_N or st["attempts_total"] >= MAX_ATTEMPTS:
                    continue
                for _ in range(12):
                    if b["eligible"] >= ELIG_PER_N or st["attempts_total"] >= MAX_ATTEMPTS:
                        break
                    tick()
                    g = generate(n, s, RANDOM[n])
                    b["attempts"] += 1
                    st["attempts_total"] += 1
                    if g is None:
                        b["reject"]["generator_reject"] = b["reject"].get("generator_reject", 0) + 1
                        continue
                    a = analyse(n, g[0], g[1])
                    if isinstance(a, tuple):
                        b["reject"][a[1]] = b["reject"].get(a[1], 0) + 1
                        st["reasons"][a[1]] = st["reasons"].get(a[1], 0) + 1
                        if a[1].endswith("not_exact"):
                            b["not_exact_skips"] += 1
                        continue
                    if consider(a, st, best, wit):
                        st["stop"] += f" (random n={n})"
                        return True
    st["stop"] = "stratified rounds exhausted"
    return False


def self_checks():
    out = {}
    a = analyse(3, {(0, 1), (0, 2), (1, 2)}, {(0, 1)})
    out["one_triangle"] = {"nu": a["nu"], "tau": a["tau"], "r": a["r"], "nu_private": a["nu_private"],
                           "expected": "nu=1 tau=1 (ratio 1), private premise HOLDS",
                           "checks": dump(a)["checks"]}
    ed = set(itertools.combinations(range(4), 2))
    rd = {(0, 1), (2, 3)}
    a = analyse(4, ed, rd)
    gate = "eligible" if isinstance(a, dict) else a[1]
    tris = tri_masks(4, ed)
    pl = pairs_of(4)
    nu, _ = max_packing([m for _, m in tris])
    tau, cov = edge_cover([m for _, m in tris], 3 * nu)
    rc = {}
    for (t, m) in tris:
        b = next(x for x in bits(m) if pl[x] in rd)
        rc[b] = rc.get(b, 0) + 1
    priv = [m for (t, m) in tris
            if rc[next(x for x in bits(m) if pl[x] in rd)] == 1]
    nu_priv, _ = max_packing(priv)
    out["K4_red_perfect_matching"] = {
        "every_triangle_exactly_one_red": all(len([x for x in bits(m) if pl[x] in rd]) == 1 for _, m in tris),
        "tau_edge_transversal": tau, "cover": [[pl[x][0], pl[x][1]] for x in sorted(cov)],
        "nu_edge_disjoint_packing": nu, "tau_eq_2nu": tau == 2 * nu,
        "nu_private": nu_priv, "premise_holds": nu_priv == nu, "full_gate": gate,
        "note": "ratio 2 for the GLOBAL quantities, but each red edge of K4 lies in 2 triangles, "
                "so nu_private=0 != nu=1 and the private premise EXCLUDES it. Global tau/nu and "
                "private-only packing are different objects."}
    cycle = {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}
    cone = cycle | {(i, 5) for i in range(5)}
    a = analyse(6, cone, cycle)
    if not isinstance(a, dict):
        raise AssertionError("C5 cone control failed its premises")
    checks = dump(a)["checks"]
    if (a["nu"], a["nu_private"], a["tau"], a["r"]) != (2, 2, 3, 5) or not all(checks.values()):
        raise AssertionError("C5 cone control failed its exact quantities or literal checks")
    out["C5_red_base_blue_apex"] = {
        "nu": a["nu"], "nu_private": a["nu_private"], "tau": a["tau"], "r": a["r"],
        "expected": "nu=nu_private=2, tau=3, r=5; nontrivial ratio 3/2",
        "checks": checks,
    }
    out["invariant_note"] = "nu<=tau<=3nu checked per instance; tau<=2nu under the private premise reported if violated"
    return out


def main():
    global RANDOM
    if len(sys.argv) > 1:
        if len(sys.argv) != 4 or sys.argv[1] != "--verify":
            raise SystemExit("usage: red_edge_search.py [--verify n colorstring]")
        n = int(sys.argv[2])
        colorstring = sys.argv[3]
        pl = pairs_of(n)
        if len(colorstring) != len(pl) or any(ch not in "0BR" for ch in colorstring):
            raise SystemExit("colorstring must have one 0/B/R character per vertex pair")
        ed = {e for e, ch in zip(pl, colorstring) if ch in "BR"}
        rd = {e for e, ch in zip(pl, colorstring) if ch == "R"}
        result = analyse(n, ed, rd)
        if isinstance(result, dict):
            output = {"n": n, "colorstring": colorstring, "meets_all_premises": True,
                      "certificate": dump(result)}
        else:
            output = {"n": n, "colorstring": colorstring, "meets_all_premises": False,
                      "rejection_reason": result[1]}
        print(json.dumps(output, indent=1, default=str))
        return
    for i, n in enumerate(NS):
        RANDOM[n] = random.Random(20260815 + 1000 * i)
    sc = self_checks()
    st = {"per_n": {n: {"attempts": 0, "eligible": 0, "exact_solved": 0, "not_exact_skips": 0,
                        "reject": {}, "tau_gt_2nu": 0, "best_tau_over_nu": 0.0,
                        "hist_nu": {}, "hist_tau_over_nu": {}} for n in (3, 4, 5, 6, 7, 8)},
          "attempts_total": 0, "eligible_total": 0, "reasons": {}, "stop": ""}
    for k in (3, 4, 5, 6, 7, 8):
        if k not in RANDOM:
            RANDOM[k] = random.Random(20260815 + 1000 * k)
    best = [0.0, None]
    wit = {}
    hit = "cap"
    try:
        if not systematic(st, best, wit):
            randoms(st, best, wit)
    except Over:
        st["stop"] = "time budget hit (partial search)"
    st["attempts_cap"] = MAX_ATTEMPTS
    payload = {"correction": "tau = Tuza EDGE transversal over triangle edge masks (bitset); "
                             "nu = exact max edge-disjoint packing with witness; Q = returned "
                             "maximum private packing verified len(Q)==nu, disjoint, private; "
                             "per-n budgets interleaved and systematic n<=5 block first.",
               "withdrawn": "first red_budget run (vertex-cover tau, greedy Q, dead per-n quota)",
               "setting": "red/blue colouring, every triangle exactly one red edge (parent's premises)",
               "definitions": {"nu": "max edge-disjoint triangle packing (exact)",
                               "nu_private": "max packing over globally-private-red triangles",
                               "tau": "min edge set meeting every triangle (exact)",
                               "r": "red edges lying in >=1 triangle"},
               "premises": ["every triangle exactly 1 red", "nu_private == nu > 0 (witnessed by Q)",
                            "r <= 3 nu", "H connected"],
               "invariants_checked": list(sc["invariant_note"].split(";")),
               "witness_test": "100*tau > 199*nu with nu<=9; stop immediately on a certified witness",
               "budgets": {"hard_wall_s": 120.0, "self_limit_s": SELF_LIMIT,
                           "max_colored_attempts": MAX_ATTEMPTS, "eligible_per_n": ELIG_PER_N,
                           "systematic_block": "n=3,4,5 coloured-graph loops, each marked complete or quota-truncated",
                           "random_block": "n=6,7,8 stratified seeded",
                           "exactness": "instances whose nu or tau is not certified are SKIPPED"},
               "self_checks": sc, "stats": st, "best_record": best[1],
               "witness_count": len(wit), "witnesses": list(wit.values())[:10],
               "disclaimer": "Bounded search. Nothing here is a theorem or a proof; 'no witness "
                             "found' is a statement about this budget and these families only."}
    (OUT / "results_v3.json").write_text(json.dumps(payload, indent=1, default=str), encoding="utf-8")
    write_report(sc, st, best, wit)
    print(json.dumps({"stop": st["stop"], "attempts": st["attempts_total"],
                      "eligible": st["eligible_total"], "best_ratio": best[0],
                      "witnesses": len(wit),
                      "per_n": {str(k): {kk: vv for kk, vv in v.items() if kk not in ("hist_nu",)}
                                for k, v in sorted(st["per_n"].items()) if v["attempts"]},
                      "self_checks": sc}, indent=1, default=str))


def write_report(sc, st, best, wit):
    k4 = sc["K4_red_perfect_matching"]
    c5 = sc["C5_red_base_blue_apex"]
    L = ["# Round10 / Role B (v4, REPAIRED) - Tuza EDGE transversal search for E: tau <= 199p/100",
         "",
         "Withdrawn: first red_budget run (tau was a VERTEX cover; greedy Q was not a certified",
         "maximum packing; per-n quota never decremented so the cap was spent before n=6..8).",
         "Here tau = min EDGE set meeting every triangle and nu = max edge-disjoint triangle",
         "packing, both EXACT bitset branch and bound with returned witnesses; nu_private is the",
         "same packing restricted to globally-private-red triangles. If an optimum is not",
         "certified inside the node budget the instance is SKIPPED (no fractional/timeout value).",
         "Premises imposed (not derived): every triangle exactly 1 red; nu_private==nu>0; r<=3nu; H connected.",
         "",
         "## Self-checks before searching",
         f"- single triangle: nu={sc['one_triangle']['nu']} tau={sc['one_triangle']['tau']} "
         f"nu_private={sc['one_triangle']['nu_private']} r={sc['one_triangle']['r']} -> ratio 1, premise holds",
         f"- K4, red = perfect matching: every triangle exactly 1 red = {k4['every_triangle_exactly_one_red']}; "
         f"EDGE tau={k4['tau_edge_transversal']} nu={k4['nu_edge_disjoint_packing']} tau==2nu: {k4['tau_eq_2nu']}; "
         f"nu_private={k4['nu_private']} -> premise nu_private==nu: {k4['premise_holds']} (gate: {k4['full_gate']})",
         f"- so the ratio-2 example is a GLOBAL tau/nu fact that the private premise EXCLUDES: "
         "every K4 edge (hence every red edge) lies in 2 triangles. Global cover/packing and",
         "  private-only packing are different objects and are not conflated below.",
         f"- C5 red-base/blue-apex: nu={c5['nu']} nu_private={c5['nu_private']} "
         f"EDGE tau={c5['tau']} r={c5['r']}; checks={c5['checks']}",
         "",
         "## Per-n accounting  (attempts / eligible / exact / nu-histogram / best tau-over-nu)"]
    L.append(f"{'n':>3} {'attempts':>9} {'eligible':>9} {'exact':>6} {'tau>2nu':>8} {'not_exact':>10} {'best tau/nu':>12}  nu hist")
    for n in sorted(st["per_n"]):
        v = st["per_n"][n]
        if not v["attempts"]:
            continue
        L.append(f"{n:>3} {v['attempts']:>9} {v['eligible']:>9} {v['exact_solved']:>6} "
                 f"{v['tau_gt_2nu']:>8} {v['not_exact_skips']:>10} {v['best_tau_over_nu']:>12.4f}  "
                 f"{v['hist_nu']}" + (f"  systematic scanned={v.get('systematic_scanned')}/"
                                      f"{v.get('systematic_total')} complete={v.get('systematic_complete')}"
                                      if "systematic_scanned" in v else ""))
    L += [f"- totals: coloured attempts {st['attempts_total']} (cap {MAX_ATTEMPTS}), eligible "
          f"{st['eligible_total']}; stop: {st['stop'] or 'completed'}; wall {round(time.time()-T0,2)}s (hard 120s)",
          "- eligible counts are instance occurrences; sampled colourings are not deduplicated",
          "  by key or graph isomorphism. The C5 ratio-3/2 self-check is separate from search results.",
          f"- premise rejections (global): {st['reasons']}",
          f"- ratios seen among eligible: {sorted({r for v in st['per_n'].values() for r in v['hist_tau_over_nu']})}",
          "", "## Best eligible instance (max tau/nu)"]
    b = best[1]
    if b:
        L += [f"- n={b['n']} tau={b['tau']} nu={b['nu']} nu_private={b['nu_private']} r={b['r']} "
              f"tau/nu={b['tau_over_nu']:.6f} margin(100tau-199nu)={b['margin_100tau_minus_199nu']}",
              f"- colouring {b['colorstring']} over pairs {b['pair_order']}",
              f"- edge cover ({b['tau']} edges): {b['edge_cover_certificate']}  |  Q ({b['nu']} triangles): "
              f"{b['packing_Q_certificates']}",
              f"- literal checks: {b['checks']}",
              f"- single-instance re-check (same implementation): {b['verifier_cmd']}"]
    L += ["", "## Witness: tau > 199nu/100 (i.e. tau == 2nu here) with nu <= 9"]
    if wit:
        for w in list(wit.values())[:4]:
            L.append(f"- FOUND n={w['n']} tau={w['tau']} nu={w['nu']} colouring {w['colorstring']} "
                     f"cover={w['edge_cover_certificate']} Q={w['packing_Q_certificates']} checks={w['checks']}")
    else:
        L += ["- none found in this budget. Every eligible instance examined here had tau/nu <= best",
              "  above, so this run neither produces a counterexample to E nor establishes E. Not a theorem."]
    L += ["", "## Scope / honesty",
          "- systematic loops on n=3,4,5 are exhaustive only where the per-n 'complete' flag is True;",
          "  n=5 may stop early at its eligible quota. Stratified seeded samples for n=6,7,8 use",
          "  at most 200 eligible per n and <=20000 attempts total. No exhaustive claim for",
          "  quota-truncated or randomly sampled orders.",
          "- p_private==p and r<=3p are imposed; no graph-theoretic reason is asserted for either.",
          "- No census, no downloads, no LP for tau. Full data: results_v3.json in this directory."]
    (OUT / "report.txt").write_text("\n".join(L) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
