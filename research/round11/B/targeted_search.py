#!/usr/bin/env python3
"""Round11 / Role B (numerical analyst, no proof declared): targeted attack on
RB(1/100) -- find an exact instance with tau > 199p/100, or hard instances that carry
NON-PRIVATE (multipage) red edges and a high tau/p ratio.

Setting (premises imposed, not derived): H finite simple red/blue, EVERY triangle has
EXACTLY ONE red edge;
  p          = max # pairwise EDGE-disjoint triangles (exact) with a returned packing
  p_private  = max packing over triangles whose red edge lies in exactly ONE triangle
               of H.  Premise p_private == p > 0  <=>  "there is a maximum packing Q
               whose red edges are globally private".
  tau        = min # graph EDGES meeting every triangle (Tuza EDGE transversal, exact)
  r          = # red edges lying in >= 1 triangle;  premise r <= 3p
  s          = # participating red edges lying in >= 2 triangles (multipage red edges)

Engines, deliberately doubled:
  A) the AUDITED round10 edge-mask solver, imported read-only from
     research/round10/B/red_budget/red_edge_search.py (graph-EDGE masks; tau is NOT a
     vertex cover; maximum packings with witnesses; instance skipped, never guessed, if
     an optimum is not certified inside the node cap). Historical round10 files are not
     modified; only the imported module's NODE_CAP global is set for this run.
  B) research/round11/B/verify_witness.py, a standalone re-derivation (exhaustive
     subsets for small inputs, scipy/HiGHS ILP accepted only at status Optimal).
Every retained example and every control must agree between A and B.

Round10 diagnostic weakness being fixed here: 899 eligible random occurrences all had
tau = p (the private premise plus iid-sparse colourings almost never produce a red edge
in >= 2 triangles, and never a packing-dominated multipage cluster). This stage-1 file
therefore searches STRUCTURED seeds (odd-cycle red cones, cone pairs linked by a
triangle-free bridge, book/page attachments, private-triangle attachments) and mutates
VALID parents through slightly relaxed intermediate states.

STAGE 1 (what is allowed to run now):  python targeted_search.py controls
STAGE 2 (after Role C audits):         python targeted_search.py full
Single-instance re-check (read-only):   python targeted_search.py verify <n> <colorstring>
Nothing in this file is a theorem or a proof; ratios are statements about the printed
instances only.
"""
import argparse, importlib.util, itertools, json, random, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
R10_PATH = REPO / "research" / "round10" / "B" / "red_budget" / "red_edge_search.py"
PRIVATE = REPO / ".codex" / "researchround11" / "B"

sys.setrecursionlimit(20000)

# ---------------------------------------------------------------- budgets (stage-2 plan)
WALL_S = 180.0          # requested wall budget; no OS-level process kill is installed
SELF_LIMIT_S = 150.0    # stop generating/solving here (search is then "partial")
WRITE_DEADLINE_S = 168.0   # artifacts must be written before T0 + this
SOLVE_SLACK_S = 3.0     # never START a solve whose worst case could pass the deadline
MAX_ATTEMPTS = 10000    # unique-or-not generated colourings
MAX_ELIGIBLE = 1000     # exactly eligible inputs analysed end to end
NODE_CAP = 250000       # per exact solve in the imported round10 engine (boundedness of A)
BRUTE_CAP = 1 << 20     # per brute subproblem in the standalone verifier (boundedness of B)
NS = tuple(range(6, 13))
ELIG_PER_N = {n: max(40, MAX_ELIGIBLE // len(NS)) for n in NS}
# reasons that mean "the exact optimum was NOT certified" -- never a premise rejection:
UNCERTIFIED = ("packing_not_exact", "private_packing_not_exact", "cover_not_exact",
               "not_exact_nodecap", "solver_engine_error", "engine_b_not_certified")
# hard-instance-diagnostic retarget (round11 C, citing Role E): with an all-private maximum
# packing Q, tau <= 2p - 1, so a strict RB(1/100) counterexample needs 1.99p < 2p-1, i.e.
# p > 100. At n <= 12 there are at most C(12,2)=66 edges and edge-disjoint triangles use 3p
# distinct ones, so p <= 22 < 101: NO small-order instance can refute RB(1/100). Stage 2
# therefore maximises tau/p among eligible s>0 instances (target > 1.5) and keeps the old
# witness test only as a solver bug alarm (it must never fire at n <= 12).

T0 = [None]


def elapsed():
    return 0.0 if T0[0] is None else time.time() - T0[0]


def solve_time_limit():
    """remaining seconds a sub-solver may still use before the write deadline."""
    return max(0.0, WRITE_DEADLINE_S - SOLVE_SLACK_S - elapsed())


def check_deadline():
    if elapsed() > SELF_LIMIT_S:
        raise Over()
    if solve_time_limit() <= 0.5:
        raise Over()


class WriteMissed(Exception):
    pass


def check_write_slot():
    """raise unless artifacts can still be written before T0 + WRITE_DEADLINE_S."""
    if elapsed() >= WRITE_DEADLINE_S:
        raise WriteMissed()


class Over(Exception):
    pass


def tick():
    if T0[0] is not None and time.time() - T0[0] > SELF_LIMIT_S:
        raise Over()


# ---------------------------------------------------------------- engines
def load_r10():
    """import the audited round10 module WITHOUT touching its files."""
    spec = importlib.util.spec_from_file_location("r10_red_edge_search_audited", str(R10_PATH))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    mod.NODE_CAP = NODE_CAP
    return mod


def snapshot_r10_mtime():
    return {p.relative_to(REPO).as_posix(): [p.stat().st_mtime_ns, p.stat().st_size]
            for p in sorted(R10_PATH.parent.iterdir()) if p.suffix in (".py", ".json", ".txt")}


R10 = load_r10()
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import verify_witness as VW                      # same directory, standalone engine B


def colorstring(n, ed, rd):
    return R10.key_of(n, ed, rd)


def engine_a(n, ed, rd):
    """audited round10 gate + exact quantities. Returns (dict|None, reason|None)."""
    try:
        a = R10.analyse(n, ed, rd)
    except R10.Over:
        return None, "not_exact_nodecap"
    except (RecursionError, RuntimeError):
        return None, "solver_engine_error"
    if isinstance(a, tuple):
        return None, a[1]
    d = R10.dump(a)
    d["s"] = sum(1 for c in a["redcount"].values() if c >= 2)
    d["nonprivate_red"] = sorted([[a["pl"][b][0], a["pl"][b][1], c]
                                  for b, c in a["redcount"].items() if c >= 2])
    d["p"], d["p_private"] = d["nu"], d["nu_private"]      # round11 naming
    d["engine_a_checks"] = d["checks"]
    return d, None


def engine_b(n, cs, claims=None):
    """standalone verifier. Engine B is bounded by the brute subset cap and by a finite
    per-solve scipy.milp time_limit = the wall time still left before the write deadline,
    reset before every call (a time-limited HiGHS status is never read as an optimum)."""
    VW.TIME_LIMIT[0] = solve_time_limit()
    VW.ABS_DEADLINE[0] = (None if T0[0] is None else
                          T0[0] + WRITE_DEADLINE_S - SOLVE_SLACK_S)
    return VW.verify(n, cs, claims)


# ---------------------------------------------------------------- controls (stage 1)
def norm(e):
    return (min(e), max(e))


def _cs_from(n, edges, reds):
    pl = list(itertools.combinations(range(n), 2))
    ed, rd = set(edges), set(reds)
    return "".join("R" if e in rd else ("B" if e in ed else "0") for e in pl)


CYCLE5 = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]
K3_CS = _cs_from(3, [(0, 1), (0, 2), (1, 2)], [(0, 1)])
K4_CS = _cs_from(4, list(itertools.combinations(range(4), 2)), [(0, 1), (2, 3)])
C5_CS = _cs_from(6, CYCLE5 + [(i, 5) for i in range(5)], CYCLE5)


# Coordinator's REQUIRED s>0 control, supplied literally (not searched). Everything about
# it below -- triangle list, per-edge page counts, p, p_private, tau, r, s -- is produced by
# the two exact solvers (A and B); no triangle enumeration or interpretation is hand-written
# in this file. See research/round11/E/multipage_matching_gap.txt for the family it sits in.
SP8_BLUE = [norm((i, (i + 1) % 8)) for i in range(8)] + [norm((0, 8)), norm((2, 8))]
SP8_RED = [norm(x) for x in [(0, 2), (2, 4), (4, 6), (0, 6), (1, 3), (3, 5), (5, 7), (7, 8)]]
SP8_ED, SP8_RD = set(SP8_BLUE) | set(SP8_RED), set(SP8_RED)
SP8_CS = _cs_from(9, sorted(SP8_ED), sorted(SP8_RD))

CONTROLS = [
    {"name": "K3_single_triangle", "n": 3, "colorstring": K3_CS,
     "expect": {"eligible": True, "p": 1, "p_private": 1, "tau": 1, "r": 1, "s": 0,
                "tau_over_p": 1.0},
     "why": "floor case: one triangle, its red edge is globally private"},
    {"name": "K4_red_perfect_matching", "n": 4, "colorstring": K4_CS,
     "expect": {"eligible": False, "reject": "private_premise_fails",
                "p": 1, "p_private": 0, "tau": 2, "r": 2, "s": 2, "tau_over_p": 2.0},
     "why": "the global ratio-2 example: every K4 edge lies in 2 triangles, so no red "
            "edge is private, p_private=0<p=1 and the private premise REJECTS it. "
            "Must not be reported as a witness to tau>199p/100."},
    {"name": "C5_red_base_blue_apex", "n": 6, "colorstring": C5_CS,
     "expect": {"eligible": True, "p": 2, "p_private": 2, "tau": 3, "r": 5, "s": 0,
                "tau_over_p": 1.5},
     "why": "reference nontrivial ratio 3/2 with a valid private maximum packing "
            "(odd-cycle vertex cover vs matching in the red base)"},
    {"name": "spine8_C4plusoddpath_one_multipage_red", "n": 9, "colorstring": SP8_CS,
     "spec": {"blue": sorted(map(list, SP8_BLUE)), "red": sorted(map(list, SP8_RED))},
     "expect": {"eligible": True, "p": 4, "p_private": 4, "tau": 5, "r": 8, "s": 1,
                "n_triangles": 9, "tau_over_p": 1.25},
     "why": "coordinator-specified REQUIRED s>0 control (supplied, not searched): BLUE "
            "8-cycle on 0..7 plus BLUE (0,8),(2,8); RED (0,2),(2,4),(4,6),(0,6),(1,3), "
            "(3,5),(5,7),(7,8), y = 8. Both exact solvers certify for this literal input: "
            "9 triangles, every triangle exactly one red edge, p = p_private = 4, tau = 5, "
            "r = 8 <= 3p = 12, s = 1 (one participating red edge lies in 2 triangles), "
            "tau/p = 5/4. The triangle list, the red edge of each triangle and the "
            "non-private red edges with their page counts are stored as engine-B output in "
            "stage1_controls.json -- nothing about this instance is asserted by hand here. "
            "Interpretation of the mechanism is Role E/C material "
            "(research/round11/E/multipage_matching_gap.txt); this file states numerics only."},
]


def run_controls(out_prefix, verbose=True):
    T0[0] = time.time()
    before = snapshot_r10_mtime()
    rows, allok = [], True
    for c in CONTROLS:
        n, cs = c["n"], c["colorstring"]
        ed = {e for e, ch in zip(itertools.combinations(range(n), 2), cs) if ch in "BR"}
        rd = {e for e, ch in zip(itertools.combinations(range(n), 2), cs) if ch == "R"}
        a, reason = engine_a(n, ed, rd)
        b = engine_b(n, cs)                      # no claims: pure independent recompute
        q = {"p": b["p"], "p_private": b["p_private"], "tau": b["tau"], "r": b["r"],
             "s": b["s"], "eligible": b["eligible"]}
        agree = None
        if a is not None:
            agree = {k: a.get(k) == b.get(k) for k in ("p", "p_private", "tau", "r", "s")}
        exp = c["expect"]
        got = dict(q)
        got["reject"] = reason
        got["n_triangles"] = b["n_triangles"]
        got["triangle_constraints_ok"] = b["triangle_constraints"]["every_triangle_exactly_one_red"]
        got["violations"] = b["triangle_constraints"]["violations"]
        got["triangles_computed_by_engine_b"] = b["triangles"]
        got["red_edge_of_each_triangle_engine_b"] = b["red_edge_of_triangle"]
        got["nonprivate_red_edges_engine_b"] = b["nonprivate_red_edges"]
        got["p_global_engine_a"] = (a or {}).get("p")
        got["tau_global_engine_a"] = (a or {}).get("tau")
        checks_ok = all(b["literal_checks"].values()) and \
            bool(b["triangle_constraints"]["every_triangle_exactly_one_red"]) and \
            bool(b["certified"])
        match = all(got.get(k) == v for k, v in exp.items()
                    if k not in ("reject", "tau_over_p")) and \
            (exp.get("reject") is None or reason == exp["reject"])
        row = {"control": c["name"], "why": c["why"], "n": n, "colorstring": cs,
               "specified_by": ("coordinator (required s>0 control, supplied not searched)"
                                if "spec" in c else "round10 carry-over"),
               "spec": c.get("spec"),
               "expected": exp, "engine_b_standalone": got,
               "engine_a_reject_reason": reason,
               "engine_a_eligible": a is not None,
               "engines_agree_on_p_tau_r_s": agree,
               "expected_match": match, "literal_checks_ok": checks_ok,
               "verifier_cmd": f"python verify_witness.py --n {n} --colorstring {cs}",
               "b_full": b, "a_full": a}
        rows.append(row)
        allok = allok and match and checks_ok and (agree is None or all(agree.values()))
    after = snapshot_r10_mtime()
    r10_untouched = before == after
    payload = {"stage": 1, "mode": "controls",
               "engines": {"A": R10_PATH.relative_to(REPO).as_posix(),
                           "B": (HERE / "verify_witness.py").relative_to(REPO).as_posix()},
               "budgets_config": {"configured_wall_s": WALL_S, "self_limit_s": SELF_LIMIT_S,
                                  "write_deadline_s": WRITE_DEADLINE_S,
                                  "solve_slack_s": SOLVE_SLACK_S,
                                  "max_attempts": MAX_ATTEMPTS,
                                  "max_eligible": MAX_ELIGIBLE, "node_cap": NODE_CAP,
                                  "brute_cap": BRUTE_CAP,
                                  "ilp_time_limit_policy": "remaining wall before the write "
                                                           "deadline, reset every solve",
                                  "orders": list(NS),
                                  "eligible_per_n": {str(k): v for k, v in ELIG_PER_N.items()},
                                  "uncertified_reasons": list(UNCERTIFIED)},
               "round10_untouched": r10_untouched, "round10_mtimes": after,
               "all_controls_pass": bool(allok and r10_untouched),
               "wall_s": round(time.time() - T0[0], 3), "controls": rows}
    out_prefix.mkdir(parents=True, exist_ok=True)
    (out_prefix / "stage1_controls.json").write_text(json.dumps(payload, indent=1, default=str),
                                                     encoding="utf-8")
    if verbose:
        slim = {"all_controls_pass": payload["all_controls_pass"],
                "round10_untouched": r10_untouched,
                "controls": [{k: r[k] for k in ("control", "n", "colorstring", "expected",
                                                "engine_b_standalone",
                                                "engine_a_reject_reason",
                                                "engines_agree_on_p_tau_r_s",
                                                "expected_match", "literal_checks_ok")}
                             for r in rows],
                "wall_s": payload["wall_s"]}
        print(json.dumps(slim, indent=1, default=str))
    return payload


# ---------------------------------------------------------------- generators (stage 2)
def cone(base_edges, apex):
    """Cone over a base graph: base edges RED, apex spokes BLUE. A triangle-free base
    keeps every red edge globally private (s=0); odd cycles give tau/p=(k+1)/(k-1)."""
    ed, rd = set(base_edges), set(base_edges)
    for (u, v) in list(base_edges):
        for w in (u, v):
            if w != apex:
                ed.add(norm((w, apex)))
    return ed, ed & rd


def seed_cone_cycle(k, n, apex=None):
    """C_k red base + blue apex (odd k gives tau/p = (k+1)/2 / ((k-1)/2))."""
    vs = list(range(k))
    base = [(vs[i], vs[(i + 1) % k]) for i in range(k)]
    ap = k if apex is None else apex
    return cone(base, ap, n)


def seed_cone_graph(base_edges, apex, n):
    return cone(base_edges, apex)


def odd_cycle(k):
    return [norm((i, (i + 1) % k)) for i in range(k)]


def use_all_vertices(n, ed, rd, rng):
    """attach every still-isolated vertex with one of the two structural pages, so the
    seed actually spans H (isolated vertices only produce 'disconnected' rejections):
      page_on_red  : join a new vertex to a RED edge with two BLUE spokes -> that red
                     edge becomes multipage (s grows), the triangle is non-private;
      page_on_blue : join a new vertex to a BLUE edge and colour ONE new spoke red ->
                     a fresh globally private red edge (premise-friendly growth)."""
    used = {v for e in ed for v in e}
    for v in range(n):
        if v in used:
            continue
        reds, blues = sorted(rd), sorted(e for e in ed if e not in rd)
        if reds and (not blues or rng.random() < 0.5):
            a, b = rng.choice(reds)
            ed |= {norm((v, a)), norm((v, b))}
        elif blues:
            a, b = rng.choice(blues)
            ed |= {norm((v, a)), norm((v, b))}
            rd.add(norm((v, a)) if rng.random() < 0.5 else norm((v, b)))
        else:
            return None
        used |= {v}
    return ed, ed & rd


def seed_cone_cycle(n, rng, want=None):
    """C_k RED base (k odd) + BLUE apex: p = (k-1)/2, tau = (k+1)/2, all red private."""
    ks = [k for k in (3, 5, 7, 9, 11) if k <= n - 1]
    if not ks:
        return None
    k = want if want in ks else rng.choice(ks[-2:])
    return use_all_vertices(n, *cone(odd_cycle(k), k), rng)


def seed_two_cones_linked(n, rng):
    """two odd-cycle red cones on disjoint bases joined by a triangle-free bridge
    (matching or 2-regular shift). Needs k1+k2+2 <= n."""
    opts = [(a, b) for a in (3, 5, 7) for b in (3, 5, 7) if a + b + 2 <= n]
    if not opts:
        return None
    k1, k2 = rng.choice(opts[-2:] if len(opts) > 1 else opts)
    b1 = odd_cycle(k1)
    off = k1 + 1
    b2 = [norm((off + i, off + (i + 1) % k2)) for i in range(k2)]
    a1, a2 = k1, off + k2
    ed, rd = set(), set()
    for base, ap in ((b1, a1), (b2, a2)):
        e, r = cone(base, ap)
        ed |= e
        rd |= r
    for i in range(rng.randint(1, min(k1, k2))):        # triangle-free bridge
        u = rng.randrange(k1)
        v = off + rng.randrange(k2)
        if rng.random() < 0.5:
            v = off + (2 * i) % k2
        ed.add(norm((u, v)))
    return use_all_vertices(n, ed, ed & rd, rng)


def seed_book(n, rng, red_where="pages"):
    """a book: base vertex 0, t spines, m pages each. red_where='spines' makes the spine
    edge multipage (s>0, premise usually fails); 'pages' keeps red edges private."""
    t = rng.randint(1, 3)
    m = rng.randint(1, 3)
    ed, rd = set(), set()
    nxt = 1
    for _ in range(t):
        if nxt >= n:
            break
        sp = nxt
        nxt += 1
        ed.add(norm((0, sp)))
        if red_where == "spines":
            rd.add(norm((0, sp)))
        for _ in range(m):
            if nxt >= n:
                break
            v = nxt
            nxt += 1
            ed |= {norm((0, v)), norm((sp, v))}
            if red_where == "pages":
                rd.add(norm((sp, v)))
    if not rd:
        return None
    return use_all_vertices(n, ed, ed & rd, rng)


def mutate(n, ed, rd, rng):
    """one structural mutation of a valid parent; intermediate states may violate a
    premise and are then rejected and logged (that relaxation is the point)."""
    ed, rd = set(ed), set(rd)
    pl = list(itertools.combinations(range(n), 2))
    op = rng.choice(["flip_presence", "recolor", "add_page_on_red", "add_private_tri",
                     "drop_edge", "add_bridge"])
    if op == "flip_presence":
        e = rng.choice(pl)
        if e in ed:
            ed.discard(e)
            rd.discard(e)
        else:
            ed.add(e)
    elif op == "recolor":
        if not ed:
            return None
        e = rng.choice(sorted(ed))
        if e in rd:
            rd.discard(e)
        else:
            rd.add(e)
    elif op == "add_page_on_red":
        if not rd:
            return None
        e = rng.choice(sorted(rd))
        a, b = e
        cands = [v for v in range(n) if v not in (a, b)]
        rng.shuffle(cands)
        for v in cands:
            if norm((a, v)) in ed and norm((b, v)) in ed:
                continue
            ed |= {norm((a, v)), norm((b, v))}
            break
        else:
            return None
    elif op == "add_private_tri":
        blue = [x for x in ed if x not in rd]
        if not blue:
            return None
        e = rng.choice(sorted(blue))          # grow a triangle on an existing BLUE edge
        a, b = e
        cands = [v for v in range(n) if v not in (a, b) and norm((a, v)) not in ed
                 and norm((b, v)) not in ed]
        if not cands:
            return None
        v = rng.choice(cands)
        ed |= {norm((a, v)), norm((b, v))}
        rd.add(norm((a, v)) if rng.random() < 0.5 else norm((b, v)))
    elif op == "drop_edge":
        if not ed:
            return None
        e = rng.choice(sorted(ed))
        ed.discard(e)
        rd.discard(e)
    else:                                    # add_bridge: triangle-free by construction
        if n < 4:
            return None
        for _ in range(20):
            u, v = rng.sample(range(n), 2)
            e = (min(u, v), max(u, v))
            if e in ed:
                continue
            if any((min(u, w), max(u, w)) in ed and (min(v, w), max(v, w)) in ed
                   for w in range(n)):
                continue
            ed.add(e)
            if rng.random() < 0.35:
                rd.add(e)
            break
        else:
            return None
    return ed, rd


SEEDS = [("cone_odd_cycle", lambda n, rng: seed_cone_cycle(n, rng)),
         ("cone_C5", lambda n, rng: seed_cone_cycle(n, rng, want=5)),
         ("cone_C7", lambda n, rng: seed_cone_cycle(n, rng, want=7)),
         ("cone_C3", lambda n, rng: seed_cone_cycle(n, rng, want=3)),
         ("two_cones_linked", lambda n, rng: seed_two_cones_linked(n, rng)),
         ("book_pages_red", lambda n, rng: seed_book(n, rng, "pages")),
         ("book_spines_red", lambda n, rng: seed_book(n, rng, "spines")),
         # coordinator's s>0 control, reused as a STRUCTURAL SEED for stage 2 (n >= 9):
         ("spine8_c4_plus_path", lambda n, rng: use_all_vertices(n, set(SP8_ED),
                                                                 set(SP8_RD), rng)
          if n >= 9 else None)]


def run_full(out_prefix, seed=20261003, verbose=True, out_name="instances.json"):
    """Stage-2 HARD-INSTANCE DIAGNOSTIC (retargeted after round-11 C, citing Role E).
    Maximise tau/p among ELIGIBLE instances with s > 0 at n = 6..12. A strict RB(1/100)
    counterexample cannot occur at these orders: with an all-private maximum packing Q,
    tau <= 2p - 1 forces p > 100, while n <= 12 has at most C(12,2)=66 edges and 3p
    distinct edges are needed for p edge-disjoint triangles, i.e. p <= 22. The witness
    test is therefore kept ONLY as a solver bug alarm (it must never fire). NOT run yet."""
    T0[0] = time.time()
    rng = random.Random(seed)
    st = {"attempts": 0, "unique": 0, "repeats": 0, "eligible": 0, "uncertified_skips": 0,
          "engine_b_not_certified": 0, "gen_unusable": 0, "parent_mutations": 0,
          "premise_rejects": {}, "uncertified_reasons": {},
          "per_n": {str(n): {"attempts": 0, "eligible": 0, "quota": ELIG_PER_N[n]}
                    for n in NS},
          "hist_tau_over_p": {}, "hist_s": {}, "hist_max_red_pages": {},
          "stop": "", "disagreements": [], "witness_alarm": []}
    seen = {}
    pool = {"s0": [], "sp": []}

    def alive_orders():
        return [x for x in NS if st["per_n"][str(x)]["eligible"] < ELIG_PER_N[x]]

    try:
        while st["attempts"] < MAX_ATTEMPTS and st["eligible"] < MAX_ELIGIBLE:
            check_deadline()                        # bounded before ANY solve
            alive = alive_orders()
            if not alive:                           # no `or NS` fallback
                st["stop"] = ("per-n eligible quotas saturated; global cap "
                              f"{MAX_ELIGIBLE} NOT reached, so no order was oversampled")
                break
            parents = [p for p in pool["sp"] + pool["s0"] if p["n"] in alive]
            if parents and rng.random() < 0.6:      # mutate an ELIGIBLE parent
                par = rng.choice(parents)
                n = par["n"]                        # n decided BEFORE any mutation
                _, ed, rd = VW.decode(n, par["colorstring"])
                kmax = rng.randint(1, 3)
                st["parent_mutations"] += 1
                nm = "mutant_of_" + str(par.get("seed_family", "?"))
            else:                                   # fresh structured seed
                n = rng.choice(alive)
                cands = list(SEEDS)
                rng.shuffle(cands)
                for f, g in cands:                  # take the first family that fits n
                    got = g(n, rng)
                    if got is not None:
                        nm, (ed, rd) = f, got
                        break
                else:
                    st["gen_unusable"] += 1
                    continue
                kmax = rng.randint(0, 4)
            for _ in range(kmax):                   # relaxed intermediate states allowed
                m = mutate(n, ed, rd, rng)
                if m is not None:
                    ed, rd = m
            st["attempts"] += 1
            st["per_n"][str(n)]["attempts"] += 1
            cs = colorstring(n, ed, rd)
            if cs in seen:
                st["repeats"] += 1
                seen[cs] += 1
                continue
            seen[cs] = 1
            st["unique"] += 1
            a, reason = engine_a(n, ed, rd)
            if a is None:
                if reason in UNCERTIFIED:           # NOT a premise rejection
                    st["uncertified_skips"] += 1
                    st["uncertified_reasons"][reason] = st["uncertified_reasons"].get(
                        reason, 0) + 1
                else:
                    st["premise_rejects"][reason] = st["premise_rejects"].get(reason, 0) + 1
                continue
            b = engine_b(n, cs, {"p": a["p"], "p_private": a["p_private"],
                                 "tau": a["tau"], "r": a["r"], "s": a["s"]})
            if not b["certified"]:                  # ILP hit its time limit / brute skipped
                st["engine_b_not_certified"] += 1
                st["uncertified_reasons"]["engine_b_not_certified"] = st[
                    "uncertified_reasons"].get("engine_b_not_certified", 0) + 1
                continue
            pages_a = sorted((int(x[0]), int(x[1]), int(x[2])) for x in a["nonprivate_red"])
            pages_b = sorted((int(p[0][0]), int(p[0][1]), int(p[1]))
                             for p in b["nonprivate_red_edges"])
            if not (b["eligible"] and b["p_private"] == a["p_private"] and
                    all(b["literal_checks"].values()) and
                    b["triangle_constraints"]["every_triangle_exactly_one_red"] and
                    not b["claim_mismatches"] and pages_a == pages_b):
                st["disagreements"].append({"n": n, "colorstring": cs,
                                            "mismatch": b["claim_mismatches"],
                                            "b_eligible": b["eligible"],
                                            "p_private": [a["p_private"], b["p_private"]],
                                            "failed_checks": [k for k, v in
                                                              b["literal_checks"].items()
                                                              if not v],
                                            "pages_a_vs_b": [pages_a, pages_b]})
                continue
            st["eligible"] += 1
            st["per_n"][str(n)]["eligible"] += 1    # quota charged on the FINAL n
            max_pages = max([x[2] for x in pages_a], default=1)
            rec = {"name": f"{nm}_n{n}_{st['eligible']}", "seed_family": nm, "n": n,
                   "colorstring": cs, "p": a["p"], "p_private": a["p_private"],
                   "tau": a["tau"], "r": a["r"], "s": a["s"],
                   "nonprivate_red_page_counts": pages_a, "max_red_pages": max_pages,
                   "tau_over_p": a["tau"] / a["p"],
                   "ceiling_tau_le_2p_minus_1_from_role_E": 2 * a["p"] - 1,
                   "gap_to_that_ceiling": (2 * a["p"] - 1) - a["tau"],
                   "margin_100tau_minus_199p": 100 * a["tau"] - 199 * a["p"],
                   "edge_cover_certificate": a["edge_cover_certificate"],
                   "packing_Q_certificates": a["packing_Q_certificates"],
                   "checks": b["literal_checks"],
                   "engine_b_certified": b["certified"], "engine_b_eligible": b["eligible"],
                   "methods": b["methods"],
                   "verifier_cmd": f"python verify_witness.py --n {n} --colorstring {cs}"}
            st["hist_tau_over_p"][f"{a['tau']}/{a['p']}"] = st["hist_tau_over_p"].get(
                f"{a['tau']}/{a['p']}", 0) + 1
            st["hist_s"][str(a["s"] > 0)] = st["hist_s"].get(str(a["s"] > 0), 0) + 1
            st["hist_max_red_pages"][str(max_pages)] = st["hist_max_red_pages"].get(
                str(max_pages), 0) + 1
            key = "sp" if a["s"] > 0 else "s0"
            pool[key].append(rec)
            pool[key].sort(key=lambda x: (-x["tau_over_p"], x["p"]))
            del pool[key][40:]
            if rec["margin_100tau_minus_199p"] > 0:      # BUG ALARM, not a witness claim
                st["witness_alarm"].append({
                    "n": n, "colorstring": cs, "p": a["p"], "tau": a["tau"],
                    "note": "tau > 1.99p observed at n <= 12 although tau <= 2p-1 with "
                            "p <= 22 makes this impossible; suspect a solver/record bug "
                            "and re-verify. NOT reported as an RB(1/100) witness."})
    except Over:
        st["stop"] = st["stop"] or "deadline/self-limit hit; PARTIAL search"
    st["stop"] = st["stop"] or "attempt cap or global eligible cap reached"
    best = {"s0": pool["s0"][:3], "sp": pool["sp"][:3]}
    payload = {"stage": 2, "mode": "full", "seed": seed,
               "objective": "hard-instance diagnostic: eligible instances with s>0 and the "
                            "largest tau/p found (target > 1.5); NOT a search for an "
                            "RB(1/100) witness, which cannot exist at n<=12",
               "why_small_orders_cannot_refute_RB_1_100":
                   "Role E (round 11, C-approved): an H whose every triangle has exactly "
                   "one red edge and which has an all-private maximum packing Q satisfies "
                   "tau <= 2p - 1. A strict counterexample needs 1.99p < 2p - 1, i.e. "
                   "p > 100. At n <= 12, p <= floor(C(12,2)/3) = 22 because p "
                   "edge-disjoint triangles use 3p distinct edges. So no n <= 12 instance "
                   "can witness tau > 199p/100; the retained examples only carry "
                   "diagnostic value for how high tau/p climbs with s > 0.",
               "budgets": {"configured_wall_s": WALL_S, "self_limit_s": SELF_LIMIT_S,
                           "write_deadline_s": WRITE_DEADLINE_S,
                           "solve_slack_s": SOLVE_SLACK_S,
                           "max_attempts": MAX_ATTEMPTS, "max_eligible": MAX_ELIGIBLE,
                           "per_n_eligible_quota": {str(k): v for k, v in ELIG_PER_N.items()},
                           "engine_A_node_cap": NODE_CAP, "engine_B_brute_cap": BRUTE_CAP,
                           "engine_B_ilp_time_limit": "remaining wall before write deadline, "
                                                      "reset before every solve"},
               "stats": st, "best_by_stratum": best,
               "repeat_counts_top": sorted(seen.items(), key=lambda kv: -kv[1])[:20],
               "witness_alarm_count": len(st["witness_alarm"]),
               "retained": {"s_equals_0": pool["s0"], "s_positive": pool["sp"]},
               "controls_are_not_counted_here": True,
               "wall_s": round(elapsed(), 3),
               "disclaimer": "bounded search over the listed seed families; no theorem, "
                             "no universal constant, no RB(1/100) witness claimed"}
    try:
        check_write_slot()                          # bounded before ANY write
        out_prefix.mkdir(parents=True, exist_ok=True)
        (out_prefix / out_name).write_text(json.dumps(payload, indent=1, default=str),
                                           encoding="utf-8")
        payload["artifact_written"] = str(out_prefix / out_name)
    except WriteMissed:
        payload["artifact_written"] = None
        st["stop"] += "; WRITE SKIPPED (past write deadline), summary printed only"
    if verbose:
        print(json.dumps({"wall_s": payload["wall_s"], "artifact_written":
                          payload["artifact_written"], "objective": payload["objective"],
                          "best_by_stratum": best, "stats": st}, indent=1, default=str))
    return payload


# ---------------------------------------------------------------- CLI
def main(argv=None):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("controls")
    c.add_argument("--out", default=str(HERE))
    c.add_argument("--private-log", default=str(PRIVATE / "stage1_log.json"))
    f = sub.add_parser("full")
    f.add_argument("--out", default=str(HERE))
    f.add_argument("--seed", type=int, default=20261003)
    f.add_argument("--smoke", action="store_true")
    v = sub.add_parser("verify")
    v.add_argument("n", type=int)
    v.add_argument("colorstring")
    a = ap.parse_args(argv)
    if a.cmd == "controls":
        p = run_controls(Path(a.out))
        PRIVATE.mkdir(parents=True, exist_ok=True)
        Path(a.private_log).write_text(json.dumps(p, indent=1, default=str), encoding="utf-8")
        return 0 if p["all_controls_pass"] else 1
    if a.cmd == "full":
        if a.smoke:
            global MAX_ATTEMPTS, MAX_ELIGIBLE
            MAX_ATTEMPTS, MAX_ELIGIBLE = 20, 3
            ELIG_PER_N.update({n: 1 for n in NS})
            run_full(PRIVATE, verbose=True, out_name="smoke_instances.json")
            return 0
        run_full(Path(a.out))
        return 0
    ed = {e for e, ch in zip(itertools.combinations(range(a.n), 2), a.colorstring)
          if ch in "BR"}
    rd = {e for e, ch in zip(itertools.combinations(range(a.n), 2), a.colorstring)
          if ch == "R"}
    aa, reason = engine_a(a.n, ed, rd)
    bb = engine_b(a.n, a.colorstring)
    print(json.dumps({"engine_a_audited_round10": {"eligible": aa is not None,
                                                   "reject": reason,
                                                   "quantities": None if aa is None else
                                                   {k: aa[k] for k in ("p", "p_private",
                                                                        "tau", "r", "s")}},
                      "engine_b_standalone": {k: bb[k] for k in ("p", "p_private", "tau",
                                                                 "r", "s", "eligible",
                                                                 "certified",
                                                                 "literal_checks",
                                                                 "premises")}}, indent=1))
    return 0 if bb["certified"] else 2


if __name__ == "__main__":
    sys.exit(main())
