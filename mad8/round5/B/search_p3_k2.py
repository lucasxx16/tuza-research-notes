"""Role B / round5: ONE fixed 10-vertex instance, coupled MILP (scipy milp / HiGHS).

Graph is NOT the round3 P3-center graph. Vertices 0..9, hubs {0,1}, C={2..6},
w=7, B={8,9}. Budget |X| <= 2|S| is an INEQUALITY (never an equality).
The solver only proposes a candidate: every claim about (S, X) is recomputed
with exact integer set logic from the literal edge list below.
No proof is claimed from a solver status, and no unrestricted irreducibility
statement is made (restrictions: S avoids {8,9}; X forced to contain 18,19 and
to avoid every other edge incident to 8 or 9).
"""
import itertools, json, os, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

V = tuple(range(10)); HUBS = frozenset((0, 1)); C = (2, 3, 4, 5, 6); W = 7; B = (8, 9)
MISSING_IN_C = {(2, 3), (3, 4)}                      # C is NOT complete
FORBIDDEN = [(1, 7), (0, 8), (0, 9), (7, 8), (7, 9)]

E = set()
def add(a, b): E.add((a, b) if a < b else (b, a))
add(0, 1)
for c in C: add(0, c); add(1, c)
add(0, W); add(1, 8); add(1, 9)
for a, b in itertools.combinations(C, 2):
    if (a, b) not in MISSING_IN_C: add(a, b)
for c in C: add(W, c)
for b in B:
    for c in C: add(b, c)
add(8, 9)

def deg(v): return sum(1 for e in E if v in e)
assert deg(0) == 7 and deg(1) == 8, (deg(0), deg(1))
N0 = sorted({b for e in E if 0 in e for b in e if b != 0})   # neighbours of hub 0
lk0c = sorted(p if p[0] < p[1] else p[::-1] for p in itertools.combinations(N0, 2)
              if p not in E)
assert lk0c == [(1, 7), (2, 3), (3, 4)], lk0c        # complement of link(0)
assert not any(p in E for p in FORBIDDEN), "extra edge present"

def tri(vs):
    return [t for t in itertools.combinations(vs, 3)
            if all((min(x, y), max(x, y)) in E for x, y in itertools.combinations(t, 2))]
ALL_TRIS = tri(V)                 # ambient triangles of G
SL = sorted(tri(range(8)))        # S candidates: vertex triples entirely in 0..7
HT = [t for t in ALL_TRIS if set(t) & HUBS]           # hub triangles X must hit
EL = sorted(E)
EI = {e: i for i, e in enumerate(EL)}; SI = {t: i for i, t in enumerate(SL)}
NS, NX = len(SL), len(EL); N = NS + NX
def inner(t):                                       # edges of t avoiding both hubs
    return [(min(x, y), max(x, y)) for x, y in itertools.combinations(t, 2)
            if not ({x, y} & HUBS)]

rows = []
for e in EL:                                          # (1) edge in <=1 selected triangle
    co = {SI[t]: 1.0 for t in SL if e[0] in t and e[1] in t}
    if co: rows.append((-np.inf, 1.0, co))
for t in HT:                                          # (2) X meets every hub triangle
    rows.append((1.0, np.inf, {NS + EI[(min(x, y), max(x, y))]: 1.0
                               for x, y in itertools.combinations(t, 2)}))
for t in SL:                                          # (3) x_e >= s_t for hub-free edges
    for e in inner(t):
        rows.append((0.0, np.inf, {NS + EI[e]: 1.0, SI[t]: -1.0}))
rows.append((-np.inf, 0.0, {NS + EI[e]: 1.0 for e in EL}    # (4) |X| <= 2|S|
                       | {SI[t]: -2.0 for t in SL}))
A = np.zeros((len(rows), N)); bl = np.zeros(len(rows)); bu = np.zeros(len(rows))
for i, (lo, hi, co) in enumerate(rows):
    for j, v in co.items(): A[i, j] = v
    bl[i], bu[i] = lo, hi
lb = np.zeros(N); ub = np.ones(N)
for i, e in enumerate(EL):                            # (5) 18,19 in X; other B-edges out
    if e in ((1, 8), (1, 9)): lb[NS + i] = ub[NS + i] = 1.0
    elif set(e) & set(B): ub[NS + i] = 0.0
c = np.zeros(N); c[:NS] = -2.0; c[NS:] = 1.0          # min |X| - 2|S|

t0 = time.time(); res = None; calls = 0; stat = "no-call"
for opts in ({"time_limit": 60}, {"time_limit": 60, "presolve": True}):
    calls += 1
    res = milp(c=c, integrality=np.ones(N), bounds=Bounds(lb, ub),
               constraints=LinearConstraint(A, bl, bu), options=opts)
    stat = "%s | %s" % (res.status, res.message)
    if getattr(res, "x", None) is not None: break
el_t = time.time() - t0
got = getattr(res, "x", None) is not None
S = [SL[i] for i in range(NS) if res.x[i] > 0.5] if got else []
X = {EL[j] for j in range(NX) if res.x[NS + j] > 0.5} if got else set()
S = [tuple(int(z) for z in t) for t in S]
X = {tuple(int(z) for z in e) for e in X}
ESet = set(EL); TRIset = set(ALL_TRIS)

def verify(S, X):
    P = []
    k = lambda ok, m: None if ok else P.append(m)
    k(len(set(S)) == len(S) and all(len(set(t)) == 3 and t in TRIset for t in S),
      "S not distinct ambient triangles of G")
    k(all(max(t) <= 7 for t in S), "S uses vertex 8 or 9")
    used = [(min(x, y), max(x, y)) for t in S for x, y in itertools.combinations(t, 2)]
    k(len(used) == len(set(used)) == 3 * len(S), "S not edge-disjoint")
    k(X <= ESet, "X not a subset of E")
    k(all(any((min(x, y), max(x, y)) in X for x, y in itertools.combinations(t, 2))
          for t in HT), "some hub triangle missed by X")
    k(all(e in X for t in S for e in inner(t)), "packed hub-free edge missing from X")
    k(len(X) <= 2 * len(S), "budget |X|=%d > 2|S|=%d" % (len(X), 2 * len(S)))
    k((1, 8) in X and (1, 9) in X, "forced spoke 18/19 missing")
    k(all(not (set(e) & set(B)) or e in ((1, 8), (1, 9)) for e in X),
      "X contains a forbidden edge incident to 8 or 9")
    return P

P = verify(S, X) if got else ["no candidate: " + stat]
ok = got and not P
base = os.path.dirname(os.path.abspath(__file__))
wit = {"certificate": ok, "claims": "candidate only; no proof from solver status",
       "instance": {"vertices": list(V), "hubs": [0, 1], "C": list(C), "w": W, "B": list(B),
                    "edges": [list(e) for e in EL], "deg0": deg(0), "deg1": deg(1),
                    "complement_of_link_at_0": [list(e) for e in lk0c]},
       "counts": {"edges": NX, "all_triangles": len(ALL_TRIS), "S_candidates_no_89": NS,
                  "hub_triangles": len(HT), "constraints": len(rows)},
       "model": {"objective": "min |X| - 2|S|", "budget": "|X| <= 2|S| (inequality)",
                 "forced_X": [[1, 8], [1, 9]],
                 "forbidden_X": [list(e) for e in EL if set(e) & set(B) and e not in ((1, 8), (1, 9))],
                 "S_triples_avoid": [8, 9]},
       "solver": {"calls": calls, "status": stat, "time_limit": 60,
                  "wall_time_s": round(el_t, 3),
                  "objective": None if res.fun is None else int(round(res.fun))},
       "S": [list(t) for t in sorted(S)], "X": [list(e) for e in sorted(X)],
       "sizes": {"|S|": len(S), "|X|": len(X), "slack_2|S|-|X|": 2 * len(S) - len(X)},
       "exact_checks": {"S_triangles_exist": ok or all(t in TRIset for t in S),
                        "S_edge_disjoint": len({(min(a, b), max(a, b)) for t in S for a, b in
                                                itertools.combinations(t, 2)}) == 3 * len(S),
                        "hub_triangle_coverage": all(any((min(a, b), max(a, b)) in X for a, b in
                                                        itertools.combinations(t, 2)) for t in HT),
                        "packed_edge_in_X": all(e in X for t in S for e in inner(t)),
                        "budget": len(X) <= 2 * len(S), "extra_restrictions": (1, 8) in X and
                        (1, 9) in X and all(not (set(e) & set(B)) or e in ((1, 8), (1, 9)) for e in X)},
       "problems": P, "irreducibility": "not claimed (restricted search only)"}
with open(os.path.join(base, "witness.json"), "w", encoding="utf-8") as f:
    json.dump(wit, f, indent=1)
rep = "\n".join([
 "round5/B fixed-instance coupled MILP (10 vertices, |E|=%d, hub triangles=%d)" % (NX, len(HT)),
 "objective min |X|-2|S|; budget |X|<=2|S| as inequality; S avoids {8,9}; X has 18,19 only B-edges.",
 "solver: %d call(s), status=%s, wall=%.2fs (limit 60s). Solver status alone is not an exact certificate." % (calls, res.status, el_t),
 "certificate: %s | |S|=%d %s" % (ok, len(S), sorted(S)),
 "|X|=%d %s | slack 2|S|-|X| = %d" % (len(X), sorted(X), 2 * len(S) - len(X)),
 "exact checks: existence/disjointness/hub-coverage/packed-containment/budget/restrictions -> %s"
 % ("ALL PASS" if ok else P),
 "No proof claimed; no unrestricted irreducibility claim. Mainline/C decide generalization."]) + "\n"
with open(os.path.join(base, "report.txt"), "w", encoding="utf-8") as f: f.write(rep)
print(rep)
