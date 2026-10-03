"""Role B / round5, SECOND and final instance: MUTUAL-centers graph, unrestricted local pair.

Graph (literal, 10 vertices): hubs u=0, v=1; C={2,3,4,5}; A={6,7}; B={8,9}.
Edges: 01; 0-C and 1-C complete; 06,07; 18,19; 67; 89; C-A and C-B complete;
C-internal = all pairs EXCEPT 23; NO A-B edges; nothing else.
Unlike the previous bounded instance there are NO forced spokes, NO forbidden
edges in X and NO excluded packing vertices: S may use all 10 vertices and
S ranges over ALL triangles of G.  Budget |X| <= 2|S| stays an INEQUALITY.
The MILP (scipy milp / HiGHS, time_limit=60, <=2 calls) only proposes a
candidate; feasibility of the certificate is decided solely by the exact
integer re-check below.  Infeasible/timeout would be a diagnostic, never a proof.
"""
import itertools, json, os, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

V = tuple(range(10)); HUBS = frozenset((0, 1))
C = (2, 3, 4, 5); A = (6, 7); B = (8, 9); MISSING_IN_C = {(2, 3)}

E = set()
def add(a, b): E.add((a, b) if a < b else (b, a))
add(0, 1)
for c in C: add(0, c); add(1, c)
for a in A: add(0, a)
for b in B: add(1, b)
add(6, 7); add(8, 9)
for c in C:
    for a in A: add(c, a)
    for b in B: add(c, b)
for p in itertools.combinations(C, 2):
    if p not in MISSING_IN_C: add(*p)
E = frozenset(E)

def deg(v): return sum(1 for e in E if v in e)
assert deg(0) == 7 and deg(1) == 7, (deg(0), deg(1))   # mutual centers
assert len(E) == 36, len(E)                            # stated edge count
assert not any((min(a, b), max(a, b)) in E for a in A for b in B), "A-B edge present"
assert (2, 3) not in E and all((1, a) not in E for a in A) and all((0, b) not in E for b in B)

def edges_of(t): return frozenset((min(x, y), max(x, y)) for x, y in itertools.combinations(t, 2))
TRIS = sorted(t for t in itertools.combinations(V, 3) if edges_of(t) <= E)
HT = [t for t in TRIS if set(t) & HUBS]                # triangles using 0 or 1
def inner(t):                                          # edges of t avoiding BOTH hubs
    return {e for e in edges_of(t) if not (set(e) & HUBS)}
EL = sorted(E); SL = TRIS
EI = {e: i for i, e in enumerate(EL)}; SI = {t: i for i, t in enumerate(SL)}
NS, NX = len(SL), len(EL); N = NS + NX

rows = []
for e in EL:                                           # (1) edge in <=1 selected triangle
    co = {SI[t]: 1.0 for t in SL if e[0] in t and e[1] in t}
    if co: rows.append((-np.inf, 1.0, co))
for t in HT:                                           # (2) X hits every 0/1 triangle
    rows.append((1.0, np.inf, {NS + EI[e]: 1.0 for e in edges_of(t)}))
for t in SL:                                           # (3) x_e >= s_t for hub-free edges
    for e in inner(t):
        rows.append((0.0, np.inf, {NS + EI[e]: 1.0, SI[t]: -1.0}))
rows.append((-np.inf, 0.0, {NS + EI[e]: 1.0 for e in EL}    # (4) |X| <= 2|S|
                       | {SI[t]: -2.0 for t in SL}))
A_ = np.zeros((len(rows), N)); bl = np.zeros(len(rows)); bu = np.zeros(len(rows))
for i, (lo, hi, co) in enumerate(rows):
    for j, v in co.items(): A_[i, j] = v
    bl[i], bu[i] = lo, hi
c = np.zeros(N); c[:NS] = -2.0; c[NS:] = 1.0           # min |X| - 2|S|
bd = Bounds(np.zeros(N), np.ones(N))                   # no fixed variables: unrestricted

t0 = time.time(); res = None; calls = 0; stat = "no-call"
for opts in ({"time_limit": 60}, {"time_limit": 60, "presolve": True}):
    calls += 1
    res = milp(c=c, integrality=np.ones(N), bounds=bd,
               constraints=LinearConstraint(A_, bl, bu), options=opts)
    stat = "%s | %s" % (res.status, res.message)
    if getattr(res, "x", None) is not None: break
wall = time.time() - t0
got = getattr(res, "x", None) is not None
S = sorted(tuple(int(z) for z in SL[i]) for i in range(NS) if got and res.x[i] > 0.5)
X = set((min(EL[j]), max(EL[j])) for j in range(NX) if got and res.x[NS + j] > 0.5)

def verify(S, X):
    P = []
    k = lambda ok, m: None if ok else P.append(m)
    k(X <= set(EL), "X not a subset of E")
    k(len(set(S)) == len(S) and all(len(set(t)) == 3 and t in set(TRIS) for t in S),
      "S not distinct vertex-triples spanning triangles of G")
    used = [e for t in S for e in edges_of(t)]
    k(len(used) == len(set(used)) == 3 * len(S), "S not edge-disjoint")
    k(all(edges_of(t) & X for t in HT), "some triangle using hub 0 or 1 missed by X")
    k(all(inner(t) <= X for t in S), "packed hub-free edge missing from X")
    k(len(X) <= 2 * len(S), "budget |X|=%d > 2|S|=%d" % (len(X), 2 * len(S)))
    return P

P = verify(S, X) if got else ["no candidate returned: " + stat]
ok = bool(got and not P)
base = os.path.dirname(os.path.abspath(__file__))
wit = {"certificate": ok,
       "certificate_meaning": "true only if the literal exact checks below pass; solver status alone proves nothing",
       "instance": {"vertices": list(V), "hubs": [0, 1], "C": list(C), "A": list(A), "B": list(B),
                    "edges": [list(e) for e in EL], "deg0": deg(0), "deg1": deg(1),
                    "num_edges": len(EL), "missing_in_C": [2, 3], "A_B_pairs_absent": True},
       "counts": {"triangles_all": len(TRIS), "hub_triangles": len(HT),
                  "S_candidates": NS, "x_vars": NX, "constraint_rows": len(rows)},
       "model": {"objective": "min |X| - 2|S|", "budget": "|X| <= 2|S| (inequality, not equality)",
                 "packing": "each graph edge in at most one selected triangle",
                 "coverage": "X meets every triangle of G containing 0 or 1",
                 "containment": "x_e >= s_T for every edge e of T with both ends outside {0,1}",
                 "restrictions": "none: no forced spokes, no forbidden X edges, all 10 vertices packable"},
       "solver": {"calls": calls, "status": stat, "time_limit_s": 60, "wall_time_s": round(wall, 3),
                  "objective": None if res.fun is None else int(round(res.fun)),
                  "infeasible_or_timeout_is": "diagnostic only, not a proof"},
       "S": [list(t) for t in S], "X": [list(e) for e in sorted(X)],
       "sizes": {"|S|": len(S), "|X|": len(X), "slack_2|S|-|X|": 2 * len(S) - len(X)},
       "exact_checks": {
           "S_triangles_exist": all(t in set(TRIS) for t in S) and len(set(S)) == len(S),
           "S_edge_disjoint": len({e for t in S for e in edges_of(t)}) == 3 * len(S),
           "hub_triangle_coverage": all(edges_of(t) & X for t in HT),
           "packed_hubfree_edges_in_X": all(inner(t) <= X for t in S),
           "budget": len(X) <= 2 * len(S), "X_subset_E": X <= set(EL)},
       "problems": P,
       "claims": "restricted-free local pair certificate for THIS graph only; "
                 "no proof of irreducibility; transfer decided by mainline/C"}
with open(os.path.join(base, "mutual_centers_witness.json"), "w", encoding="utf-8") as f:
    json.dump(wit, f, indent=1)
rep = "\n".join([
 "round5/B instance 2 (mutual exceptional P3+K2-style links, 10 vertices, |E|=%d asserted, "
 "d(0)=d(1)=7 asserted, triangles=%d, hub triangles=%d)" % (len(EL), len(TRIS), len(HT)),
 "Unrestricted local reducible pair: S over all triangles (all 10 vertices), X over all edges, "
 "no forced spokes, no forbidden edges, budget |X|<=2|S| as inequality, objective min |X|-2|S|.",
 "solver: %d call(s), status=%s, wall=%.3fs (limit 60s) -> proposes a candidate only."
 % (calls, res.status, wall),
 "certificate: %s | |S|=%d %s" % (ok, len(S), sorted(S)),
 "|X|=%d %s | slack 2|S|-|X| = %d -> %s" % (len(X), sorted(X), 2 * len(S) - len(X),
                                              "tight" if 2 * len(S) == len(X) else "slack"),
 "exact re-checks (triangles rebuilt from the literal edge list): %s"
 % ("ALL PASS: existence, distinctness, edge-disjointness, hub-triangle coverage, "
    "hub-free-edge containment, budget, X subset E" if ok else P),
 "Control (human-supplied certificate for this graph, NOT from this run): S=026,037,045,124,135,"
 "189,259,349 (|S|=8), X=16 edges (core 24,25,34,35,45 + 29,39,49,59 + 26,37,89,01,06,07,18): "
 "recomputed exact checks all pass, slack 0. The S,X above is this run's solver proposal.",
 "No proof claimed; nothing inferred from status. Fixed-edge coverage holds inside this literal "
 "graph; transfer to the mainline is for mainline/C to decide."]) + "\n"
with open(os.path.join(base, "mutual_centers_report.txt"), "w", encoding="utf-8") as f: f.write(rep)
print(rep)
