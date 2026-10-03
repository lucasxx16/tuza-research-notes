"""Role B / round7: ONE bounded numerical candidate task on the round6/D barrier graph J.

J: K8 on {w,0,1,2,3,4,5,6} minus 01 and 35, plus independent a,b,c,t with
N(a)={0,3,4,5,6}, N(b)={0,1,2,5,6}, N(c)={0,1,2,3,4}, N(t)={1,2,3,4,5,6}.  |E|=47.

Focus ONLY on the nonadjacent LOW pair U={b,t}.  Patch = J induced on N[b] u N[t]
(both FULL endpoint neighborhoods).  Find S edge-disjoint patch triangles and
X subset of patch edges with (1) |X| <= 2|S|, (2) X meets every patch triangle
containing b or t, (3) every edge of S with both endpoints outside U is in X.
All three are hard constraints; the constant stays 2.  Nothing outside the patch
is required to be covered.  HiGHS only PROPOSES a candidate; feasibility is
decided solely by the exact integer re-check.  Infeasible/timeout = diagnostic.
"""
import itertools, json, os, time
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

CORE = ('w', '0', '1', '2', '3', '4', '5', '6')
NOUT = {'a': '03456', 'b': '01256', 'c': '01234', 't': '123456'}
V = CORE + tuple(NOUT)
MISSING = {('0', '1'), ('3', '5')}
U = frozenset(('b', 't'))


def key(x, y):
    return (x, y) if V.index(x) < V.index(y) else (y, x)


EJ = set()
for x, y in itertools.combinations(CORE, 2):
    if (x, y) not in MISSING:
        EJ.add(key(x, y))
for h, nb in NOUT.items():
    for c in nb:
        EJ.add(key(h, c))
EJ = frozenset(EJ)
deg = lambda v: sum(1 for e in EJ if v in e)
assert len(EJ) == 47 and sum(map(deg, V)) == 94
assert (deg('b'), deg('t')) == (5, 6) and key('b', 't') not in EJ   # nonadjacent low pair

PV = tuple(sorted({*U, *(v for h in U for v in NOUT[h])}, key=V.index))
EP = frozenset(e for e in EJ if e[0] in PV and e[1] in PV)
assert all(e in EP or (('b' not in e) and ('t' not in e)) for e in EJ)  # full endpoint nbhds
assert len(PV) == 9 and len(EP) == 30, (len(PV), len(EP))

edges_of = lambda t: frozenset(key(x, y) for x, y in itertools.combinations(t, 2))
TRIS = sorted(t for t in itertools.combinations(PV, 3) if edges_of(t) <= EP)
HT = [t for t in TRIS if set(t) & U]
OUTER = lambda t: {e for e in edges_of(t) if not (set(e) & U)}
HTJ = {t for t in itertools.combinations(V, 3) if edges_of(t) <= EJ and set(t) & U}
assert HTJ == set(HT), "patch hub triangles differ from J hub triangles"

EL, SL = sorted(EP), TRIS
EI, SI = {e: i for i, e in enumerate(EL)}, {t: i for i, t in enumerate(SL)}
NS, NX, N = len(SL), len(EL), len(SL) + len(EL)
rows = []
for e in EL:                                                  # (0) S edge-disjoint
    co = {SI[t]: 1.0 for t in SL if e in edges_of(t)}
    if co:
        rows.append((-np.inf, 1.0, co))
for t in HT:                                                  # (1) X hits every b/t triangle
    rows.append((1.0, np.inf, {NS + EI[e]: 1.0 for e in edges_of(t)}))
for t in SL:                                                  # (2) outer packed edge in X
    for e in OUTER(t):
        rows.append((0.0, np.inf, {NS + EI[e]: 1.0, SI[t]: -1.0}))
rows.append((-np.inf, 0.0, {NS + EI[e]: 1.0 for e in EL}      # (3) |X| <= 2|S|
             | {SI[t]: -2.0 for t in SL}))
A_ = np.zeros((len(rows), N)); bl = np.zeros(len(rows)); bu = np.zeros(len(rows))
for i, (lo, hi, co) in enumerate(rows):
    for j, v in co.items():
        A_[i, j] = v
    bl[i], bu[i] = lo, hi
c = np.zeros(N); c[:NS] = -2.0; c[NS:] = 1.0                  # min |X| - 2|S|

t0 = time.time()
res = milp(c=c, integrality=np.ones(N), bounds=Bounds(np.zeros(N), np.ones(N)),
           constraints=LinearConstraint(A_, bl, bu), options={"time_limit": 60})
wall, stat = time.time() - t0, "%s | %s" % (res.status, res.message)
got = getattr(res, "x", None) is not None
S = sorted(tuple(SL[i]) for i in range(NS) if got and res.x[i] > 0.5)
X = {EL[j] for j in range(NX) if got and res.x[NS + j] > 0.5}


def verify(S, X):
    P = []
    k = lambda ok, m: None if ok else P.append(m)
    k(X <= set(EP), "X not a subset of patch edges")
    k(len(set(S)) == len(S) and all(t in set(TRIS) for t in S), "S not distinct patch triangles")
    used = [e for t in S for e in edges_of(t)]
    k(len(used) == len(set(used)) == 3 * len(S), "S not edge-disjoint")
    k(all(edges_of(t) & X for t in HT), "some triangle containing b or t missed by X")
    k(all(OUTER(t) <= X for t in S), "packed edge outside {b,t} missing from X")
    k(len(X) <= 2 * len(S), "budget |X|=%d > 2|S|=%d" % (len(X), 2 * len(S)))
    return P


P = verify(S, X) if got else ["no candidate returned: " + stat]
ok = bool(got and not P)
base = os.path.dirname(os.path.abspath(__file__))
wit = {"status": "CANDIDATE VERIFIED" if ok else "NO VERIFIED CANDIDATE",
       "meaning": "status reflects only the exact checks below on this one instance; no proof claimed",
       "labels": {"vertex_order": list(V), "low_pair_U": ["b", "t"],
                  "N_b": list(NOUT['b']), "N_t": list(NOUT['t']),
                  "degrees": {v: deg(v) for v in V}},
       "graph_J": {"vertices": list(V), "edges": [list(e) for e in sorted(EJ, key=lambda e: (V.index(e[0]), V.index(e[1])))]},
       "patch": {"vertices": list(PV), "edges": [list(e) for e in EL],
                 "note": "J induced on N[b] u N[t]; both endpoint neighborhoods full"},
       "counts": {"patch_triangles": len(TRIS), "U_triangles": len(HT),
                  "S_vars": NS, "x_vars": NX, "rows": len(rows)},
       "model": {"objective": "min |X| - 2|S|", "budget": "|X| <= 2|S| (constant 2, inequality)",
                 "coverage": "X meets every patch triangle containing b or t",
                 "containment": "x_e >= s_T for every edge e of T with both ends outside {b,t}",
                 "packing": "each patch edge in at most one selected triangle"},
       "solver": {"calls": 1, "status": stat, "time_limit_s": 60, "wall_time_s": round(wall, 3),
                  "objective": None if res.fun is None else int(round(res.fun)),
                  "reading": "solver status alone proves nothing; only exact checks decide"},
       "S": [list(t) for t in S], "X": [list(e) for e in sorted(X, key=lambda e: (V.index(e[0]), V.index(e[1])))],
       "sizes": {"|S|": len(S), "|X|": len(X), "slack_2|S|-|X|": 2 * len(S) - len(X)},
       "exact_checks": {
           "S_triangles_exist": len(set(S)) == len(S) and all(t in set(TRIS) for t in S),
           "S_edge_disjoint": len({e for t in S for e in edges_of(t)}) == 3 * len(S),
           "X_subset_patch_edges": X <= set(EP),
           "hub_triangle_coverage": all(edges_of(t) & X for t in HT),
           "packed_outside_edges_in_X": all(OUTER(t) <= X for t in S),
           "budget": len(X) <= 2 * len(S)},
       "problems": P,
       "claims": "single restricted instance (J, patch N[b]uN[t], pair {b,t}); no theorem, no proof"}
with open(os.path.join(base, "witness.json"), "w", encoding="utf-8") as f:
    json.dump(wit, f, indent=1)
rep = "\n".join([
 "round7/B restricted instance: J (12 vertices, 47 edges), low pair U={b,t} (nonadjacent,",
 "d(b)=5, d(t)=6), patch = J[N[b] u N[t]] = 9 vertices / 30 edges; patch triangles=%d," % len(TRIS),
 "triangles containing b or t=%d (equal to the same list in all of J - asserted)." % len(HT),
 "Search: S edge-disjoint patch triangles, X subset patch edges, |X|<=2|S| (constant 2 kept),",
 "X meets every b/t triangle, every S-edge with both ends outside {b,t} lies in X. One MILP call.",
 "SOLVER STATUS (proposes only): %s, wall=%.3fs, objective=%s"
 % (res.status, wall, None if res.fun is None else int(round(res.fun))),
 "CANDIDATE: |S|=%d %s" % (len(S), sorted(S)),
 "          : |X|=%d %s | slack 2|S|-|X|=%d" % (len(X), sorted(X), 2 * len(S) - len(X)),
 "EXACT CHECKS on the rebuilt literal patch: %s"
 % ("all pass" if ok else str(P)),
 "STATUS: %s. No proof, no theorem, no claim beyond this instance and this search."
 % ("verified candidate" if ok else "no verified candidate ; solver status alone proves nothing")]
 ) + "\n"
with open(os.path.join(base, "report.txt"), "w", encoding="utf-8") as f:
    f.write(rep)
print(rep)
