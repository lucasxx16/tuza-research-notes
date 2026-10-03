"""Bounded COUPLED MILP: P3-center diagnostic, single 11-vertex graph G.

MISTAKE GUARDS (previous run):
  * HUBS = {0,1}. The core {2,3,4,5} is NOT the hub pair.
  * Triangles are enumerated as VERTEX triples (3 distinct vertices), never as
    edge tuples standing in for vertices; edges are READ OFF afterwards.
  * Positive certificate = an exactly checked (S, X). Timeout / status alone proves nothing.
"""
import itertools, json, os
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

HUBS, CORE, AS, BS = {0, 1}, {2, 3, 4, 5}, {6, 7}, {8, 9, 10}
V = tuple(range(11))

E = set()                                   # literal edge set (frozensets of 2 vertices)
def add(u, v): E.add(frozenset((u, v)))
add(0, 1)
for c in CORE: add(0, c); add(1, c)         # both hubs joined to the core
for a in AS: add(0, a)                      # 0 - A
for b in BS: add(1, b)                      # 1 - B
for u, v in itertools.combinations(CORE, 2): add(u, v)   # core complete
for c in CORE:
    for a in AS: add(c, a)                  # core - A complete
add(6, 7)                                   # A complete
for c in CORE:
    for b in BS: add(c, b)                  # core - B complete
for u, v in itertools.combinations(BS, 2): add(u, v)     # B complete

def edge(u, v): return frozenset((u, v))
deg = {v: sum(1 for e in E if v in e) for v in V}
assert deg[0] == 7 and deg[1] == 8, deg      # stated degrees u0=7, v1=8

ALL_TRIS = [t for t in itertools.combinations(V, 3)
            if edge(t[0], t[1]) in E and edge(t[0], t[2]) in E and edge(t[1], t[2]) in E]
ALLOWED = [t for t in ALL_TRIS if not (set(t) & BS)]        # S avoids B: vertices 0..7
HUB_TRIS = [t for t in ALL_TRIS if set(t) & HUBS]           # triangles touching HUBS

EL = sorted(E, key=lambda e: tuple(sorted(e)))
EI = {e: i for i, e in enumerate(EL)}
AL = sorted(ALLOWED)
SI = {t: i for i, t in enumerate(AL)}
NS, NX = len(AL), len(EL)
N = NS + NX

def interior(t):                              # edges of t with BOTH endpoints outside HUBS
    return [p for p in itertools.combinations(t, 2) if not (set(p) & HUBS)]

rows = []
for e in EL:                                  # (1) each graph edge in <=1 selected triangle
    co = {SI[t]: 1.0 for t in AL if e <= set(t)}
    if co: rows.append((0.0, 1.0, co))
for t in HUB_TRIS:                            # (2) every hub-touching triangle hits X
    rows.append((1.0, np.inf, {NS + EI[edge(*p)]: 1.0 for p in itertools.combinations(t, 2)}))
for t in AL:                                  # (3) boundary safety: x_e >= s_t
    for p in interior(t):
        rows.append((0.0, np.inf, {NS + EI[edge(*p)]: 1.0, SI[t]: -1.0}))
rows.append((-np.inf, 0.0, {NS + EI[e]: 1.0 for e in EL}
                      | {SI[t]: -2.0 for t in AL}))            # (4) |X| <= 2|S|
for b in BS:                                  # (5) forced spokes 1-b in X
    rows.append((1.0, 1.0, {NS + EI[edge(1, b)]: 1.0}))

A = np.zeros((len(rows), N)); bl = np.zeros(len(rows)); bu = np.zeros(len(rows))
for i, (lo, hi, co) in enumerate(rows):
    for j, v in co.items(): A[i, j] = v
    bl[i], bu[i] = lo, hi
c = np.zeros(N); c[:NS] = -2.0; c[NS:] = 1.0   # min |X| - 2|S|  (maximize budget slack)

res = milp(c=c, integrality=np.ones(N), bounds=Bounds(np.zeros(N), np.ones(N)),
           constraints=LinearConstraint(A, bl, bu), options={"time_limit": 60})

def verify(S, X):
    P = []
    k = lambda ok, m: None if ok else P.append(m)
    k(all(len(set(t)) == 3 and all(edge(*p) in E for p in itertools.combinations(t, 2))
          for t in S), "S: entries are not vertex-triangles of G")
    k(all(not (set(t) & BS) for t in S), "S: a triangle uses B")
    used = [p for t in S for p in map(lambda q: frozenset(q), itertools.combinations(t, 2))]
    k(len(used) == len(set(used)) and len(used) == 3 * len(S), "S: not edge-disjoint")
    k(X <= E, "X: not a subset of E")
    for t in HUB_TRIS:
        k(any(edge(*p) in X for p in itertools.combinations(t, 2)), f"hub triangle {t} missed by X")
    for t in S:
        for p in interior(t):
            k(edge(*p) in X, f"packed interior edge {sorted(p)} missing from X")
    k(len(X) <= 2 * len(S), f"budget |X|={len(X)} > 2|S|={2*len(S)}")
    for b in BS: k(edge(1, b) in X, f"forced spoke 1-{b} missing")
    return P

got = getattr(res, "x", None) is not None
S = [AL[i] for i in range(NS) if got and res.x[i] > 0.5] if got else []
X = {EL[j] for j in range(NX) if got and res.x[NS + j] > 0.5} if got else set()
P = verify(S, X) if got else ["solver status %s (%s)" % (res.status, res.message)]
ok = got and not P

Ss = [sorted(t) for t in sorted(S)]; Xs = sorted("-".join(map(str, sorted(e))) for e in X)
os.makedirs(os.path.dirname(os.path.abspath(__file__)), exist_ok=True)
base = os.path.dirname(os.path.abspath(__file__))
witness = {"certificate": ok, "status": str(res.status), "objective": None if res.fun is None else float(res.fun),
           "S": Ss, "X": Xs, "slack_2|S|-|X|": 2 * len(Ss) - len(Xs), "verify_problems": P,
           "counts": {"E": len(EL), "triangles": len(ALL_TRIS), "allowed_no_B": NS, "hub_triangles": len(HUB_TRIS)}}
with open(os.path.join(base, "witness.json"), "w", encoding="utf-8") as f: json.dump(witness, f, indent=1)

lines = ["P3-center bounded coupled MILP  (diagnostic only, not a proof premise)",
         "HUBS=%s CORE=%s A=%s B=%s | |E|=%d |G-triangles|=%d allowed(S, no B)=%d hub-triangles=%d"
         % (sorted(HUBS), sorted(CORE), sorted(AS), sorted(BS), len(EL), len(ALL_TRIS), NS, len(HUB_TRIS)),
         "constraints: (1) edge<=1 packed tri  (2) hub-triangle hits X  (3) x_e>=s_t for e of t with both"
         " endpoints NOT in HUBS  (4) |X|<=2|S|  (5) 1-b in X for b in B",
         "milp status=%s obj=%s time_limit=60 one-call" % (res.status, res.fun),
         "VERDICT: %s" % ("POSITIVE CERTIFICATE (exact checks passed)" if ok else "NO FEASIBLE CANDIDATE under this fixed restriction"),
         "|S|=%d %s" % (len(Ss), Ss), "|X|=%d %s" % (len(Xs), Xs),
         "checks: %s" % ("all passed" if ok else P)]
rep = "\n".join(lines) + "\n"
with open(os.path.join(base, "report.txt"), "w", encoding="utf-8") as f: f.write(rep)
print(rep)
