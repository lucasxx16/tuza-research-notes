"""Independent exact check of B2's one saved seven-vertex Wang-chain witness.

This checks only certificate.json's printed graph and chain; it does not scan graphs
or other legal choices. Uses standard-library recursion independent of B2's solver.
"""
import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
record = json.loads((ROOT / "B2" / "certificate.json").read_text(encoding="utf-8"))
chain = record["one_certified_chain"]["chain"]
literal = chain["literal"]
vertices = tuple(literal["vertices"])
edges = {tuple(sorted(e)) for e in chain["edges"]}

def te(t):
    return frozenset(tuple(sorted(e)) for e in combinations(t, 2))

def triangles(edge_set):
    return tuple(t for t in combinations(vertices, 3) if te(t) <= edge_set)

def optimum(tris, weights):
    masks = tuple(sum(1 << edge_idx[e] for e in te(t)) for t in tris)
    @lru_cache(None)
    def solve(i, used):
        if i == len(tris):
            return (0,) * len(weights[0]) if weights else (0,)
        best = solve(i + 1, used)
        if not masks[i] & used:
            cand = tuple(a + b for a, b in zip(weights[i], solve(i + 1, used | masks[i])))
            best = max(best, cand)
        return best
    return solve(0, 0)

edge_idx = {e: i for i, e in enumerate(sorted(edges))}
all_tris = triangles(edges)
P = tuple(tuple(t) for t in literal["P"])
A = tuple(tuple(t) for t in literal["A"])
Pprime = tuple(tuple(t) for t in literal["Pprime"])
Q = tuple(tuple(t) for t in literal["Q"])

def packing(ts, allowed):
    seen = set()
    for t in ts:
        assert t in allowed
        e = te(t)
        assert not seen.intersection(e)
        seen.update(e)

packing(P, all_tris)
n = optimum(all_tris, [(1,)] * len(all_tris))[0]
O = set().union(*(te(t) for t in P))
assert O == {tuple(e) for e in literal["O_edges"]}
assert len(P) == n == chain["n"] == 4

type1 = tuple(t for t in all_tris if len(te(t) & O) == 1)
packing(A, type1)
a = optimum(type1, [(1,)] * len(type1))[0]
assert len(A) == a == chain["a"] == 1
EA = set().union(*(te(t) for t in A))
assert EA == {tuple(e) for e in literal["E_A_edges"]}
Gprime = edges - EA

pp_candidates = triangles(Gprime)
packing(Pprime, pp_candidates)
weights = [(int(len(te(t) & O) == 2), 1) for t in pp_candidates]
b, m = optimum(pp_candidates, weights)
assert (b, m) == (chain["b"], chain["m"]) == (3, 3)
assert len(Pprime) == m
assert sum(len(te(t) & O) == 2 for t in Pprime) == b
B = set().union(*(te(t) & O for t in Pprime))
assert B == {tuple(e) for e in literal["B_edges"]}
H = Gprime - B
assert H == {tuple(e) for e in literal["H_edges"]}
Htris = triangles(H)
packing(Q, Htris)
c = optimum(Htris, [(1,)] * len(Htris))[0]
assert len(Q) == c == chain["c"] == 1
assert a + b + c - n == chain["margin"] == 1
print({"vertices": len(vertices), "edges": len(edges), "triangles": len(all_tris),
       "H_triangles": [list(t) for t in Htris], "n": n, "a": a,
       "b": b, "m": m, "c": c, "margin": a + b + c - n})
