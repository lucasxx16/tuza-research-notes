"""Independent literal verification of the one saved J/{b,t} certificate.

Reconstructs the fixed graph and full ambient hub-triangle list directly;
does not import or rerun the MILP/search script.
"""
import itertools
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O so exact certificate assertions remain active")

ROOT = Path(__file__).resolve().parents[3]
WIT = ROOT / "research/round7/B/witness.json"
W = json.loads(WIT.read_text(encoding="utf-8"))
core = ("w", "0", "1", "2", "3", "4", "5", "6")
outside = {"a": "03456", "b": "01256", "c": "01234", "t": "123456"}
V = core + tuple(outside)
edge = lambda x, y: frozenset((x, y))
E = {edge(x, y) for x, y in itertools.combinations(core, 2)
     if edge(x, y) not in {edge("0", "1"), edge("3", "5")}}
E |= {edge(h, v) for h, nb in outside.items() for v in nb}
U = {"b", "t"}
assert edge("b", "t") not in E
PV = U | {v for h in U for v in outside[h]}
EP = {e for e in E if e <= PV}


def triangles(V0, E0):
    return {frozenset(t) for t in itertools.combinations(V0, 3)
            if all(edge(x, y) in E0 for x, y in itertools.combinations(t, 2))}


TJ = triangles(V, E)
TP = triangles(PV, EP)
HJ = {t for t in TJ if t & U}
HP = {t for t in TP if t & U}
assert (len(V), len(E), len(PV), len(EP), len(TP), len(HP)) == (12, 47, 9, 30, 48, 23)
assert HJ == HP
assert {frozenset(e) for e in W["graph_J"]["edges"]} == E
assert {frozenset(e) for e in W["patch"]["edges"]} == EP
assert set(W["patch"]["vertices"]) == PV
S = [frozenset(t) for t in W["S"]]
X = {frozenset(e) for e in W["X"]}


def check(S0, X0):
    sedges = [edge(x, y) for t in S0 for x, y in itertools.combinations(t, 2)]
    external = {e for e in sedges if not e & U}
    return {
        "S_exists": len(S0) == len(set(S0)) and all(t in TP for t in S0),
        "S_edge_disjoint": len(sedges) == len(set(sedges)) == 3 * len(S0),
        "X_subset_patch": X0 <= EP,
        "all_ambient_hub_triangles_hit": all(any(edge(x, y) in X0 for x, y in itertools.combinations(t, 2)) for t in HJ),
        "all_external_S_edges_in_X": external <= X0,
        "budget": len(X0) <= 2 * len(S0),
    }


checks = check(S, X)
assert len(S) == 7 and len(X) == 13 and all(checks.values()), checks
assert W["sizes"]["slack_2|S|-|X|"] == 1

# D's smaller symbolic certificate on the same fixed graph, independently
# reconstructed rather than read from the solver witness.
S6 = [frozenset(t) for t in (("1", "2", "b"), ("5", "6", "b"),
                            ("1", "5", "t"), ("2", "6", "t"),
                            ("1", "4", "6"), ("2", "4", "5"))]
X6 = {edge(x, y) for x, y in (("1", "2"), ("1", "5"), ("1", "6"),
                              ("2", "5"), ("2", "6"), ("5", "6"),
                              ("1", "4"), ("2", "4"), ("4", "5"),
                              ("4", "6"), ("0", "b"), ("3", "t"))}
assert len(S6) == 6 and len(X6) == 12 and all(check(S6, X6).values())
assert set(S) == set(S6) | {frozenset(("3", "4", "t"))}
assert X == X6 | {edge("3", "4")}

# Negative controls test separate obligations, including the previously
# error-prone outside-edge and factor-two budget conditions.
external_edge = edge("1", "4")
assert external_edge in X
assert not check(S, X - {external_edge})["all_external_S_edges_in_X"]
assert not check(S, X - {edge("0", "b")})["all_ambient_hub_triangles_hit"]
assert not check(S, X | {edge("b", "t")})["X_subset_patch"]
assert not check(S + [S[0]], X)["S_edge_disjoint"]
spare = list(EP - X)
assert len(spare) >= 2
assert not check(S, X | set(spare[:2]))["budget"]

print({"J_vertices": len(V), "J_edges": len(E), "patch_vertices": len(PV),
       "patch_edges": len(EP), "ambient_hub_triangles": len(HJ),
       "S": len(S), "X": len(X), "checks": checks,
       "D_smaller_S_X": [len(S6), len(X6)], "negative_controls": 5})
