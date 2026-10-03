"""Independent literal checker for the saved diamond/Lemma-K witnesses only.

No atlas, original census, solver, or new graph search. Reconstruct each of the
42 exported record graphs directly from the public input masks, then check S,X.
"""
import itertools
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O so exact certificate assertions remain active")

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "compression/input/B_codegree4_certificates.json"
WIT = ROOT / "research/round6/B_saved/diamond_transfer_witnesses.json"

data = json.loads(SOURCE.read_text(encoding="utf-8"))
records = data["records"]
witnesses = json.loads(WIT.read_text(encoding="utf-8"))
labels = data["vertex_labels"]
C = labels["common"]
A = labels["left_exclusive"]
B = labels["right_exclusive"]
name = {"u": labels["u"], "v": labels["v"]}
name.update({f"c{i}": x for i, x in enumerate(C)})
name.update({f"a{i}": x for i, x in enumerate(A)})
name.update({f"b{i}": x for i, x in enumerate(B)})
edge = lambda x, y: frozenset((x, y))


def graph_of(rec):
    E = {edge(0, 1)}
    E.update(edge(h, c) for h in (0, 1) for c in C)
    E.update(edge(0, a) for a in A)
    E.update(edge(1, b) for b in B)
    for i, (j, k) in enumerate(data["core_bit_order"]):
        if rec["core_mask"] & (1 << i):
            E.add(edge(C[j], C[k]))
    for h, pair, key in ((0, A, "left_side_mask"), (1, B, "right_side_mask")):
        for i, (j, k) in enumerate(data["side_bit_order"]):
            if not rec[key] & (1 << i):
                continue
            vj = C[j] if j < 4 else pair[j - 4]
            vk = C[k] if k < 4 else pair[k - 4]
            E.add(edge(vj, vk))
    return E


def triangles(E):
    return [frozenset(t) for t in itertools.combinations(range(10), 3)
            if all(edge(x, y) in E for x, y in itertools.combinations(t, 2))]


def certificate(E, S, X):
    tri = triangles(E)
    sedges = [edge(x, y) for t in S for x, y in itertools.combinations(t, 2)]
    ext = {e for e in sedges if not e & {0, 1}}
    checks = {
        "distinct_triangles": len(S) == len(set(S)),
        "triangle_existence": all(t in tri for t in S),
        "edge_disjoint": len(sedges) == len(set(sedges)),
        "cover_subset_graph": X <= E,
        "hub_triangle_coverage": all(any(edge(x, y) in X for x, y in itertools.combinations(t, 2))
                                     for t in tri if t & {0, 1}),
        "packed_external_edges_in_cover": ext <= X,
        "budget": len(X) <= 2 * len(S),
    }
    return checks, ext, tri


diamond = set()
eligible = set()
missing_private_edge = 0
both_edges_no_common_center_private = 0
for i, rec in enumerate(records):
    E = graph_of(rec)
    cd = [sum(edge(c, d) in E for d in C if d != c) for c in C]
    if sorted(cd) != [2, 2, 3, 3]:
        continue
    diamond.add(i)
    centers = [C[j] for j, d in enumerate(cd) if d == 3]
    if edge(*A) not in E or edge(*B) not in E:
        missing_private_edge += 1
    elif any(all(edge(t, c) in E for c in centers) for t in A + B):
        eligible.add(i)
    else:
        both_edges_no_common_center_private += 1
assert (len(diamond), len(eligible), missing_private_edge,
        both_edges_no_common_center_private) == (139, 42, 84, 13)


assert len(witnesses) == 42
seen = set()
results = []
for w in witnesses:
    idx = w["index"]
    assert idx not in seen
    seen.add(idx)
    rec = records[idx]
    assert w["key"] == [rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]]
    E = graph_of(rec)
    cd = [sum(edge(c, d) in E for d in C if d != c) for c in C]
    assert sorted(cd) == [2, 2, 3, 3]
    R = {k: name[v] for k, v in w["roles"].items() if k in ("U", "V", "x", "y", "p", "q", "a", "b", "c", "d")}
    assert {R["U"], R["V"]} == {0, 1} and len(set(R.values())) == 10
    assert cd[C.index(R["p"])] == cd[C.index(R["q"])] == 3
    assert edge(R["a"], R["b"]) in E and edge(R["c"], R["d"]) in E
    assert edge(R["d"], R["p"]) in E and edge(R["d"], R["q"]) in E
    S = [frozenset(name[v] for v in t) for t in w["packing_S"]]
    X = {frozenset(name[v] for v in e.split("+")) for e in w["cover_X"]}
    checks, ext, tri = certificate(E, S, X)
    assert len(S) == 7 and len(X) == 14 and all(checks.values()), (idx, checks)

    # Three independent negative controls exercise external-edge safety,
    # graph membership, and packing disjointness.
    assert ext
    x_bad = X - {next(iter(ext))}
    assert not certificate(E, S, x_bad)[0]["packed_external_edges_in_cover"]
    nonedge = edge(0, B[0])
    assert nonedge not in E
    assert not certificate(E, S, X | {nonedge})[0]["cover_subset_graph"]
    assert not certificate(E, S + [S[0]], X)[0]["edge_disjoint"]
    results.append((idx, len(E), len(tri)))

assert seen == eligible
print({"diamonds": len(diamond), "eligible": len(eligible),
       "missing_private_edge": missing_private_edge,
       "both_edges_no_common_center_private": both_edges_no_common_center_private,
       "validated": len(results), "distinct_records": len(seen),
       "min_edges": min(x[1] for x in results), "max_edges": max(x[1] for x in results),
       "negative_controls_rejected": 3 * len(results), "all_tight": True})
