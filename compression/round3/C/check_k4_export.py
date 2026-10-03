"""Independently decode and validate B's 21 saved K4 recipe witnesses."""

import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this check uses assertions")


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source = json.loads((ROOT / "input" / "B_codegree4_certificates.json").read_text(encoding="utf-8"))
export = json.loads((HERE.parent / "B" / "k4_recipe_check.json").read_text(encoding="utf-8"))
labels = source["vertex_labels"]
u, v = labels["u"], labels["v"]
C = tuple(labels["common"])
A = tuple(labels["left_exclusive"])
B = tuple(labels["right_exclusive"])
vertices = (u, v) + C + A + B
names = {"u": u, "v": v}
names.update({f"c{i}": c for i, c in enumerate(C)})
names.update({f"a{i}": a for i, a in enumerate(A)})
names.update({f"b{i}": b for i, b in enumerate(B)})


def edge(x, y):
    return tuple(sorted((x, y)))


def triangle_edges(t):
    return {edge(x, y) for x, y in itertools.combinations(t, 2)}


def graph_edges(rec):
    result = {edge(u, v)}
    result.update(edge(u, x) for x in C + A)
    result.update(edge(v, x) for x in C + B)
    for bit, (i, j) in enumerate(source["core_bit_order"]):
        if rec["core_mask"] & (1 << bit):
            result.add(edge(C[i], C[j]))
    for field, side in (("left_side_mask", A), ("right_side_mask", B)):
        for bit, (i, j) in enumerate(source["side_bit_order"]):
            if rec[field] & (1 << bit):
                result.add(edge(C[i], side[j - 4]) if i < 4 else edge(*side))
    return result


def decode_edge(s):
    possibilities = {edge(x, y) for nx, x in names.items() for ny, y in names.items()
                     if x != y and (nx + ny == s or ny + nx == s)}
    assert len(possibilities) == 1, (s, possibilities)
    return possibilities.pop()


k4_indices = {i for i, rec in enumerate(source["records"]) if rec["core_mask"] == 63}
witnesses = export["witnesses"]
assert len(witnesses) == len(k4_indices) == 21
assert {item["record_index"] for item in witnesses} == k4_indices
counts = {"G": 0, "E": 0}
for item in witnesses:
    rec = source["records"][item["record_index"]]
    assert item["key"] == [rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]]
    edges = graph_edges(rec)
    packing = [tuple(t) for t in item["packing"]]
    cover = {tuple(ed) for ed in item["cover_edges"]}
    named_packing = {frozenset(names[name] for name in t) for t in item["triangles"]}
    assert {frozenset(t) for t in packing} == named_packing
    assert cover == {decode_edge(s) for s in item["cover"]}
    assert len(packing) == len({frozenset(t) for t in packing}) == 6
    assert len(cover) == len(item["cover_edges"]) == len(item["cover"]) == 12
    assert cover <= edges
    used = set()
    for t in packing:
        te = triangle_edges(t)
        assert len(set(t)) == 3 and te <= edges and not te & used
        used.update(te)
    assert all(triangle_edges(t) & cover for t in itertools.combinations(vertices, 3)
               if (u in t or v in t) and triangle_edges(t) <= edges)
    assert all(e in cover for t in packing for e in triangle_edges(t)
               if u not in e and v not in e)
    counts[item["construction"]] += 1

assert counts == {"G": 18, "E": 3}, counts
print("Independently validated K4 exports:", counts)
