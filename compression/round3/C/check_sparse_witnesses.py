"""Check literal E witnesses on saved P3+isolate, star, and P4 records only."""

import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this check uses assertions")


SOURCE = Path(__file__).resolve().parents[2] / "input" / "B_codegree4_certificates.json"
doc = json.loads(SOURCE.read_text(encoding="utf-8"))
labels = doc["vertex_labels"]
u, v = labels["u"], labels["v"]
C = tuple(labels["common"])
A = tuple(labels["left_exclusive"])
B = tuple(labels["right_exclusive"])


def edge(x, y):
    return tuple(sorted((x, y)))


def edges_of_triangle(t):
    return {edge(x, y) for x, y in itertools.combinations(t, 2)}


def graph_edges(record):
    edges = {edge(u, v)}
    edges.update(edge(u, x) for x in C + A)
    edges.update(edge(v, x) for x in C + B)
    for bit, (i, j) in enumerate(doc["core_bit_order"]):
        if record["core_mask"] & (1 << bit):
            edges.add(edge(C[i], C[j]))
    for field, side in (("left_side_mask", A), ("right_side_mask", B)):
        for bit, (i, j) in enumerate(doc["side_bit_order"]):
            if record[field] & (1 << bit):
                edges.add(edge(C[i], side[j - 4]) if i < 4 else edge(*side))
    return edges


counts = {3: 0, 7: 0, 13: 0}
for rec in doc["records"]:
    core = rec["core_mask"]
    if core not in counts:
        continue
    edges = graph_edges(rec)
    p, q0, r0, s0 = C
    if core == 13:
        paths = [(pp, qq, rr, ss) for pp, qq, rr, ss in itertools.permutations(C)
                 if all(edge(x, y) in edges for x, y in ((pp, qq), (qq, rr), (rr, ss)))
                 and all(edge(x, y) not in edges for x, y in ((pp, rr), (pp, ss), (qq, ss)))]
        choices = [(hub_u, hub_v, left, right, pp, qq, rr, ss, aa, bb)
                   for hub_u, hub_v, left, right in ((u, v, A, B), (v, u, B, A))
                   for pp, qq, rr, ss in paths for aa in left for bb in right
                   if edge(pp, aa) in edges and edge(rr, bb) in edges]
        assert choices, (core, rec["left_side_mask"], rec["right_side_mask"])
        hub_u, hub_v, left, right, pp, qq, rr, ss, aa, bb = choices[0]
        packing = [(hub_u, hub_v, ss), (hub_u, qq, rr), (hub_u, pp, aa),
                   (hub_v, pp, qq), (hub_v, rr, bb)]
        cover = {edge(hub_u, hub_v), *(edge(hub_u, x) for x in left),
                 *(edge(hub_v, x) for x in right), edge(pp, qq), edge(qq, rr),
                 edge(rr, ss), edge(pp, aa), edge(rr, bb)}
    else:
        if core == 3:
            assert edge(p, q0) in edges and edge(p, r0) in edges
            assert all(edge(x, y) not in edges for x, y in ((p, s0), (q0, r0), (q0, s0), (r0, s0)))
        else:
            assert all(edge(p, x) in edges for x in (q0, r0, s0))
            assert all(edge(x, y) not in edges for x, y in ((q0, r0), (q0, s0), (r0, s0)))
        leaves = (q0, r0) if core == 3 else (q0, r0, s0)
        choices = [(q, a, r, b) for q in leaves for a in A
                   for r in leaves for b in B
                   if q != r and edge(q, a) in edges and edge(r, b) in edges]
        assert choices, (core, rec["left_side_mask"], rec["right_side_mask"])
        q, a, r, b = choices[0]
        s = next(x for x in leaves + ((s0,) if core == 3 else ()) if x not in (q, r))
        packing = [(u, v, s), (u, p, r), (u, q, a), (v, p, q), (v, r, b)]
        cover = {edge(u, v), *(edge(u, x) for x in A), *(edge(v, x) for x in B),
                 edge(p, q), edge(p, r), edge(q, a), edge(r, b)}
        if edge(p, s) in edges:
            cover.add(edge(p, s))
    used = set()
    for t in packing:
        triangle_edges = edges_of_triangle(t)
        assert triangle_edges <= edges and not triangle_edges & used
        used.update(triangle_edges)
    assert cover <= edges and len(cover) <= 2 * len(packing)
    vertices = (u, v) + C + A + B
    assert all(edges_of_triangle(t) & cover for t in itertools.combinations(vertices, 3)
               if (u in t or v in t) and edges_of_triangle(t) <= edges)
    assert all(e in cover for t in packing for e in edges_of_triangle(t)
               if u not in e and v not in e)
    counts[core] += 1

assert counts == {3: 150, 7: 113, 13: 273}, counts
print("E witnesses validated on saved core records:", counts)
