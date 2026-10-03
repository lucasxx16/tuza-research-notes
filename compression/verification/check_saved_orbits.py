"""Independent scan of saved witnesses only; no configuration census or finder."""

import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this audit uses assertions")

SOURCE = Path(__file__).resolve().parents[1] / "input" / "B_codegree4_certificates.json"
DOCUMENT = json.loads(SOURCE.read_text(encoding="utf-8"))
RECORDS = DOCUMENT["records"]
LABELS = DOCUMENT["vertex_labels"]
U, V = LABELS["u"], LABELS["v"]
C = tuple(LABELS["common"])
A = tuple(LABELS["left_exclusive"])
B = tuple(LABELS["right_exclusive"])
VERTICES = (U, V) + C + A + B
CORE_BITS = DOCUMENT["core_bit_order"]
SIDE_BITS = DOCUMENT["side_bit_order"]


def maps():
    for core in itertools.permutations(range(4)):
        for sa, sb, hubs in itertools.product(range(2), repeat=3):
            p = [0] * 10
            p[0], p[1] = (1, 0) if hubs else (0, 1)
            for c in range(4):
                p[2 + c] = 2 + core[c]
            for a in range(2):
                p[6 + a] = (8 if hubs else 6) + (a ^ sa)
                p[8 + a] = (6 if hubs else 8) + (a ^ sb)
            yield p


GAMMA = tuple(maps())
assert len(GAMMA) == len({tuple(p) for p in GAMMA}) == 192


def transform(items, p):
    return tuple(sorted(tuple(sorted(p[v] for v in item)) for item in items))


packing_orbits = set()
pair_orbits = set()
for record in RECORDS:
    packing = record["packing"]
    cover = record["cover"]
    shapes = [(transform(packing, p), transform(cover, p)) for p in GAMMA]
    packing_orbits.add(min(s for s, _ in shapes))
    pair_orbits.add(min(shapes))

print("saved records:", len(RECORDS))
print("packing orbits under 192 vertex relabelings:", len(packing_orbits))
print("(packing, cover) orbits under 192 vertex relabelings:", len(pair_orbits))


def edge(x, y):
    return tuple(sorted((x, y)))


def triangle_edges(t):
    return {edge(x, y) for x, y in itertools.combinations(t, 2)}


def graph_edges(record):
    result = {edge(U, V)}
    result.update(edge(U, x) for x in C + A)
    result.update(edge(V, x) for x in C + B)
    for bit, (x, y) in enumerate(CORE_BITS):
        if record["core_mask"] & (1 << bit):
            result.add(edge(C[x], C[y]))
    for field, side in (("left_side_mask", A), ("right_side_mask", B)):
        mask = record[field]
        for bit, (x, y) in enumerate(SIDE_BITS):
            if mask & (1 << bit):
                result.add(edge(C[x], side[y - 4]) if x < 4 else edge(*side))
    return result


def triangles(edges):
    return [t for t in itertools.combinations(VERTICES, 3) if triangle_edges(t) <= edges]


def is_hub_triangle(t):
    return U in t or V in t


def audit(record):
    edges = graph_edges(record)
    packing = [tuple(t) for t in record["packing"]]
    cover = {tuple(e) for e in record["cover"]}
    assert len(cover) == len(record["cover"])
    assert cover <= edges
    used = set()
    for t in packing:
        te = triangle_edges(t)
        assert te <= edges and not (te & used)
        used |= te
    assert len(cover) <= 2 * len(packing)
    assert all(triangle_edges(t) & cover for t in triangles(edges) if is_hub_triangle(t))
    assert all(e in cover for t in packing for e in triangle_edges(t) if U not in e and V not in e)
    return edges, packing, cover


AUDITED = [audit(record) for record in RECORDS]
print("saved records passing all three local reduction conditions:", len(AUDITED))


def gamma_formula(edges, rim):
    core_remaining = {e for e in edges - rim if set(e) <= set(C)}

    def costs(side):
        out = {}
        for bits in range(1 << len(C)):
            chosen = {C[i] for i in range(len(C)) if bits & (1 << i)}
            if any(not (set(e) & chosen) for e in core_remaining):
                continue
            forced_side = {a for a in side for c in C if c not in chosen and edge(a, c) in edges - rim}
            sideedge = edge(*side) in edges - rim
            out[bits] = len(chosen) + len(forced_side) + int(sideedge and not forced_side)
        return out

    left, right = costs(A), costs(B)
    with_uv = 1 + min(left.values()) + min(right.values())
    without_uv = min((a + b for ua, a in left.items() for vb, b in right.items()
                      if ua | vb == (1 << len(C)) - 1), default=10**9)
    return min(with_uv, without_uv)


def gamma_brute(edges, rim):
    candidates = [edge(U, V)] + [edge(U, x) for x in C + A] + [edge(V, x) for x in C + B]
    remaining = [triangle_edges(t) for t in triangles(edges) if is_hub_triangle(t) and not (triangle_edges(t) & rim)]
    universe = (1 << len(remaining)) - 1
    hits = [sum(1 << i for i, te in enumerate(remaining) if e in te) for e in candidates]
    for size in range(len(candidates) + 1):
        for choice in itertools.combinations(range(len(candidates)), size):
            covered = 0
            for i in choice:
                covered |= hits[i]
            if covered == universe:
                return size
    raise AssertionError("No spoke cover exists")


SAMPLE_BY_CORE = {}
for record, (edges, packing, cover) in zip(RECORDS, AUDITED):
    SAMPLE_BY_CORE.setdefault(record["core_mask"], (edges, packing, cover))

for core, (edges, packing, cover) in sorted(SAMPLE_BY_CORE.items()):
    forced = {e for t in packing for e in triangle_edges(t) if U not in e and V not in e}
    extra_core = {e for e in cover - forced if set(e) <= set(C)}
    rim = forced | extra_core
    formula, brute = gamma_formula(edges, rim), gamma_brute(edges, rim)
    assert formula == brute, (core, formula, brute)
print("gamma formula equals direct spoke-cover optimum on core representatives:", len(SAMPLE_BY_CORE))
