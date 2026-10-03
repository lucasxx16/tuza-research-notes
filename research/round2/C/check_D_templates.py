"""Independent finite-input audit of D's signed templates; no census/finder imports."""

import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this audit uses assertions")

import check_saved_orbits as own


PATH = Path(__file__).resolve().parents[1] / "D" / "compressed_templates.json"
DATA = json.loads(PATH.read_text(encoding="utf-8"))
OPT = tuple(map(tuple, DATA["optional_edges"]))
OPT_INDEX = {e: i for i, e in enumerate(OPT)}
assert len(OPT) == len(OPT_INDEX) == 24

FIXED = {own.edge(own.U, own.V)}
FIXED |= {own.edge(own.U, x) for x in own.C + own.A}
FIXED |= {own.edge(own.V, x) for x in own.C + own.B}
UNIVERSAL = FIXED | set(OPT)


def move_edge(e, p):
    return own.edge(p[e[0]], p[e[1]])


def move_triangle(t, p):
    return tuple(sorted(p[v] for v in t))


def edge_mask(edges):
    mask = 0
    for e in edges:
        mask |= 1 << OPT_INDEX[e]
    return mask


def mask_edges(mask):
    return {e for i, e in enumerate(OPT) if mask & (1 << i)}


assert set(OPT) == UNIVERSAL - FIXED
assert {tuple(p) for p in DATA["vertex_permutations"]} == {tuple(p) for p in own.GAMMA}

PROFILES = []
for template in DATA["templates"]:
    packing = [tuple(t) for t in template["packing"]]
    cover = {tuple(e) for e in template["cover"]}
    D = cover & FIXED
    R = cover & set(OPT)
    assert cover == D | R
    used = set()
    for t in packing:
        te = own.triangle_edges(t)
        assert te <= UNIVERSAL and not (te & used)
        used |= te
    P = used & set(OPT)
    assert P <= R
    assert all(own.triangle_edges((own.U, own.V, c)) & D for c in own.C)
    assert len(D) + len(R) <= 2 * len(packing)

    danger = set()
    for x, y in OPT:
        for h in (own.U, own.V):
            if own.edge(h, x) in FIXED and own.edge(h, y) in FIXED:
                if own.edge(h, x) not in D and own.edge(h, y) not in D:
                    danger.add((x, y))
    N = danger - R
    assert edge_mask(P) == template["required"]
    assert edge_mask(N) == template["forbidden"]
    assert not (P & N)
    PROFILES.append((packing, D, R, P, N))

print("templates passing universal signed-rim conditions:", len(PROFILES))


IMAGES = []
for ti, (packing, D, R, P, N) in enumerate(PROFILES):
    for pi, p in enumerate(own.GAMMA):
        moved_p = {move_edge(e, p) for e in P}
        moved_n = {move_edge(e, p) for e in N}
        IMAGES.append((ti, pi, edge_mask(moved_p), edge_mask(moved_n), p))

key_to_record = {
    (r["core_mask"], r["left_side_mask"], r["right_side_mask"]): r
    for r in own.RECORDS
}
assert len(key_to_record) == 1144
assert len(DATA["assignments"]) == 1144

coverage_counts = [0] * len(PROFILES)
for record, (edges, _, _) in zip(own.RECORDS, own.AUDITED):
    current = edge_mask(edges & set(OPT))
    applicable = {ti for ti, _, req, forbid, _ in IMAGES
                  if (current & req) == req and (current & forbid) == 0}
    assert applicable, (record["core_mask"], record["left_side_mask"], record["right_side_mask"])
    for ti in applicable:
        coverage_counts[ti] += 1
print("saved graphs covered by at least one transformed template:", len(own.RECORDS))
print("individual template coverage:", coverage_counts)


assignment_keys = set()
for assignment in DATA["assignments"]:
    key = tuple(assignment["key"])
    assert key in key_to_record and key not in assignment_keys
    assignment_keys.add(key)
    record = key_to_record[key]
    ti = assignment["template"]
    pi = assignment["permutation_index"]
    assert 0 <= ti < len(PROFILES) and 0 <= pi < 192
    p = DATA["vertex_permutations"][pi]
    assert tuple(p) in {tuple(q) for q in own.GAMMA}
    packing, D, R, P, N = PROFILES[ti]
    edges = own.graph_edges(record)
    moved_p = {move_edge(e, p) for e in P}
    moved_n = {move_edge(e, p) for e in N}
    assert moved_p <= edges and not (moved_n & edges)
    moved_packing = [move_triangle(t, p) for t in packing]
    moved_cover = {move_edge(e, p) for e in D}
    moved_cover |= {move_edge(e, p) for e in R} & edges
    trial = dict(record, packing=[list(t) for t in moved_packing],
                 cover=[list(e) for e in sorted(moved_cover)])
    own.audit(trial)

assert assignment_keys == set(key_to_record)
print("saved assignments with independently verified transferred witnesses:", len(assignment_keys))
