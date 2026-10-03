"""Rebuild signed-pattern incidence from saved witnesses; audit B2's 9/9 proof."""

import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this audit uses assertions")

import check_saved_orbits as own

ROOT = Path(__file__).resolve().parents[1]
D_INCIDENCE = json.loads((ROOT / "templates" / "finite_cover_incidence.json").read_text())
SELECTED = json.loads((ROOT / "set_cover" / "selected_cover.json").read_text())
LOWER = json.loads((ROOT / "set_cover" / "lower_bound.json").read_text())

OPT = tuple(own.edge(*e) for e in json.loads((ROOT / "templates" / "compressed_templates.json").read_text())["optional_edges"])
OI = {e: i for i, e in enumerate(OPT)}
FIXED = {own.edge(own.U, own.V)}
FIXED |= {own.edge(own.U, x) for x in own.C + own.A}
FIXED |= {own.edge(own.V, x) for x in own.C + own.B}
assert len(OPT) == len(OI) == 24 and len(FIXED) == 13


def bits(edges):
    out = 0
    for e in edges:
        out |= 1 << OI[e]
    return out


def bit_indices(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


PERMS = []
for p in own.GAMMA:
    translated = [OI[own.edge(p[x], p[y])] for x, y in OPT]
    PERMS.append((p, translated))


def move_bits(mask, translated):
    out = 0
    for i in bit_indices(mask):
        out |= 1 << translated[i]
    return out


def source_profile(record, graph, packing, cover):
    D = cover & FIXED
    P = {e for t in packing for e in own.triangle_edges(t) if e in OI}
    danger = {e for e in OPT if any(
        own.edge(h, e[0]) in FIXED and own.edge(h, e[1]) in FIXED
        and own.edge(h, e[0]) not in D and own.edge(h, e[1]) not in D
        for h in (own.U, own.V))}
    R = P | (danger & graph)
    N = danger - R
    assert P <= R <= cover and len(D) + len(R) <= 2 * len(packing)
    assert all(own.triangle_edges((own.U, own.V, c)) & D for c in own.C)
    return bits(P), bits(N), D, R, packing


RECORDS = own.RECORDS
GRAPHS = [triple[0] for triple in own.AUDITED]
PROFILES = [source_profile(r, *triple) for r, triple in zip(RECORDS, own.AUDITED)]
KEY_TO_INDEX = {(r["core_mask"], r["left_side_mask"], r["right_side_mask"]): i
                for i, r in enumerate(RECORDS)}
assert len(KEY_TO_INDEX) == len(RECORDS) == 1144


def canonical(req, forb):
    return min((move_bits(req, m), move_bits(forb, m)) for _, m in PERMS)


raw_classes = {canonical(p[0], p[1]) for p in PROFILES}
assert len(raw_classes) == 499
print("catalogue-derived signed-pattern Gamma orbits:", len(raw_classes))

CANDIDATES = D_INCIDENCE["candidates"]
assert len(CANDIDATES) == 499
candidate_classes = set()
candidate_profiles = []
for cid, candidate in enumerate(CANDIDATES):
    assert candidate["id"] == cid
    source_i = KEY_TO_INDEX[tuple(candidate["source_key"])]
    profile = PROFILES[source_i]
    assert (candidate["required_mask"], candidate["forbidden_mask"]) == profile[:2]
    candidate_classes.add(canonical(profile[0], profile[1]))
    candidate_profiles.append(profile)
assert candidate_classes == raw_classes and len(candidate_classes) == 499

# Encode the 1,144 saved graph masks as 1,144-bit columns, then rebuild each
# candidate's entire coverage without reading its supplied incidence list.
ALL = (1 << len(RECORDS)) - 1
graph_masks = [bits(graph & set(OPT)) for graph in GRAPHS]
PRESENT = [sum(1 << j for j, g in enumerate(graph_masks) if g & (1 << i))
           for i in range(24)]


def matched_records(req, forb):
    out = ALL
    for i in bit_indices(req):
        out &= PRESENT[i]
    for i in bit_indices(forb):
        out &= ALL ^ PRESENT[i]
    return out


coverage = []
for candidate, profile in zip(CANDIDATES, candidate_profiles):
    req, forb = profile[:2]
    patterns = {(move_bits(req, m), move_bits(forb, m)) for _, m in PERMS}
    covered = 0
    for a, b in patterns:
        covered |= matched_records(a, b)
    stated = sum(1 << j for j in candidate["covered_records"])
    assert covered == stated, candidate["id"]
    coverage.append(covered)
print("candidate incidence lists independently matched:", len(coverage))

ids = SELECTED["selected_candidate_ids"]
assert ids == [7, 78, 195, 214, 316, 329, 387, 428, 491]
union = 0
for cid in ids:
    union |= coverage[cid]
assert union == ALL
print("nine selected candidates cover saved records:", union.bit_count())

lower_indices = LOWER["packing_record_indices"]
assert len(set(lower_indices)) == 9
assert [list(list(KEY_TO_INDEX)[i]) for i in lower_indices] == LOWER["packing_record_keys"]
lower_mask = sum(1 << i for i in lower_indices)
maximum = max((c & lower_mask).bit_count() for c in coverage)
assert maximum == 1
print("maximum lower-bound records hit by one candidate:", maximum)

# Independently transfer the source witnesses for the nine selected candidates.
assigned = 0
for index, (record, graph, graph_mask) in enumerate(zip(RECORDS, GRAPHS, graph_masks)):
    chosen = None
    for cid in ids:
        req, forb, D, R, packing = candidate_profiles[cid]
        for p, m in PERMS:
            moved_req, moved_forb = move_bits(req, m), move_bits(forb, m)
            if (graph_mask & moved_req) == moved_req and not (graph_mask & moved_forb):
                chosen = (p, D, R, packing)
                break
        if chosen is not None:
            break
    assert chosen is not None, index
    p, D, R, packing = chosen
    new_packing = [sorted(p[v] for v in t) for t in packing]
    new_cover = {own.edge(p[x], p[y]) for x, y in D}
    new_cover |= {own.edge(p[x], p[y]) for x, y in R} & graph
    trial = dict(record, packing=new_packing, cover=[list(e) for e in sorted(new_cover)])
    own.audit(trial)
    assigned += 1
print("selected-template transferred witnesses independently checked:", assigned)
print("exact optimum within this 499-candidate dictionary:", 9)
