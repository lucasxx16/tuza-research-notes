"""Check D's final literal archive against C's independently rebuilt nine-cover."""

import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python -O; this audit uses assertions")

import check_B2_optimum as base

ROOT = Path(__file__).resolve().parents[1]
optimal = json.loads((ROOT / "D" / "optimal_templates.json").read_text())
literal = json.loads((ROOT / "D" / "optimal_transformed_certificates.json").read_text())
summary = json.loads((ROOT / "D" / "optimum_summary.json").read_text())
ids = base.SELECTED["selected_candidate_ids"]
assert optimal["candidate_ids"] == summary["candidate_ids"] == ids
assert len(optimal["templates"]) == len(ids) == 9
assert len(optimal["assignments"]) == len(literal) == len(base.RECORDS) == 1144
assert optimal["lower_bound_record_indices"] == base.LOWER["packing_record_indices"]
assert optimal["lower_bound_record_keys"] == base.LOWER["packing_record_keys"]
assert {tuple(p) for p in optimal["vertex_permutations"]} == {tuple(p) for p in base.own.GAMMA}

for i, (cid, template) in enumerate(zip(ids, optimal["templates"])):
    assert template["candidate_id"] == cid
    req, forb, D, R, packing = base.candidate_profiles[cid]
    assert (template["required"], template["forbidden"]) == (req, forb)
    assert {tuple(e) for e in template["cover"]} == D | R
    assert {tuple(t) for t in template["packing"]} == set(packing)
print("final exported templates agree with rebuilt candidates:", len(ids))

for j, (assignment, saved) in enumerate(zip(optimal["assignments"], literal)):
    record = base.RECORDS[j]
    graph = base.GRAPHS[j]
    key = [record["core_mask"], record["left_side_mask"], record["right_side_mask"]]
    assert assignment["record_index"] == saved["record_index"] == j
    assert assignment["key"] == saved["key"] == key
    ti = assignment["template"]
    cid = ids[ti]
    assert assignment["candidate_id"] == saved["candidate_id"] == cid
    assert saved["template"] == ti
    pi = assignment["permutation_index"]
    assert saved["permutation_index"] == pi
    p = optimal["vertex_permutations"][pi]
    assert assignment["vertex_permutation"] == saved["vertex_permutation"] == p
    req, forb, D, R, packing = base.candidate_profiles[cid]
    moved_req = base.move_bits(req, base.PERMS[next(k for k, (q, _) in enumerate(base.PERMS)
                                                       if tuple(q) == tuple(p))][1])
    moved_forb = base.move_bits(forb, base.PERMS[next(k for k, (q, _) in enumerate(base.PERMS)
                                                         if tuple(q) == tuple(p))][1])
    mask = base.graph_masks[j]
    assert (mask & moved_req) == moved_req and not (mask & moved_forb)
    rebuilt_packing = {tuple(sorted(p[v] for v in t)) for t in packing}
    rebuilt_cover = {base.own.edge(p[x], p[y]) for x, y in D}
    rebuilt_cover |= {base.own.edge(p[x], p[y]) for x, y in R} & graph
    assert {tuple(t) for t in saved["packing"]} == rebuilt_packing
    assert {tuple(e) for e in saved["cover"]} == rebuilt_cover
    base.own.audit(dict(record, packing=[list(t) for t in rebuilt_packing],
                        cover=[list(e) for e in rebuilt_cover]))
print("final exported assignments/literal certificates agree and verify:", len(literal))
