"""Role B round 6 addendum (E request) -- saved-record center-attachment pairing query.

Reuses the decoder of check_diamond_transfer.py (imported, unchanged) on the 139 saved
diamond-core records only: no new graphs, no search, no generic subgraph census, no MILP.
For every record we check that each degree-3 core center has exactly one A-side
(left_exclusive, hub u) and exactly one B-side (right_exclusive, hub v) neighbour, then
label the two centers on that side PAIRED (same unique private neighbour) / SPLIT
(different ones).  Groups: (A paired|split, B paired|split, a0a1 present, b0b1 present);
a second view merges the A<->B label swap and records the swap explicitly per member.
All counts are diagnostics, not a proof.  Attribution: dataset Gupta, CC BY 4.0.
"""
import json, sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_diamond_transfer as M                            # reuse the first decoder

LBL = {M.LBL["u"]: "u", M.LBL["v"]: "v"}
LBL.update({c: M.CN[i] for i, c in enumerate(M.COM)})
LBL.update({c: M.AN[i] for i, c in enumerate(M.LA)})
LBL.update({c: M.BN[i] for i, c in enumerate(M.LB)})
COVERED = {w["index"] for w in json.loads((HERE / "diamond_transfer_witnesses.json").read_text(encoding="utf-8"))}
REMAIN = [w["index"] for w in json.loads((HERE / "diamond_transfer_remaining.json").read_text(encoding="utf-8"))]
tri = lambda t: "+".join(sorted(LBL[x] for x in t))
edg = lambda e: "".join(sorted(LBL[x] for x in e))

rows, exceptions = [], []
for idx, rec in enumerate(M.REC):
    E, cdeg, att, priv = M.decode(rec)
    if sum(cdeg) != 2 * (2 * M.NMC - 3):                       # diamond core = 5 core edges
        continue
    ctr = [i for i in range(M.NMC) if cdeg[i] == M.NMC - 1]
    leaf = [j for j in range(M.NMC) if cdeg[j] == M.NMC - 2]
    nb = {s: {M.CN[i]: sorted(n for n, m in att[s].items() if m >> i & 1) for i in ctr} for s in ("u", "v")}
    ok = all(len(v) == 1 for s in ("u", "v") for v in nb[s].values() if isinstance(v, list)) and \
        all(len(nb[s][M.CN[i]]) == 1 for s in ("u", "v") for i in ctr)
    if not ok:
        exceptions.append(dict(index=idx, key=[rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]],
                               center_neighbors=nb))
    st = {s: ((nb[s][M.CN[ctr[0]]] == nb[s][M.CN[ctr[1]]]) and "paired" or "split") if ok else "no_unique_attachment"
          for s in ("u", "v")}
    key = (st["u"], st["v"], bool(priv["u"]), bool(priv["v"]))
    flipped = (st["v"], st["u"], bool(priv["v"]), bool(priv["u"]))
    rows.append(dict(index=idx, key=[rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]],
                     membership="covered42" if idx in COVERED else "remaining97",
                     centers=[M.CN[i] for i in ctr], leaves=[M.CN[j] for j in leaf],
                     center_attachments=nb, unique_ok=ok,
                     leaf_matrix={M.CN[j]: {n: int((att["u"] if n in M.AN else att["v"])[n] >> j & 1)
                                            for n in M.AN + M.BN} for j in leaf},
                     leaf_AB_multiplicity=[[sum(1 for j in leaf if (att["u"][a] >> j & 1) and (att["v"][b] >> j & 1))
                                            for b in M.BN] for a in M.AN],
                     group=key, canonical=min(key, flipped), ab_swapped=key > flipped))

gkey = lambda k: "A=%s,B=%s,a0a1=%d,b0b1=%d" % (k[0], k[1], int(k[2]), int(k[3]))
raw, canon = defaultdict(list), defaultdict(list)
for r in rows:
    raw[gkey(r["group"])].append(r)
    canon[gkey(r["canonical"])].append(r)
pack = lambda g, mem: {k: dict(count=len([r for r in v if r["membership"] in mem]),
                               covered42=len([r for r in v if r["membership"] == "covered42"]),
                               remaining97=len([r for r in v if r["membership"] == "remaining97"]),
                               record_keys=[r["key"] for r in v if r["membership"] in mem])
                       for k, v in sorted(g.items())}
reps = {}
for k, v in sorted(canon.items()):
    rem = [r for r in v if r["membership"] == "remaining97"]
    if not rem:
        continue
    r = min(rem, key=lambda z: z["index"])
    rec = M.REC[r["index"]]
    reps[k] = dict(record_key=r["key"], index=r["index"], ab_swapped_label_view=r["ab_swapped"],
                   group_label_view=gkey(r["group"]), centers=r["centers"], leaves=r["leaves"],
                   center_attachments=r["center_attachments"], leaf_attachment_matrix_rows_leaf_cols_private=r["leaf_matrix"],
                   leaf_AB_multiplicity_rows_a0a1_cols_b0b1=r["leaf_AB_multiplicity"],
                   a0a1_edge=r["group"][2], b0b1_edge=r["group"][3],
                   saved_packing=[tri(t) for t in rec["packing"]], saved_cover=[edg(e) for e in rec["cover"]])
both = [r for r in rows if r["group"][2] and r["group"][3]]
pside = {r["index"] for r in both if "paired" in r["group"][:2]}
ssplit = [r for r in both if r["group"][:2] == ("split", "split")]
consist = dict(both_edges_records=len(both), with_a_paired_side=len(pside), paired_side_equals_covered42=(pside == COVERED),
               split_split_both_edges=len(ssplit), split_split_all_in_remaining97=all(r["membership"] == "remaining97" for r in ssplit))
out = dict(query="E addendum: center-attachment uniqueness and A/B pairing grouping of the 139 saved diamond records",
           reuse="decoder imported from check_diamond_transfer.py; saved records only, no new graphs/search/MILP",
           attribution="dataset Gupta, CC BY 4.0 (compression/input/PROVENANCE.txt); diagnostic counts, not a proof",
           legend=dict(A_side="left_exclusive a0,a1 attached to hub u", B_side="right_exclusive b0,b1 attached to hub v",
                       paired="both degree-3 centers share the same unique private neighbour on that side",
                       split="the two centers use different private neighbours on that side",
                       group="A pairing, B pairing, a0a1 internal edge, b0b1 internal edge"),
           total_diamond_records=len(rows), centers_unique_A_and_B_in_record=sum(1 for r in rows if r["unique_ok"]),
           records_failing_uniqueness=len(exceptions), failing_examples=[e["key"] for e in exceptions[:3]],
           grouped_all_139_raw_no_swap=pack(raw, ("covered42", "remaining97")),
           grouped_all_139_A_B_swap_merged=pack(canon, ("covered42", "remaining97")),
           swap_used_count=sum(1 for r in rows if r["ab_swapped"]),
           grouped_remaining97_raw_no_swap=pack(raw, ("remaining97",)),
           grouped_remaining97_A_B_swap_merged=pack(canon, ("remaining97",)),
           representative_per_nonempty_remaining_group=reps,
           covered42_group_counts={k: len([r for r in v if r["membership"] == "covered42"]) for k, v in sorted(canon.items())},
           pairing_transfer_consistency=consist)
(HERE / "diamond_center_pairing_groups.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
gc = {k: v["count"] for k, v in out["grouped_all_139_A_B_swap_merged"].items() if v["count"]}
gr = {k: v["count"] for k, v in out["grouped_remaining97_A_B_swap_merged"].items() if v["count"]}
rep = ["Role B addendum (E) -- saved-record query, decoder reused, no new graphs/search/MILP.",
       "139 diamond records checked: centers with exactly one A and one B attachment in %d/%d; exceptions %d." %
       (out["centers_unique_A_and_B_in_record"], len(rows), out["records_failing_uniqueness"]),
       "Grouping (A/B label swap merged, swap recorded per member; %d records needed the swap): %s" %
       (out["swap_used_count"], gc),
       "Remaining-97 split of the same grouping: %s" % gr,
       "Cross-check vs the transfer audit: of the %d records with BOTH internal edges, the %d with a paired side are"
       " exactly the 42 covered ones (%s); the %d split/split ones all fall in the 97 remainder." %
       (consist["both_edges_records"], consist["with_a_paired_side"], consist["paired_side_equals_covered42"],
        consist["split_split_both_edges"]),
       "One representative per non-empty remaining group (leaf attachment matrix + saved packing/cover) is stored in",
       "diamond_center_pairing_groups.json:representative_per_nonempty_remaining_group.",
       "Counts are diagnostics only; no proof claimed. Dataset attribution: Gupta, CC BY 4.0."]
(HERE / "grouping_report.txt").write_text("\n".join(rep) + "\n", encoding="utf-8")
print("checked", len(rows), "unique_ok", out["centers_unique_A_and_B_in_record"], "exceptions", out["records_failing_uniqueness"])
print("groups139", gc)
print("groups97", gr)
print("swap_used", out["swap_used_count"], "reps", len(reps), "consistency", consist)
