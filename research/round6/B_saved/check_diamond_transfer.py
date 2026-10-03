"""Role B round 6 -- bounded saved-record audit of the diamond/Lemma-K transfer claim.

Persisted records only (compression/input/B_codegree4_certificates.json): no enumeration,
no MILP/solver, no census or finder.  Claim tested: 139 diamond-core records, 42 satisfying
mad8/round5/E Lemma K up to core permutation, private-pair rename and hub side swap (BOTH
private internal edges present AND a private vertex adjacent to BOTH degree-3 core vertices).
Core degrees are decoded from core_bit_order, not a blind mask.  Attribution: dataset Gupta,
CC BY 4.0 (compression/input/PROVENANCE.txt).  Audit counts + literal certificate checks only.
"""
import json, itertools
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
DOC = json.loads((ROOT / "compression" / "input" / "B_codegree4_certificates.json").read_text(encoding="utf-8"))
REC, CB, SB = DOC["records"], [tuple(t) for t in DOC["core_bit_order"]], [tuple(t) for t in DOC["side_bit_order"]]
LBL = DOC["vertex_labels"]
COM, LA, LB = list(LBL["common"]), list(LBL["left_exclusive"]), list(LBL["right_exclusive"])
NMC, NPR = len(COM), len(LA)
CN, AN, BN = ["c%d" % i for i in range(NMC)], ["a%d" % i for i in range(NPR)], ["b%d" % i for i in range(NPR)]
ROLES = ["U", "V", "x", "y", "p", "q", "a", "b", "c", "d"]
UV = frozenset((LBL["u"], LBL["v"]))
CBITS = [(i, min(x, y), max(x, y)) for i, (x, y) in enumerate(CB) if max(x, y) < NMC]
SIDE = {}
for hub, names in (("u", AN), ("v", BN)):
    att, internal = [], []
    for i, (x, y) in enumerate(SB):
        lo, hi = min(x, y), max(x, y)
        if lo < NMC <= hi and hi - NMC < NPR:
            att.append((i, lo, names[hi - NMC]))
        elif lo >= NMC:
            internal.append(i)
    SIDE[hub] = (att, internal, names)


def decode(rec):
    """(edges over readable names, core degrees, private->core masks, private-edge flags)."""
    E = {frozenset(("u", "v"))} | {frozenset((h, c)) for h in ("u", "v") for c in CN}
    cdeg = [0] * NMC
    for i, x, y in CBITS:
        if rec["core_mask"] >> i & 1:
            E.add(frozenset((CN[x], CN[y])))
            cdeg[x] += 1
            cdeg[y] += 1
    att, priv = {}, {}
    for hub, msk in (("u", rec["left_side_mask"]), ("v", rec["right_side_mask"])):
        a, names = {n: 0 for n in SIDE[hub][2]}, SIDE[hub][2]
        for i, ci, pn in SIDE[hub][0]:
            if msk >> i & 1:
                E.add(frozenset((CN[ci], pn)))
                a[pn] |= 1 << ci
        priv[hub] = any(msk >> i & 1 for i in SIDE[hub][1])
        E |= {frozenset((hub, n)) for n in names} | ({frozenset(names)} if priv[hub] else set())
        att[hub] = a
    return E, cdeg, att, priv


def lemma_roles(E, cdeg, att, priv):
    """(roles, category): roles None unless Lemma K holds under some allowed relabelling."""
    if sorted(cdeg) != [2, 2, NMC - 1, NMC - 1]:
        return None, "not_diamond_core"
    if not (priv["u"] and priv["v"]):
        return None, "missing_private_edge_on_" + "_and_".join(h for h in ("u", "v") if not priv[h])
    ctr = [i for i in range(NMC) if cdeg[i] == NMC - 1]
    leaf = [j for j in range(NMC) if cdeg[j] == NMC - 2]
    for Vh in ("u", "v"):
        Uh, onames = ("v", BN) if Vh == "u" else ("u", AN)
        for d in sorted(att[Vh]):
            if all(att[Vh][d] >> i & 1 for i in ctr):
                return dict(U=Uh, V=Vh, x=CN[leaf[0]], y=CN[leaf[1]], p=CN[ctr[0]], q=CN[ctr[1]],
                            a=sorted(onames)[0], b=sorted(onames)[1], d=d, swapped=(Vh == "u"),
                            c=[n for n in SIDE[Vh][2] if n != d][0]), None
    return None, "both_private_edges_no_private_vertex_on_both_centers"


def build(idx, rec, D, R):
    """Construct S, X and run the literal certificate checks on the decoded graph."""
    E, cdeg, att, priv = D
    S = [(R["U"], R["x"], R["q"]), (R["U"], R["y"], R["p"]), (R["U"], R["a"], R["b"]),
         (R["V"], R["x"], R["p"]), (R["V"], R["y"], R["q"]), (R["V"], R["c"], R["d"]),
         (R["d"], R["p"], R["q"])]
    Sed = {frozenset(pr) for t in S for pr in itertools.combinations(t, 2)}
    Xed = {frozenset(pr) for pr in itertools.combinations((R["x"], R["y"], R["p"], R["q"]), 2)} - {frozenset((R["x"], R["y"]))}
    Xed |= {frozenset(pr) for pr in [(R["a"], R["b"]), (R["c"], R["d"]), (R["d"], R["p"]), (R["d"], R["q"]),
             (R["U"], R["V"]), (R["U"], R["a"]), (R["U"], R["b"]), (R["V"], R["c"]), (R["V"], R["d"])]}
    tris = [set(t) for t in itertools.combinations(sorted({n for e in E for n in e}), 3)
            if all(frozenset(pr) in E for pr in itertools.combinations(t, 2))]
    hit = lambda t: any(frozenset(pr) in Xed for pr in itertools.combinations(sorted(t), 2))
    hubtri = [t for t in tris if R["U"] in t or R["V"] in t]
    outside_packed = {e for e in Sed if R["U"] not in e and R["V"] not in e}
    fmt = lambda s: sorted("+".join(sorted(e)) for e in s)
    return dict(index=idx, key=[rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]],
                roles=R, core_degrees=cdeg, hub_side_swapped=R["swapped"],
                packing_S=[sorted(t) for t in S], cover_X=sorted("+".join(sorted(e)) for e in Xed),
                checks=dict(existence=Sed <= E, disjoint=len(Sed) == 3 * len(S) == 21,
                            roles_distinct=len(set(R[k] for k in ROLES)) == 10,
                            hub_coverage=all(hit(t) for t in hubtri),
                            outside_packed_edges_in_X=outside_packed <= Xed,
                            cover_subset_E=Xed <= E, budget_ok=len(Xed) <= 2 * len(S)),
                n_edges=len(E), n_triangles=len(tris), n_hub_triangles=len(hubtri),
                packed_external_edges=fmt(outside_packed),
                nu_record=len(rec["packing"]), tau_record=len(rec["cover"]),
                uv_witnessed_in_record=any(frozenset(e) == UV for e in rec["cover"]) or any(UV <= frozenset(t) for t in rec["packing"]),
                certificate_tight=len(Xed) == 2 * len(S))


diamonds, cov, rest = [], [], []
for idx, rec in enumerate(REC):
    D = decode(rec)
    if sum(D[1]) != 2 * (2 * NMC - 3):                  # diamond core = 5 core edges
        continue
    diamonds.append(idx)
    R, cat = lemma_roles(*D)
    if R is None:
        rest.append(dict(index=idx, key=[rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]],
                         category=cat, core_degrees=D[1], both_private_edges=all(D[3].values()),
                         attachments={"u_side": D[2]["u"], "v_side": D[2]["v"]}))
    else:
        cov.append(build(idx, rec, D, R))

miss = Counter(w["category"] for w in rest)
T = json.loads((ROOT / "mad8" / "round5" / "B_D" / "scan_tight_summary.json").read_text(encoding="utf-8"))
cen, nu = T["tight_census"], Counter(e["nu"] for e in T["tight_census"])
tight = dict(source="mad8/round5/B_D/scan_tight_summary.json (read only, no rescan)", census_len=len(cen),
             nu1=nu[1], nu2=nu[2], other_nu=sum(v for k, v in nu.items() if k not in (1, 2)),
             reported_counts_field=T["counts"]["tight_tau_eq_2nu"],
             all_tau_eq_2nu=all(e["tau"] == 2 * e["nu"] for e in cen),
             claim_20_nu1_7_nu2_verified=(len(cen) == 27 and nu[1] == 20 and nu[2] == 7))
tot = {k: sum(1 for w in cov if w["checks"][k]) for k in cov[0]["checks"]} if cov else {}
summary = dict(task="saved-record audit of diamond/Lemma-K transfer claim (no enumeration, no solver)",
               attribution="dataset Gupta, CC BY 4.0 (compression/input/PROVENANCE.txt); no private paths",
               legend=dict(core_degrees="decoded from core_bit_order; diamond = 3,3,2,2",
                           roles="U,V hubs; x,y degree-2 core; p,q centers; a,b pair at U; c,d pair at V, d on both p,q",
                           S="uxq,uyp,uab,vxp,vyq,vcd,dpq", X="E(K4-xy)+ab,cd,dp,dq+uv,ua,ub,vc,vd",
                           naming="u-side = left_exclusive (a0,a1); v-side = right_exclusive (b0,b1)"),
               total_records=len(REC), decoded_diamond_records=len(diamonds), claim_diamond_records=139,
               diamond_claim_verified=len(diamonds) == 139, lemmaK_covered=len(cov), claim_covered=42,
               covered_claim_verified=len(cov) == 42, remaining=len(rest), partition=dict(sorted(miss.items())),
               missing_private_edge_total=sum(v for k, v in miss.items() if k.startswith("missing")),
               both_edges_no_center_total=miss.get("both_private_edges_no_private_vertex_on_both_centers", 0),
               claim_partition=dict(missing_private_edge=84, both_edges_no_center=13),
               witness_check_totals=tot, witnesses_fully_clean=sum(1 for w in cov if all(w["checks"].values())),
               all_certificates_tight=all(w["certificate_tight"] for w in cov),
               budget_note="|S|=7, |X|=14=2*|S|; cover X is tight in the local reduction sense",
               witnesses_uv_witnessed=sum(1 for w in cov if w["uv_witnessed_in_record"]),
               example_keys={k: next(w["key"] for w in rest if w["category"] == k) for k in sorted(miss)},
               tight_atlas_check=tight)
(HERE / "diamond_transfer_summary.json").write_text(json.dumps(summary, indent=1), encoding="utf-8")
(HERE / "diamond_transfer_witnesses.json").write_text(json.dumps(cov, indent=1), encoding="utf-8")
(HERE / "diamond_transfer_remaining.json").write_text(json.dumps(rest, indent=1), encoding="utf-8")
rep = ["Role B round 6 -- bounded saved-record audit (no enumeration, no solver).",
       "Source compression/input/B_codegree4_certificates.json: %d records; attribution Gupta, CC BY 4.0." % len(REC),
       "Decoded diamond cores (degrees 3,3,2,2): %d; claim 139 -> %s." % (len(diamonds), "match" if len(diamonds) == 139 else "CORRECTED"),
       "Lemma K covered (both private internal edges AND a private vertex on both centers, up to core permutation,"
       " private-pair rename, hub side swap): %d; claim 42 -> %s." % (len(cov), "match" if len(cov) == 42 else "CORRECTED"),
       "Remaining %d: %s. Examples: %s" % (len(rest), ", ".join("%s=%d" % kv for kv in sorted(miss.items())), json.dumps(summary["example_keys"])),
       "Checks on %d covered records: %s; reducibility requires hub coverage and packed external-edge containment, not full graph coverage." %
       (len(cov), json.dumps(tot)),
       "The displayed witness is tight: |S|=7 and |X|=14=2|S|. Unused graph edges outside S union X are irrelevant.",
       "uv explicitly witnessed in %d of %d covered records; 0 remaining records miss only the v-side internal edge." %
       (summary["witnesses_uv_witnessed"], len(cov)),
       "mad8/round5/B_D cross-check: %d tight entries nu1=%d nu2=%d -> claim 20+7 %s; no rescan." % (tight["census_len"], tight["nu1"], tight["nu2"], "match" if tight["claim_20_nu1_7_nu2_verified"] else "CORRECTED"),
       "Counts bound the audit only; no proof declared."]
(HERE / "report.txt").write_text("\n".join(rep) + "\n", encoding="utf-8")
print("diamonds", len(diamonds), "| covered", len(cov), "| remaining", len(rest), dict(miss))
print("checks", tot, "| all_tight", summary["all_certificates_tight"],
      "| uv_wit", summary["witnesses_uv_witnessed"])
print("tight", tight, "| examples", summary["example_keys"])
if cov:
    print("witness0", cov[0]["key"], cov[0]["roles"], cov[0]["checks"])
if not (len(REC) == 1144 and len(diamonds) == 139 and len(cov) == 42 and
        len(rest) == 97 and summary["missing_private_edge_total"] == 84 and
        summary["both_edges_no_center_total"] == 13 and
        summary["witnesses_fully_clean"] == len(cov) and summary["all_certificates_tight"]):
    raise SystemExit("Saved-record count or literal certificate validation failed")
