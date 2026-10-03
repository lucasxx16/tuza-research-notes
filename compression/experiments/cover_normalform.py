#!/usr/bin/env python3
"""E strengthened normal-form cover.

Claim (to be independently audited): every stored cover X can be normalized so
that its extra rim edges (outside mandatory support R = packing rim edges) are
CORE-only. Reason: an extra rim edge in Ju that is not a core edge has at least
one endpoint in A={6,7}; replacing it by the single u-spoke to that endpoint
keeps Ju residual covered and does not increase |X|. Same on the v side for
C-B / B-B extras. Hence a within-budget cover exists of the form

    X = R  U  D  U  {optional uv}  U  hub-spokes,      D subseteq E(core)\\R

Enumerate all D (<=64 core subsets); per D run the EXACT spoke vertex-cover
optimization (brute 64 subsets per side), options with / without uv. Report the
fewest |D| reaching |X| <= 2|S|, plus off-hub motif classes before/after the
exchange transform (already computed). Saved records only. No new finder.
"""

import json
import sys
import time
from collections import Counter
from itertools import combinations
from pathlib import Path

from analyze_certificates import (
    U, V, COMMON, LEFT, RIGHT, C4, CORE_TO_GLOBAL, CORE_EDGES,
    guaranteed_graph, graph_triangles, triangle_edge_set, literal_reduction,
    classify_triangle_hub, partition_type,
)

HERE = Path(__file__).resolve().parent
CERT_PATH = HERE.parent / "input" / "B_codegree4_certificates.json"
OUT_JSON = HERE / "B_cover_normalform.json"
OUT_REPORT = HERE / "report_cover_normalform.txt"
TRANSFORM_JSON = HERE / "transformed_records.json"

JU_VERTS = (2, 3, 4, 5, 6, 7)
JV_VERTS = (2, 3, 4, 5, 8, 9)
CSET = frozenset(COMMON)
HUBS = (U, V)


def ne(a, b):
    return (min(a, b), max(a, b))


def core_present_edges(core_mask):
    return frozenset(
        ne(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y])
        for x, y in CORE_EDGES if (core_mask >> CORE_EDGES.index((x, y))) & 1
    )


def build_Ju(core_mask, left_mask):
    edges = set()
    for i, (x, y) in enumerate(CORE_EDGES):
        if (core_mask >> i) & 1:
            edges.add(ne(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    SIDE = tuple((c, 4) for c in range(4)) + tuple((c, 5) for c in range(4)) + ((4, 5),)
    for i, (c, ex) in enumerate(SIDE):
        if (left_mask >> i) & 1:
            if c < 4:
                edges.add(ne(CORE_TO_GLOBAL[c], LEFT[ex - 4]))
            else:
                edges.add((6, 7))
    return frozenset(edges)


def build_Jv(core_mask, right_mask):
    edges = set()
    for i, (x, y) in enumerate(CORE_EDGES):
        if (core_mask >> i) & 1:
            edges.add(ne(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    SIDE = tuple((c, 4) for c in range(4)) + tuple((c, 5) for c in range(4)) + ((4, 5),)
    for i, (c, ex) in enumerate(SIDE):
        if (right_mask >> i) & 1:
            if c < 4:
                edges.add(ne(CORE_TO_GLOBAL[c], RIGHT[ex - 4]))
            else:
                edges.add((8, 9))
    return frozenset(edges)


def packing_rim_edges(packing):
    rim = set()
    for tri in packing:
        for a, b in combinations(tri, 2):
            if a not in HUBS and b not in HUBS:
                rim.add(ne(a, b))
    return frozenset(rim)


def min_vc(edges, vertices):
    n = len(vertices)
    vset = set(vertices)
    valid = [(a, b) for a, b in edges if a in vset and b in vset]
    if not valid:
        return (0, frozenset())
    best, bset = n + 1, None
    for mask in range(1 << n):
        sz = mask.bit_count()
        if sz >= best:
            continue
        subset = frozenset(vertices[i] for i in range(n) if (mask >> i) & 1)
        if all(a in subset or b in subset for a, b in valid):
            best, bset = sz, subset
    return (best, bset)


def all_vc_by_size(edges, vertices):
    n = len(vertices)
    vset = set(vertices)
    valid = [(a, b) for a, b in edges if a in vset and b in vset]
    res = {}
    if not valid:
        return {0: [frozenset()]}
    for mask in range(1 << n):
        sz = mask.bit_count()
        subset = frozenset(vertices[i] for i in range(n) if (mask >> i) & 1)
        if all(a in subset or b in subset for a, b in valid):
            res.setdefault(sz, []).append(subset)
    return res


def exact_forced(core, left, right, forced):
    """Best |X| using exactly 'forced' rim edges + optional uv + hub spokes.
    Returns (cost, method, Qu, Qv, uv_used) or None."""
    Ju = build_Ju(core, left)
    Jv = build_Jv(core, right)
    Ju_res = frozenset(e for e in Ju if e not in forced)
    Jv_res = frozenset(e for e in Jv if e not in forced)
    base = len(forced)

    vc_u, su = min_vc(Ju_res, JU_VERTS)
    vc_v, sv = min_vc(Jv_res, JV_VERTS)
    opt1 = base + 1 + vc_u + vc_v
    best = (opt1, 'opt1_uv', su, sv, True)

    ju = all_vc_by_size(Ju_res, JU_VERTS)
    jv = all_vc_by_size(Jv_res, JV_VERTS)
    best2, pair2 = None, None
    for su_ in sorted(ju):
        if best2 is not None and su_ >= best2:
            break
        for sv_ in sorted(jv):
            if su_ + sv_ >= (best2 if best2 is not None else 10**9):
                break
            for Qu in ju[su_]:
                need = CSET - Qu
                for Qv in jv[sv_]:
                    if need <= Qv:
                        tot = su_ + sv_
                        if best2 is None or tot < best2:
                            best2, pair2 = tot, (Qu, Qv)
                        break
    if best2 is not None:
        opt2 = base + best2
        if opt2 <= opt1:
            Qu, Qv = pair2
            best = (opt2, 'opt2_no_uv', Qu, Qv, False)
    return best


def build_witness(forced, method, Qu, Qv, uv_used):
    X = set(forced)
    if uv_used:
        X.add((U, V))
    for x in Qu:
        X.add(ne(U, x))
    for y in Qv:
        X.add(ne(V, y))
    return frozenset(X)


def is_offhub(t):
    return all(v not in HUBS for v in t)


def motif(S):
    hub = Counter(classify_triangle_hub(t) for t in S)
    return {
        "off": hub.get("neither", 0),
        "off_partition_types": sorted(partition_type(t) for t in S if is_offhub(t)),
    }


def full_valid(core, left, right, packing, cover):
    p = tuple(tuple(t) for t in packing)
    c = frozenset(tuple(e) for e in cover)
    return all(literal_reduction(core, left, right, p, c, cm) for cm in range(16))


def main():
    with open(CERT_PATH, "r", encoding="utf-8") as f:
        records = json.load(f)["records"]
    n = len(records)

    feasible = 0
    infeasible_keys = []
    invalid = []
    dmin_dist = Counter()      # fewest |D| reaching <=budget
    bestcost_eps = Counter()   # epsilon = 2|S|-bestcost
    method_dist = Counter()
    per_record = []

    t0 = time.time()
    for idx, rec in enumerate(records):
        core, left, right = rec["core_mask"], rec["left_side_mask"], rec["right_side_mask"]
        S = frozenset(tuple(t) for t in rec["packing"])
        budget = 2 * len(S)
        key = (core, left, right)

        R = packing_rim_edges(S)
        core_present = core_present_edges(core)
        cand = sorted(core_present - R)
        m = len(cand)

        best_cost = budget + 1
        best_entry = None  # (|D|, Dset, method,Qu,Qv,uv,X)
        fewest_D_within = None
        # enumerate D subsets, ordered by popcount for fewest-D reporting
        for mask in range(1 << m):
            D = frozenset(cand[i] for i in range(m) if (mask >> i) & 1)
            forced = frozenset(set(R) | set(D))
            res = exact_forced(core, left, right, forced)
            if res is None:
                continue
            cost, method, Qu, Qv, uv = res
            dsz = len(D)
            if cost <= budget:
                if fewest_D_within is None or (dsz, cost) < (fewest_D_within[0], fewest_D_within[1]):
                    fewest_D_within = (dsz, cost, D, method, Qu, Qv, uv)
            if cost < best_cost or (cost == best_cost and best_entry and dsz < best_entry[0]):
                best_cost = cost
                best_entry = (dsz, cost, D, method, Qu, Qv, uv)

        ok = fewest_D_within is not None
        chosen = fewest_D_within if ok else best_entry
        if ok:
            feasible += 1
            dmin_dist[chosen[0]] += 1
            method_dist[chosen[3]] += 1
            bestcost_eps[budget - chosen[1]] += 1

        X_final = build_witness(frozenset(set(R) | set(chosen[2])), chosen[3],
                                chosen[4], chosen[5], chosen[6]) if chosen else None
        valid = X_final is not None and full_valid(core, left, right, S, X_final)
        if not valid:
            invalid.append(list(key))
        if not ok:
            infeasible_keys.append(list(key))

        per_record.append({
            "index": idx, "key": list(key), "S_size": len(S), "budget": budget,
            "R_size": len(R), "core_extra_candidates": m,
            "within_budget": ok,
            "fewest_D_for_budget": (chosen[0] if ok else None),
            "best_cost": (chosen[1] if chosen else None),
            "epsilon": (budget - chosen[1] if (ok and chosen) else None),
            "method": (chosen[3] if chosen else None),
            "D_edges": (sorted(list(e) for e in chosen[2]) if chosen else None),
            "cover_size": (len(X_final) if X_final else None),
            "cover": (sorted(list(e) for e in X_final) if X_final else None),
            "valid_all16": valid,
        })

    print(f"Elapsed {time.time()-t0:.1f}s")
    print(f"Feasible (within budget): {feasible}/{n}")
    print(f"Infeasible: {len(infeasible_keys)} {infeasible_keys[:5]}")
    print(f"Invalid witnesses: {len(invalid)} {invalid[:5]}")
    print(f"Fewest |D| reaching budget: {dict(sorted(dmin_dist.items()))}")
    print(f"Epsilon (budget - returned cover size): {dict(sorted(bestcost_eps.items()))}")
    print(f"Selected method (returned): {dict(method_dist)}")

    # ── Off-hub motif classes before/after exchange (from transformed_records) ──
    off_before = Counter(); off_after = Counter()
    motif_before = Counter(); motif_after = Counter()
    with open(TRANSFORM_JSON, "r", encoding="utf-8") as f:
        tr = json.load(f)["per_record"]
    for r in tr:
        o0 = r["original"]["off_hubs"]
        o1 = r["best_reachable"]["off_hubs_min"]
        off_before[o0] += 1; off_after[o1] += 1
        mb = r["original"]["motif"]; ma = r["best_reachable"]["motif"]
        # motif class key = off + sorted off_partition_types
        kb = (mb["off"], tuple(mb.get("off_partition_types", [])))
        ka = (ma["off"], tuple(ma.get("off_partition_types", [])))
        motif_before[kb] += 1; motif_after[ka] += 1

    print(f"\nOff-hub BEFORE exchange: {dict(sorted(off_before.items()))}")
    print(f"Off-hub AFTER  exchange: {dict(sorted(off_after.items()))}")
    print(f"Distinct off-hub motif classes BEFORE: {len(motif_before)}")
    print(f"Distinct off-hub motif classes AFTER:  {len(motif_after)}")

    out = {
        "description": "Normal-form cover: extra rim D restricted to core edges; enumerate <=64 D, "
                       "exact brute-64 spoke VC with/without uv.",
        "claim": "Should succeed for every saved S by normalization of stored X "
                 "(C-A/A-A extra rim -> one u-spoke; C-B/B-B -> one v-spoke).",
        "summary": {
            "total": n,
            "feasible_within_budget": feasible,
            "infeasible_count": len(infeasible_keys),
            "infeasible_keys": infeasible_keys,
            "invalid_witness_count": len(invalid),
            "fewest_D_distribution": {str(k): v for k, v in sorted(dmin_dist.items())},
            "epsilon_distribution": {str(k): v for k, v in sorted(bestcost_eps.items())},
            "method_distribution": dict(method_dist),
            "interpretation": "fewest_D_distribution = SMALLEST |D| reaching budget; "
                              "per-record cover/method are the FIRST such returned cover "
                              "(labels: returned cover size / selected method). Earliest "
                              "feasible |D| does NOT prove a globally smallest cover.",
        },
        "offhub_motif_classes": {
            "exchange_note": "off-hub counts/motifs are BEFORE vs AFTER the hub-free "
                             "triangle exchange transform (separate E task).",
            "before_exchange": {f"{k[0]}:{''.join(k[1]) or '-'}": v for k, v in sorted(motif_before.items(), key=lambda x: (-x[0][0], x[0][1]))},
            "after_exchange": {f"{k[0]}:{''.join(k[1]) or '-'}": v for k, v in sorted(motif_after.items(), key=lambda x: (-x[0][0], x[0][1]))},
            "distinct_classes_before": len(motif_before),
            "distinct_classes_after": len(motif_after),
        },
        "per_record": per_record,
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    # concise report
    L = ["=== E normal-form cover (core-only extra rim D) ===\n"]
    L.append("Forced support R = packing rim edges; extra rim D subset of E(core)\\R (<=64).")
    L.append("Per D: exact spoke vertex cover (brute 64/side), options with / without uv.")
    L.append(f"\nFeasible within budget 2|S|: {feasible}/{n}")
    L.append(f"Infeasible: {len(infeasible_keys)}   Invalid witnesses: {len(invalid)}")
    L.append(f"\nFewest |D| needed to reach budget:")
    L.append("(earliest feasible |D| reaches budget; does NOT prove the returned"
             " cover is the globally smallest over all admissible X)")
    for k in sorted(dmin_dist):
        L.append(f"  |D|={k}: {dmin_dist[k]} records ({100*dmin_dist[k]/n:.1f}%)")
    L.append(f"\nEpsilon (budget - returned cover size):")
    for k in sorted(bestcost_eps):
        L.append(f"  eps={k}: {bestcost_eps[k]} records")
    L.append(f"\nSelected method (returned): opt1_uv={method_dist.get('opt1_uv',0)}  opt2_no_uv={method_dist.get('opt2_no_uv',0)}")
    L.append(f"\n--- Off-hub motif classes (before vs after exchange transform) ---")
    L.append(f"Distinct classes BEFORE: {len(motif_before)}   AFTER: {len(motif_after)}")
    L.append(f"off-hub count BEFORE: {dict(sorted(off_before.items()))}")
    L.append(f"off-hub count AFTER:  {dict(sorted(off_after.items()))}")
    L.append(f"\nMotif class = (off-hub count : sorted off-triangle partition types). Record counts:")
    all_keys = sorted(set(motif_before) | set(motif_after), key=lambda x: (-x[0], x[1]))
    L.append(f"  {'class':<16}{'before':>8}{'after':>8}")
    for k in all_keys:
        lbl = f"{k[0]}:{''.join(k[1]) or '-'}"
        L.append(f"  {lbl:<16}{motif_before.get(k,0):>8}{motif_after.get(k,0):>8}")
    with open(OUT_REPORT, "w", encoding="utf-8") as f:
        f.write("\n".join(L))

    print("\nSaved: B_cover_normalform.json, report_cover_normalform.txt")
    return 0


if __name__ == "__main__":
    sys.exit(main())
