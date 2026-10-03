#!/usr/bin/env python3
"""Role B: Bounded certificate transform via hub-free triangle exchange.

For each SAVED record only (no new graphs, no finder, no census).

EXCHANGE (per E spec):
  For an off-hub (hub-free) triangle xyz in S, pick h in {0,1} and the
  unordered pair {x,y} (= xyz minus the kept-aside vertex z) such that edges
  hx, hy exist in the guaranteed graph AND are unused by S \\ {xyz}.
  Replace xyz -> hxy (keep xy).
  Replace X by (X \\ {xz, yz}) U {kz : k in {0,1}, kz exists in graph}.
  xy is kept in X. Preserves |S|; never increases |X|; removes exactly one
  off-hub triangle (off-hub count strictly decreases => DAG, depth <= 3).

This memoizes states and explores ALL exchanges recursively to the minimum
reachable off-hub count, reconstructs a full (S*,X*) witness, and validates
each original and each transformed certificate independently over all 16
A-B cross-mask extensions.

Bound: 60 s per record; over-budget records are reported UNFINISHED (never
have branches dropped silently).
"""

import json
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path

# Reuse the independently-written verifier primitives (no trust in finder).
from analyze_certificates import (
    U, V, COMMON, LEFT, RIGHT,
    guaranteed_graph, graph_triangles, triangle_edge_set,
    literal_reduction, classify_triangle_hub, partition_type,
)

HERE = Path(__file__).resolve().parent
CERT_PATH = HERE.parent / "input" / "B_codegree4_certificates.json"
OUT_RECORDS = HERE / "transformed_records.json"
OUT_STATS = HERE / "exchange_stats.json"
OUT_REPORT = HERE / "report_transform.txt"

HUBS = (U, V)
PER_RECORD_BUDGET_S = 60.0
MAX_STATES_PER_RECORD = 200000  # hard structural backstop


def norm_edge(a, b):
    return (min(a, b), max(a, b))


def is_offhub(tri):
    return tri[0] not in HUBS and tri[1] not in HUBS and tri[2] not in HUBS


def off_count(S):
    return sum(1 for t in S if is_offhub(t))


def motif(S):
    """Structural motif signature of a packing (order-independent)."""
    hub = Counter(classify_triangle_hub(t) for t in S)
    off_types = sorted(partition_type(t) for t in S if is_offhub(t))
    return {
        "size": len(S),
        "both": hub.get("both", 0),
        "u": hub.get("u", 0),
        "v": hub.get("v", 0),
        "off": hub.get("neither", 0),
        "off_partition_types": off_types,
    }


def used_edges_excluding(S, drop):
    u = set()
    for t in S:
        if t == drop:
            continue
        u |= set(triangle_edge_set(t))
    return u


def gen_exchanges(core, left, right, base_edges, S, X):
    """Yield (S2, X2, mapping) for every valid single exchange off state (S,X).

    Quick structural checks only; full hub-triangle coverage is verified later
    on the reconstructed witnesses.
    """
    out = []
    for t in S:
        if not is_offhub(t):
            continue
        a, b, c = t  # sorted tuple, all non-hub
        te = set(triangle_edge_set(t))
        # choose the vertex z that is dropped from the new triangle; pair = rest
        for z in (a, b, c):
            pair = [w for w in (a, b, c) if w != z]
            x, y = pair[0], pair[1]
            used = used_edges_excluding(S, t)
            for h in HUBS:
                e_hx = norm_edge(h, x)
                e_hy = norm_edge(h, y)
                # hx, hy must exist and be unused by S \\ {xyz}
                if e_hx not in base_edges or e_hy not in base_edges:
                    continue
                if e_hx in used or e_hy in used:
                    continue
                new_t = tuple(sorted((h, x, y)))
                if new_t in S:
                    continue
                # new triangle must be a real triangle in base graph
                if te and new_t is None:
                    continue
                S2 = frozenset([s for s in S if s != t] + [new_t])
                # build X2
                e_xz = norm_edge(x, z)
                e_yz = norm_edge(y, z)
                X2 = set(X)
                X2.discard(e_xz)
                X2.discard(e_yz)
                added = []
                for k in HUBS:
                    e_kz = norm_edge(k, z)
                    if e_kz in base_edges:
                        X2.add(e_kz)
                        added.append(list(e_kz))
                X2 = frozenset(X2)
                # invariants of the spec
                if len(S2) != len(S):
                    continue
                if len(X2) > len(X):
                    continue
                if len(X2) > 2 * len(S2):
                    continue
                mapping = {
                    "removed_triangle": list(t),
                    "hub": h,
                    "pair": [x, y],
                    "kept_aside": z,
                    "new_triangle": list(new_t),
                    "X_removed": [list(e_xz), list(e_yz)],
                    "X_added": added,
                }
                out.append((S2, X2, mapping))
    return out


def solve_state(core, left, right, base_edges, S, X, deadline, memo, ctr):
    """Memoized DFS -> (min_off, finalS, finalX, trace). Raises Timeout."""
    ctr[0] += 1
    if ctr[0] > MAX_STATES_PER_RECORD:
        raise TimeoutError("state cap")
    if time.time() > deadline:
        raise TimeoutError("time budget")
    key = (core, left, right, S, X)
    hit = memo.get(key)
    if hit is not None:
        return hit
    best_off = off_count(S)
    bestS, bestX, best_trace = S, X, []
    for (S2, X2, m) in gen_exchanges(core, left, right, base_edges, S, X):
        r_off, r_S, r_X, r_trace = solve_state(
            core, left, right, base_edges, S2, X2, deadline, memo, ctr
        )
        if (r_off < best_off or
            (r_off == best_off and (len(r_X) < len(bestX) or
             (len(r_X) == len(bestX) and len(r_trace) + 1 < len(best_trace))))):
            best_off = r_off
            bestS, bestX = r_S, r_X
            best_trace = [m] + r_trace
    res = (best_off, bestS, bestX, best_trace)
    memo[key] = res
    return res


def full_valid(core, left, right, packing, cover):
    """Independent verification across all 16 cross-mask extensions."""
    p = tuple(tuple(t) for t in packing)
    c = frozenset(tuple(e) for e in cover)
    for cm in range(16):
        if not literal_reduction(core, left, right, p, c, cm):
            return False
    return True


def main():
    with open(CERT_PATH, "r", encoding="utf-8") as f:
        doc = json.load(f)
    records = doc["records"]
    n = len(records)

    # ── BASELINE (before any transform) ───────────────────────────────────────
    baseline_off = Counter()
    for rec in records:
        S0 = frozenset(tuple(t) for t in rec["packing"])
        baseline_off[off_count(S0)] += 1
    print("=== BASELINE (original saved packings) ===")
    for k in sorted(baseline_off):
        print(f"  off-hub {k}: {baseline_off[k]} records")
    total_off = sum(k * v for k, v in baseline_off.items())
    n_with_off = sum(v for k, v in baseline_off.items() if k > 0)
    print(f"  total off-hub triangles: {total_off}; records with >=1: {n_with_off}")

    # ── TRANSFORM ─────────────────────────────────────────────────────────────
    memo = {}
    per_record = []
    final_off_dist = Counter()
    depth_dist = Counter()
    improved = 0
    stuck = 0
    already_zero = 0
    timeout_keys = []
    invalid_orig = []
    invalid_final = []
    xmax_change = Counter()
    motifs_final = Counter()
    total_states = 0
    ex_total = 0

    t0 = time.time()
    for idx, rec in enumerate(records):
        core = rec["core_mask"]
        left = rec["left_side_mask"]
        right = rec["right_side_mask"]
        S0 = frozenset(tuple(t) for t in rec["packing"])
        X0 = frozenset(tuple(e) for e in rec["cover"])
        key = (core, left, right)
        off0 = off_count(S0)
        valid0 = full_valid(core, left, right, S0, X0)
        if not valid0:
            invalid_orig.append(list(key))

        base_edges = guaranteed_graph(core, left, right, 0)
        deadline = time.time() + PER_RECORD_BUDGET_S
        ctr = [0]
        status = "finished"
        try:
            min_off, fS, fX, trace = solve_state(
                core, left, right, base_edges, S0, X0, deadline, memo, ctr
            )
        except TimeoutError:
            status = "unfinished"
            min_off = off0
            fS, fX, trace = S0, X0, []
            timeout_keys.append(list(key))
        total_states += ctr[0]

        validf = full_valid(core, left, right, fS, fX)
        if not validf:
            invalid_final.append(list(key))

        ex_total += len(trace)
        final_off_dist[min_off] += 1
        depth_dist[len(trace)] += 1
        xmax_change[len(fX) - len(X0)] += 1
        motifs_final[json.dumps(motif(fS), sort_keys=True)] += 1
        if off0 == 0:
            already_zero += 1
        elif min_off == 0:
            improved += 1
        elif min_off < off0:
            improved += 1
        elif min_off == off0:
            stuck += 1

        per_record.append({
            "index": idx,
            "key": list(key),
            "status": status,
            "original": {
                "packing": sorted(list(t) for t in S0),
                "cover": sorted(list(e) for e in X0),
                "off_hubs": off0,
                "cover_size": len(X0),
                "motif": motif(S0),
                "valid_all16": valid0,
            },
            "best_reachable": {
                "off_hubs_min": min_off,
                "packing": sorted(list(t) for t in fS),
                "cover": sorted(list(e) for e in fX),
                "cover_size": len(fX),
                "motif": motif(fS),
                "valid_all16": validf,
                "exchanges": trace,
                "depth": len(trace),
            },
            "improved": (min_off < off0),
            "states_explored": ctr[0],
        })

        if idx % 200 == 0:
            print(f"  processed {idx}/{n} (elapsed {time.time()-t0:.1f}s, memo={len(memo)})")

    print(f"\nDone in {time.time()-t0:.1f}s. memo states={len(memo)}")

    # ── SUMMARY ───────────────────────────────────────────────────────────────
    print("\n=== TRANSFORM RESULTS ===")
    print(f"  Final min off-hub distribution: {dict(sorted(final_off_dist.items()))}")
    print(f"  Improved (off decreased): {improved}")
    print(f"  Stuck (could not remove any off-hub): {stuck}")
    print(f"  Already zero off-hub: {already_zero}")
    print(f"  Unfinished (over 60s budget): {len(timeout_keys)}")
    print(f"  Invalid ORIGINAL certs: {len(invalid_orig)}")
    print(f"  Invalid FINAL certs: {len(invalid_final)}")
    print(f"  |X| change distribution (final-original): {dict(sorted(xmax_change.items()))}")
    print(f"  Total exchanges applied across all: {ex_total}")
    print(f"  Path depth distribution: {dict(sorted(depth_dist.items()))}")

    # ── SAVE ──────────────────────────────────────────────────────────────────
    stats = {
        "baseline_off_hubs_distribution": {str(k): v for k, v in sorted(baseline_off.items())},
        "baseline_total_off_hubs": total_off,
        "baseline_records_with_offhub": n_with_off,
        "final_min_off_hubs_distribution": {str(k): v for k, v in sorted(final_off_dist.items())},
        "improved_count": improved,
        "stuck_count": stuck,
        "already_zero_count": already_zero,
        "unfinished_count": len(timeout_keys),
        "unfinished_keys": timeout_keys,
        "invalid_original_count": len(invalid_orig),
        "invalid_original_keys": invalid_orig,
        "invalid_final_count": len(invalid_final),
        "invalid_final_keys": invalid_final,
        "cover_size_change_distribution": {str(k): v for k, v in sorted(xmax_change.items())},
        "total_exchanges": ex_total,
        "path_depth_distribution": {str(k): v for k, v in sorted(depth_dist.items())},
        "memo_states": len(memo),
        "distinct_final_motifs": len(motifs_final),
        "final_motif_frequencies": motifs_final.most_common(),
    }
    with open(OUT_STATS, "w", encoding="utf-8") as f:
        json.dump(stats, f, indent=2)
    with open(OUT_RECORDS, "w", encoding="utf-8") as f:
        json.dump({"per_record": per_record}, f, indent=2)

    # ── REPORT ────────────────────────────────────────────────────────────────
    L = []
    L.append("=== E-transform: Hub-free Triangle Exchange (Bounded, Saved Certs Only) ===\n")
    L.append("Exchange: off-hub xyz -> hxy (h in {0,1}); X -> (X\\{xz,yz}) U {kz: kz exists}.")
    L.append("Keeps |S|, never increases |X|, removes exactly one off-hub triangle.")
    L.append("Recursive all-exchange search, memoized, validated over all 16 cross masks.\n")
    L.append("--- BASELINE (before transform) ---")
    L.append(f"  Records with >=1 off-hub triangle: {n_with_off}/{n}")
    L.append(f"  Total off-hub triangles: {total_off}")
    for k in sorted(baseline_off):
        L.append(f"    off={k}: {baseline_off[k]} records")
    L.append("\n--- RESULT (minimum reachable off-hub count) ---")
    for k in sorted(final_off_dist):
        L.append(f"    off={k}: {final_off_dist[k]} records")
    L.append(f"\n  Improved: {improved}")
    L.append(f"  Stuck (no off-hub removable): {stuck}")
    L.append(f"  Already zero: {already_zero}")
    L.append(f"  Unfinished (>60s): {len(timeout_keys)}")
    L.append(f"  Invalid original certificates: {len(invalid_orig)}")
    L.append(f"  Invalid final certificates: {len(invalid_final)}")
    L.append(f"  Total exchanges applied: {ex_total}")
    L.append(f"  Path depths: {dict(sorted(depth_dist.items()))}")
    L.append(f"  |X| change (final-original): {dict(sorted(xmax_change.items()))}")
    L.append(f"  Distinct final motifs: {len(motifs_final)}")
    L.append("\n--- FINAL MOTIF SIGNATURES (top) ---")
    for mj, cnt in motifs_final.most_common(20):
        m = json.loads(mj)
        L.append(f"    {m['off']}off sz{m['size']} b{m['both']}u{m['u']}v{m['v']} "
                 f"types={''.join(m['off_partition_types']) or '-'}: {cnt} recs")
    with open(OUT_REPORT, "w", encoding="utf-8") as f:
        f.write("\n".join(L))

    print("\nSaved: transformed_records.json, exchange_stats.json, report_transform.txt")
    return 0


class TimeoutError(Exception):
    pass


if __name__ == "__main__":
    sys.exit(main())
