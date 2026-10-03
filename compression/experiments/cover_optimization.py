#!/usr/bin/env python3
"""Task E-targeted: Optimized cover construction for saved packings.

For each stored packing S:
  R = union of rim edges of S (edges not incident to u or v)
  Ju = induced rim subgraph on C+A = {2,3,4,5,6,7}
  Jv = induced rim subgraph on C+B = {2,3,4,5,8,9}

  Option1 (with uv): |R| + 1 + vc(Ju-R) + vc(Jv-R)
  Option2 (without uv): min |Qu|+|Qv| over joint VCs with Qu∪Qv >= C
  optimal = min(Option1, Option2)
  Test: optimal <= 2|S|

Bounded brute-force: 64 subsets per vertex cover. No solvers.
"""

from collections import Counter, defaultdict
from itertools import combinations
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CERT_PATH = HERE.parent / "input" / "B_codegree4_certificates.json"
OUTPUT_JSON = HERE / "B_cover_optimization.json"
REPORT_ADDENDUM = HERE / "report_cover_optimization.txt"

# ─── Schema constants ───────────────────────────────────────────────────────────
U, V = 0, 1
COMMON = (2, 3, 4, 5)
LEFT = (6, 7)
RIGHT = (8, 9)
ALL_VERTICES = tuple(range(10))
C4 = tuple(range(4))
CORE_TO_GLOBAL = {c: c + 2 for c in C4}
CORE_EDGES_LOCAL = tuple(combinations(C4, 2))  # 6 core edges
SIDE_EDGES_LOCAL = tuple((c, 4) for c in C4) + tuple((c, 5) for c in C4) + ((4, 5),)  # 9 side edges

# Vertex sets for Ju and Jv
JU_VERTS = (2, 3, 4, 5, 6, 7)  # C ∪ A (6 vertices, 64 subsets)
JV_VERTS = (2, 3, 4, 5, 8, 9)  # C ∪ B


def normalize_edge(a, b):
    return (min(a, b), max(a, b))


def build_Ju(core_mask, left_mask):
    """Compute edge set of Ju: rim edges in guaranteed graph on C∪A."""
    edges = set()
    # Core edges between common vertices
    for i, (x, y) in enumerate(CORE_EDGES_LOCAL):
        if (core_mask >> i) & 1:
            edges.add(normalize_edge(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    # Left side edges: common-to-A-exclusive or A-A
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (left_mask >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                ga = LEFT[ex - 4]  # 4→6, 5→7
                edges.add(normalize_edge(gc, ga))
            else:
                edges.add(normalize_edge(6, 7))  # A-A edge
    return frozenset(edges)


def build_Jv(core_mask, right_mask):
    """Compute edge set of Jv: rim edges in guaranteed graph on C∪B."""
    edges = set()
    for i, (x, y) in enumerate(CORE_EDGES_LOCAL):
        if (core_mask >> i) & 1:
            edges.add(normalize_edge(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (right_mask >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                gb = RIGHT[ex - 4]  # 4→8, 5→9
                edges.add(normalize_edge(gc, gb))
            else:
                edges.add(normalize_edge(8, 9))  # B-B edge
    return frozenset(edges)


def packing_rim_edges(packing):
    """R = all non-hub edges used by packing triangles."""
    rim = set()
    for tri in packing:
        for a, b in combinations(tri, 2):
            if a != U and a != V and b != U and b != V:
                rim.add(normalize_edge(a, b))
    return frozenset(rim)


def min_vertex_cover(edges, vertices):
    """Minimum vertex cover by brute-force over all 2^n subsets.
    vertices: tuple of vertex labels (max 6).
    edges: frozenset of (x,y) pairs among those vertices.
    Returns (min_size, all_min_covers_as_sets).
    """
    n = len(vertices)
    vset = set(vertices)
    # Validate edges are within vertices
    valid_edges = [(a, b) for a, b in edges if a in vset and b in vset]
    if not valid_edges:
        return 0, [frozenset()]

    best_size = n
    best_covers = []
    for mask in range(1 << n):
        subset = frozenset(vertices[i] for i in range(n) if (mask >> i) & 1)
        sz = len(subset)
        if sz > best_size:
            continue
        # Check if this is a valid vertex cover
        is_vc = all(a in subset or b in subset for a, b in valid_edges)
        if is_vc:
            if sz < best_size:
                best_size = sz
                best_covers = [subset]
            elif sz == best_size:
                best_covers.append(subset)
    return best_size, best_covers


def all_vertex_covers(edges, vertices):
    """Return all vertex covers as a dict size -> list of frozensets."""
    n = len(vertices)
    vset = set(vertices)
    valid_edges = [(a, b) for a, b in edges if a in vset and b in vset]
    covers_by_size = defaultdict(list)
    for mask in range(1 << n):
        subset = frozenset(vertices[i] for i in range(n) if (mask >> i) & 1)
        is_vc = all(a in subset or b in subset for a, b in valid_edges)
        if is_vc:
            covers_by_size[len(subset)].append(subset)
    return covers_by_size


def option1_cost(R, Ju_res, Jv_res):
    """Cost with uv in cover: |R| + 1 + vc(Ju-R) + vc(Jv-R)."""
    vc_u, _ = min_vertex_cover(Ju_res, JU_VERTS)
    vc_v, _ = min_vertex_cover(Jv_res, JV_VERTS)
    return len(R) + 1 + vc_u + vc_v


def option1_witness(R, Ju_res, Jv_res):
    """Build witness cover for Option 1."""
    vc_u_size, vc_u_covers = min_vertex_cover(Ju_res, JU_VERTS)
    vc_v_size, vc_v_covers = min_vertex_cover(Jv_res, JV_VERTS)
    # Pick first minimum cover
    Qu = vc_u_covers[0]
    Qv = vc_v_covers[0]
    # X = R ∪ {uv} ∪ {(u,x) for x in Qu} ∪ {(v,y) for y in Qv}
    X = set(R)
    X.add((U, V))
    for x in Qu:
        X.add(normalize_edge(U, x))
    for y in Qv:
        X.add(normalize_edge(V, y))
    return X


def option2_cost(R, Ju_res, Jv_res):
    """Cost without uv: min |R| + |Qu| + |Qv| s.t. Qu is VC of Ju_res,
    Qv is VC of Jv_res, Qu∪Qv ⊇ C."""
    Cset = set(COMMON)
    # Enumerate all covers for both sides
    ju_covers = all_vertex_covers(Ju_res, JU_VERTS)
    jv_covers = all_vertex_covers(Jv_res, JV_VERTS)

    best = len(JU_VERTS) + len(JV_VERTS) + 1  # upper bound
    best_pair = None

    for sz_u in sorted(ju_covers.keys()):
        if sz_u >= best:
            break
        for sz_v in sorted(jv_covers.keys()):
            if sz_u + sz_v >= best:
                break
            for Qu in ju_covers[sz_u]:
                # Check which common vertices Qu covers
                qu_c = Qu & Cset
                need = Cset - qu_c  # common vertices Qv must cover
                if need <= set(JV_VERTS):
                    for Qv in jv_covers[sz_v]:
                        if need <= Qv:
                            total = sz_u + sz_v
                            if total < best:
                                best = total
                                best_pair = (Qu, Qv)
                            break  # first valid Qv at this size
                if best == sz_u + sz_v:
                    break
        if best <= sz_u and best_pair:
            break

    if best_pair is None:
        return None, None
    return len(R) + best, best_pair


def option2_witness(R, Ju_res, Jv_res, best_pair):
    """Build witness cover for Option 2."""
    Qu, Qv = best_pair
    X = set(R)
    for x in Qu:
        X.add(normalize_edge(U, x))
    for y in Qv:
        X.add(normalize_edge(V, y))
    return X


def verify_cover(core, left, right, packing, X, cross_mask=0):
    """Verify X is a valid cover for this packing under given cross_mask."""
    from analyze_certificates import (
        guaranteed_graph, graph_triangles, triangle_edge_set, literal_reduction
    )
    edges = guaranteed_graph(core, left, right, cross_mask)
    X_set = frozenset(X)
    # Check subset
    if not X_set <= edges:
        return False
    # Check |X| <= 2|packing|
    if len(X_set) > 2 * len(packing):
        return False
    # Check packing disjoint within edges
    used = set()
    for tri in packing:
        te = triangle_edge_set(tri)
        if not te <= edges or used & te:
            return False
        used.update(te)
    # Check hub-triangle coverage
    for tri in graph_triangles(edges):
        if (U in tri or V in tri):
            if not (triangle_edge_set(tri) & X_set):
                return False
    # Check packing rim edges in cover
    for tri in packing:
        for edge in triangle_edge_set(tri):
            if U not in edge and V not in edge:
                if edge not in X_set:
                    return False
    return True


def classify_triangle_partition(tri):
    """Classify non-hub triangle by C/A/B partition."""
    cats = []
    for v in tri:
        if v in COMMON:
            cats.append('C')
        elif v in LEFT:
            cats.append('A')
        elif v in RIGHT:
            cats.append('B')
    return ''.join(sorted(cats))


def classify_triangle_hub(tri):
    has_u = U in tri
    has_v = V in tri
    if has_u and has_v: return 'both'
    if has_u: return 'u'
    if has_v: return 'v'
    return 'neither'


# ─── Main ───────────────────────────────────────────────────────────────────────

def main():
    print("Loading records...")
    with open(CERT_PATH, 'r', encoding='utf-8') as f:
        doc = json.load(f)
    records = doc['records']
    print(f"  {len(records)} records loaded")

    results = []
    fail_keys = []
    # Grouped accumulators
    group_stats = defaultdict(lambda: {'count': 0, 'epsilons': [], 'opt_sizes': []})

    print("Running cover optimization...")
    for idx, rec in enumerate(records):
        core = rec['core_mask']
        left = rec['left_side_mask']
        right = rec['right_side_mask']
        packing = [tuple(t) for t in rec['packing']]
        cover_stored = frozenset(tuple(e) for e in rec['cover'])

        key = (core, left, right)
        S_size = len(packing)
        budget = 2 * S_size

        # Step 1: Compute R (forced rim)
        R = packing_rim_edges(packing)

        # Step 2: Compute Ju, Jv
        Ju = build_Ju(core, left)
        Jv = build_Jv(core, right)

        # Step 3: Residual graphs (edges not in R)
        Ju_res = frozenset(e for e in Ju if e not in R)
        Jv_res = frozenset(e for e in Jv if e not in R)

        # Step 4: Option 1 (with uv)
        opt1 = option1_cost(R, Ju_res, Jv_res)

        # Step 5: Option 2 (without uv)
        opt2_val, opt2_pair = option2_cost(R, Ju_res, Jv_res)
        if opt2_val is None:
            opt2 = budget + 1  # infeasible
        else:
            opt2 = opt2_val

        # Optimal
        optimal = min(opt1, opt2)
        feasible = optimal <= budget
        epsilon = budget - optimal

        # Build witness
        if opt1 <= opt2 and opt1 <= budget:
            witness = option1_witness(R, Ju_res, Jv_res)
            method = 'opt1_uv'
            X_size = len(witness)
        elif opt2_pair and opt2 <= budget:
            witness = option2_witness(R, Ju_res, Jv_res, opt2_pair)
            method = 'opt2_no_uv'
            X_size = len(witness)
        elif opt1 <= budget:
            witness = option1_witness(R, Ju_res, Jv_res)
            method = 'opt1_uv'
            X_size = len(witness)
        else:
            witness = None
            method = 'INFEASIBLE'
            X_size = optimal

        # Verify witness (check at least cross_mask=0)
        verified = False
        if witness is not None:
            verified = verify_cover(core, left, right, packing, frozenset(witness), 0)

        # Outside triangles (neither hub) info
        outside_tris = [t for t in packing if U not in t and V not in t]
        outside_types = [classify_triangle_partition(t) for t in outside_tris]

        # Hub classification
        hub_cls = Counter(classify_triangle_hub(t) for t in packing)

        rec_result = {
            'index': idx,
            'key': list(key),
            'S_size': S_size,
            'budget': budget,
            'R_size': len(R),
            'Ju_res_edges': len(Ju_res),
            'Jv_res_edges': len(Jv_res),
            'opt1_cost': opt1,
            'opt2_cost': opt2_val,
            'optimal_cost': optimal,
            'feasible': feasible,
            'epsilon': epsilon,
            'method': method,
            'witness_size': X_size,
            'witness_verified': verified,
            'stored_cover_size': len(cover_stored),
            'outside_tri_count': len(outside_tris),
            'outside_tri_types': outside_types,
            'hub_both': hub_cls.get('both', 0),
            'hub_u': hub_cls.get('u', 0),
            'hub_v': hub_cls.get('v', 0),
            'hub_neither': hub_cls.get('neither', 0),
        }
        if witness is not None:
            rec_result['witness_cover'] = sorted(list(witness))

        results.append(rec_result)

        if not feasible:
            fail_keys.append(key)

        # Group stats by (outside_tri_count, sorted type tuple)
        gkey = (len(outside_tris), tuple(sorted(outside_types)))
        group_stats[gkey]['count'] += 1
        group_stats[gkey]['epsilons'].append(epsilon)
        group_stats[gkey]['opt_sizes'].append(optimal)

    # ─── Summary ────────────────────────────────────────────────────────────────
    n_feasible = sum(1 for r in results if r['feasible'])
    n_verified = sum(1 for r in results if r['witness_verified'])
    eps_counter = Counter(r['epsilon'] for r in results)
    method_counter = Counter(r['method'] for r in results)

    print(f"\n=== RESULTS ===")
    print(f"  Feasible: {n_feasible}/1144")
    print(f"  Witness verified: {n_verified}/1144")
    print(f"  Failed keys: {len(fail_keys)}")
    print(f"  Method distribution: {dict(method_counter)}")
    print(f"  Epsilon distribution (budget - optimal):")
    for e in sorted(eps_counter.keys()):
        print(f"    eps={e}: {eps_counter[e]} records")

    # Grouped stats
    print(f"\n=== GROUPED BY OUTSIDE TRIANGLE PROFILE ===")
    print(f"  (outside_count, types) -> records, mean_eps, min_eps")
    grouped_summary = []
    for gkey in sorted(group_stats.keys(), key=lambda k: (-k[0], k[1])):
        g = group_stats[gkey]
        mean_eps = sum(g['epsilons']) / len(g['epsilons'])
        min_eps = min(g['epsilons'])
        line = f"  {gkey}: n={g['count']}, mean_eps={mean_eps:.2f}, min_eps={min_eps}"
        print(line)
        grouped_summary.append({
            'profile': list(gkey),
            'count': g['count'],
            'mean_epsilon': mean_eps,
            'min_epsilon': min_eps,
        })

    # ─── Save ───────────────────────────────────────────────────────────────────
    output = {
        'description': 'E-targeted: Cover optimization using forced R + uv + hub spokes only',
        'method_note': 'Vertex cover found by brute-force over 64 subsets per side. '
                       'Bounded optimization for fixed saved S, NOT finder or new graph enumeration.',
        'summary': {
            'total_records': 1144,
            'feasible_count': n_feasible,
            'witness_verified_count': n_verified,
            'fail_keys': [list(k) for k in fail_keys],
            'method_distribution': dict(method_counter),
            'epsilon_distribution': {str(k): v for k, v in sorted(eps_counter.items())},
        },
        'grouped_stats': grouped_summary,
        'per_record': results,
    }
    with open(OUTPUT_JSON, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2)
    print(f"\n  Saved: {OUTPUT_JSON}")

    # Write addendum report
    lines = []
    lines.append("=== E-Targeted: Cover Optimization Report ===\n")
    lines.append("Method: For each packing S, compute optimal cover using ONLY:")
    lines.append("  - R (forced rim edges from packing, non-hub)")
    lines.append("  - Optional uv edge")
    lines.append("  - Hub spokes (u-x for x in C∪A, v-y for y in C∪B)")
    lines.append("  Vertex covers found by brute-force (64 subsets max).\n")
    lines.append("Option 1 (with uv): |R| + 1 + vc(Ju-R) + vc(Jv-R)")
    lines.append("Option 2 (no uv):   |R| + min{|Qu|+|Qv| : Qu vc Ju-R, Qv vc Jv-R, Qu∪Qv⊇C}")
    lines.append("Test: min(Opt1, Opt2) <= 2|S|\n")
    lines.append(f"--- Results ---")
    lines.append(f"Feasible: {n_feasible}/1144")
    lines.append(f"Witness verified: {n_verified}/1144")
    lines.append(f"Failed keys: {len(fail_keys)}")
    lines.append(f"Method: opt1_uv={method_counter.get('opt1_uv',0)}, "
                 f"opt2_no_uv={method_counter.get('opt2_no_uv',0)}, "
                 f"infeasible={method_counter.get('INFEASIBLE',0)}")
    lines.append(f"\nEpsilon (2|S| - optimal cover size):")
    for e in sorted(eps_counter.keys()):
        lines.append(f"  eps={e:2d}: {eps_counter[e]:4d} records ({100*eps_counter[e]/1144:.1f}%)")
    lines.append(f"\nGrouped by outside-triangle profile:")
    for gs in grouped_summary:
        lines.append(f"  {gs['profile']}: n={gs['count']}, mean_eps={gs['mean_epsilon']:.2f}, min_eps={gs['min_epsilon']}")
    lines.append(f"\n--- Failing keys (if any) ---")
    if fail_keys:
        for k in fail_keys:
            lines.append(f"  {list(k)}")
    else:
        lines.append("  NONE — all records admit an optimal restricted cover within budget.")
    lines.append(f"\n--- Witness coverage analysis ---")
    # How many witnesses differ from stored cover?
    different_count = sum(1 for r in results if r['witness_size'] < r['stored_cover_size'])
    same_count = sum(1 for r in results if r['witness_size'] == r['stored_cover_size'])
    lines.append(f"Witness strictly smaller than stored: {different_count}")
    lines.append(f"Witness same size as stored: {same_count}")
    lines.append(f"Witness larger than stored (should not happen): {1144-different_count-same_count}")

    with open(REPORT_ADDENDUM, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"  Saved: {REPORT_ADDENDUM}")

    return 0


if __name__ == '__main__':
    sys.exit(main())
