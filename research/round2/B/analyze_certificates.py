#!/usr/bin/env python3
"""Role B: Independent numerical/statistical analysis of the codegree-4 certificate catalogue.

Operates ONLY on saved records. No graph enumeration, no solver, no external deps.
"""

from collections import Counter
from itertools import combinations, permutations
import hashlib
import json
import sys
from pathlib import Path

# ─── Paths ───────────────────────────────────────────────────────────────────────
HERE = Path(__file__).resolve().parent
CERT_PATH = HERE.parent / "shared" / "B_codegree4_certificates.json"
OUTPUT_JSON = HERE / "B_analysis_results.json"
REPORT_TXT = HERE / "report.txt"

# ─── Schema constants (from check_codegree4.py) ─────────────────────────────────
U, V = 0, 1
COMMON = (2, 3, 4, 5)
LEFT = (6, 7)     # A-exclusive
RIGHT = (8, 9)   # B-exclusive
VERTICES10 = tuple(range(10))
C4 = tuple(range(4))  # local core indices 0..3
CORE_TO_GLOBAL = {c: c + 2 for c in C4}
CORE_EDGES = tuple(combinations(C4, 2))  # 6 edges
CORE_INDEX = {e: i for i, e in enumerate(CORE_EDGES)}
SIDE_EDGES = tuple((c, 4) for c in C4) + tuple((c, 5) for c in C4) + ((4, 5),)  # 9 edges
CROSS_EDGES = tuple((a, b) for a in LEFT for b in RIGHT)  # 4 edges
S4 = tuple(permutations(C4))  # 24 permutations of core vertices


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 16), b''):
            h.update(chunk)
    return h.hexdigest()


# ─── Graph construction from bit masks ──────────────────────────────────────────

def core_edges_from_mask(mask):
    """Return frozenset of (local_x, local_y) edges from 6-bit core mask."""
    return frozenset(e for i, e in enumerate(CORE_EDGES) if (mask >> i) & 1)


def side_edges_from_mask(mask):
    """Return frozenset of (c, exclusive) from 9-bit side mask.
    Side bit i corresponds to SIDE_EDGES[i] = (c, e) where c in 0..3, e in {4,5}.
    """
    return frozenset(SIDE_EDGES[i] for i in range(9) if (mask >> i) & 1)


def guaranteed_graph(core, left, right, cross_mask=0):
    """Build the guaranteed edge set on 10 vertices from (core, left, right, cross)."""
    edges = set()
    # Hub-edge: uv
    edges.add((U, V))
    # u connects to all common
    edges.update((U, c) for c in COMMON)
    # v connects to all common
    edges.update((V, c) for c in COMMON)
    # u connects to left exclusives (A-side)
    edges.update((U, a) for a in LEFT)
    # v connects to right exclusives (B-side)
    edges.update((V, b) for b in RIGHT)
    # Core edges (on common vertices)
    for x, y in core_edges_from_mask(core):
        gx, gy = CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]
        edges.add((min(gx, gy), max(gx, gy)))
    # Left side: connects common to A-exclusive
    for i, (c, ex) in enumerate(SIDE_EDGES):
        if (left >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                ga = LEFT[ex - 4]  # ex=4→LEFT[0]=6, ex=5→LEFT[1]=7
                edges.add((min(gc, ga), max(gc, ga)))
            else:
                edges.add((min(LEFT), max(LEFT)))  # (6,7)
    # Right side: connects common to B-exclusive
    for i, (c, ex) in enumerate(SIDE_EDGES):
        if (right >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                gb = RIGHT[ex - 4]  # ex=4→RIGHT[0]=8, ex=5→RIGHT[1]=9
                edges.add((min(gc, gb), max(gc, gb)))
            else:
                edges.add((min(RIGHT), max(RIGHT)))  # (8,9)
    # Cross edges (A-B)
    for i, edge in enumerate(CROSS_EDGES):
        if (cross_mask >> i) & 1:
            edges.add(edge)
    return frozenset(edges)


def graph_triangles(edges):
    """All triangles in the graph defined by edge set."""
    es = set(edges)
    return tuple(
        triple for triple in combinations(VERTICES10, 3)
        if all((min(a,b), max(a,b)) in es for a, b in combinations(triple, 2))
    )


def triangle_edge_set(triple):
    return frozenset((min(a, b), max(a, b)) for a, b in combinations(triple, 2))


# ─── Reducibility check (literal_reduction from source) ─────────────────────────

def literal_reduction(core, left, right, packing, cover, cross_mask):
    """Check all three Puleo conditions under given cross_mask."""
    edges = guaranteed_graph(core, left, right, cross_mask)
    # Condition 0: cover must be subset of edges
    if not cover <= edges:
        return False
    # Condition 1: packing triangles must use disjoint edges from the graph
    used = set()
    for tri in packing:
        te = triangle_edge_set(tri)
        if not te <= edges:
            return False
        if used & te:
            return False
        used.update(te)
    # Condition 2: |cover| <= 2|packing|
    if len(cover) > 2 * len(packing):
        return False
    # Condition 3: every triangle containing u or v must have an edge in cover
    for tri in graph_triangles(edges):
        if (U in tri or V in tri):
            if not (triangle_edge_set(tri) & cover):
                return False
    # Condition 4: every packing triangle's non-hub edges must be in cover
    for tri in packing:
        for edge in triangle_edge_set(tri):
            if U not in edge and V not in edge:
                if edge not in cover:
                    return False
    return True


# ─── Degree compatibility ──────────────────────────────────────────────────────

def core_degree(core, c):
    return sum(c in e for e in core_edges_from_mask(core))


def side_attachment_degree(side, c):
    """Count how many edges from side mask attach to core vertex c."""
    return sum((side >> (4 * ex + c)) & 1 for ex in range(2))


def degree_compatible(core, left, right):
    """All common vertices have degree <= 5 in the link."""
    return all(
        core_degree(core, c) + side_attachment_degree(left, c) + side_attachment_degree(right, c) <= 5
        for c in C4
    )


# ─── Canonical pair check ───────────────────────────────────────────────────────

def permute_core_mask(mask, perm):
    """Apply permutation perm to core mask."""
    answer = 0
    for x, y in core_edges_from_mask(mask):
        e = tuple(sorted((perm[x], perm[y])))
        answer |= 1 << CORE_INDEX[e]
    return answer


def transform_side(mask, core_perm, swap_exclusives):
    """Apply core permutation and optional exclusive swap to a side mask."""
    answer = 0
    for i, (x, y) in enumerate(SIDE_EDGES):
        if not (mask >> i) & 1:
            continue
        if x < 4:
            core_vertex = core_perm[x]
            exclusive = y
            if swap_exclusives:
                exclusive = 9 - exclusive  # 4<->5
            e = (core_vertex, exclusive)
        else:
            e = (4, 5)
        # Find index of e in SIDE_EDGES
        idx = SIDE_EDGES.index(e)
        answer |= 1 << idx
    return answer


def core_automorphisms(core):
    return tuple(p for p in S4 if permute_core_mask(core, p) == core)


def canonical_pair(core, left, right):
    """Compute the canonical representative of (core, left, right) under the orbit group."""
    candidates = []
    for perm in core_automorphisms(core):
        for swap_left in (False, True):
            tl = transform_side(left, perm, swap_left)
            for swap_right in (False, True):
                tr = transform_side(right, perm, swap_right)
                candidates.append((core, tl, tr))
                candidates.append((core, tr, tl))
    return min(candidates)


# ─── Task 2 helpers: Packing classification ─────────────────────────────────────

def classify_triangle_hub(tri):
    """Classify triangle by hub membership: 'both', 'u', 'v', 'neither'."""
    has_u = U in tri
    has_v = V in tri
    if has_u and has_v:
        return 'both'
    elif has_u:
        return 'u'
    elif has_v:
        return 'v'
    else:
        return 'neither'


def partition_type(tri):
    """Classify a non-hub triangle by partition of its vertices into C/A/B sets.
    C = common {2,3,4,5}, A = left {6,7}, B = right {8,9}
    Returns sorted string like 'CCC', 'CCA', 'CAB', etc.
    """
    cats = []
    for v in tri:
        if v in COMMON:
            cats.append('C')
        elif v in LEFT:
            cats.append('A')
        elif v in RIGHT:
            cats.append('B')
        else:
            cats.append('?')
    return ''.join(sorted(cats))


def edge_is_rim(edge):
    """Rim edge: not incident to u or v."""
    return U not in edge and V not in edge


def edge_is_spoke(edge):
    """Spoke edge: incident to u or v."""
    return U in edge or V in edge


def classify_spoke(edge):
    """Classify spoke by which hub and which category the other endpoint is in."""
    hub = U if U in edge else V
    other = edge[1] if edge[0] == hub else edge[0]
    if other in COMMON:
        cat = 'C'
    elif other in LEFT:
        cat = 'A'
    elif other in RIGHT:
        cat = 'B'
    elif other == (V if hub == U else U):
        cat = 'hub'  # uv edge
    else:
        cat = '?'
    return (hub, cat)


# ─── Task 3: Canonicalize packing under Gamma (192 maps) ────────────────────────

def build_gamma():
    """Build all 192 vertex permutations in Gamma.
    Structure: S4(common) x Z2(swap A-vertices) x Z2(swap B-vertices) x Z2(swap uA<->vB)
    Returns list of dicts mapping vertex→vertex.
    """
    # Base mappings
    A_ID = {6: 6, 7: 7}
    A_SWAP = {6: 7, 7: 6}
    B_ID = {8: 8, 9: 9}
    B_SWAP = {8: 9, 9: 8}

    gamma = []
    for sigma in S4:  # 24 permutations of {0,1,2,3} → {0,1,2,3} (local core indices)
        # Map common vertices: CORE_TO_GLOBAL[sigma[i]] for global i
        common_map = {2 + i: 2 + sigma[i] for i in range(4)}
        for alpha in (A_ID, A_SWAP):  # 2
            for beta in (B_ID, B_SWAP):  # 2
                for do_big_swap in (False, True):  # 2
                    perm = {}
                    if not do_big_swap:
                        # u→u, v→v, common→σ(common), A→α(A), B→β(B)
                        perm[0] = 0
                        perm[1] = 1
                        for c in COMMON:
                            perm[c] = common_map[c]
                        for a in LEFT:
                            perm[a] = alpha[a]
                        for b in RIGHT:
                            perm[b] = beta[b]
                    else:
                        # u→v, v→u, common→σ(common), A→β(B_via_default), B→α(A_via_default)
                        # Default A→B: 6→8, 7→9; B→A: 8→6, 9→7
                        perm[0] = 1
                        perm[1] = 0
                        for c in COMMON:
                            perm[c] = common_map[c]
                        # A vertex a maps to RIGHT vertex: first apply default map then beta
                        default_a_to_b = {6: 8, 7: 9}
                        default_b_to_a = {8: 6, 9: 7}
                        for a in LEFT:
                            perm[a] = beta[default_a_to_b[a]]
                        for b in RIGHT:
                            perm[b] = alpha[default_b_to_a[b]]
                    gamma.append(perm)
    assert len(gamma) == 192, f"Expected 192, got {len(gamma)}"
    return gamma


def apply_perm_to_triangle(perm, tri):
    """Apply vertex permutation to a triangle (3-tuple), return sorted."""
    return tuple(sorted(perm[v] for v in tri))


def apply_perm_to_packing(perm, packing):
    """Apply permutation to entire packing, return as frozenset of sorted triples."""
    return frozenset(apply_perm_to_triangle(perm, tri) for tri in packing)


def canonical_packing(packing, gamma):
    """Find canonical representative of packing under Gamma action.
    Returns sorted tuple of sorted triangles (lexicographically minimal orbit member).
    """
    ps = frozenset(packing)
    return min(tuple(sorted(apply_perm_to_packing(perm, ps))) for perm in gamma)


# ─── Main Analysis ──────────────────────────────────────────────────────────────

def main():
    print("Computing input SHA256...")
    input_sha = sha256_file(CERT_PATH)
    print(f"  SHA256: {input_sha}")

    print("Loading records...")
    with open(CERT_PATH, 'r', encoding='utf-8') as f:
        doc = json.load(f)
    records = doc['records']
    assert len(records) == 1144, f"Expected 1144 records, got {len(records)}"

    # Parse all records
    print("Parsing records...")
    parsed = []
    for rec in records:
        core = rec['core_mask']
        left = rec['left_side_mask']
        right = rec['right_side_mask']
        packing = tuple(tuple(t) for t in rec['packing'])
        cover = frozenset(tuple(e) for e in rec['cover'])
        parsed.append((core, left, right, packing, cover))

    # Check duplicate keys
    print("Checking for duplicate keys...")
    keys = [(c, l, r) for c, l, r, _, _ in parsed]
    dup_count = len(keys) - len(set(keys))
    print(f"  Duplicate keys: {dup_count}")

    # ─── Task 1: Full verification ──────────────────────────────────────────────
    print("\n=== TASK 1: Reducibility verification ===")
    task1_results = []
    all_pass = True
    for idx, (core, left, right, packing, cover) in enumerate(parsed):
        key = (core, left, right)
        # Check degree budget
        deg_ok = degree_compatible(core, left, right)
        # Check canonical form
        canon = canonical_pair(core, left, right)
        canon_ok = (canon == key)
        # Check all 16 cross extensions
        cross_results = []
        for cm in range(16):
            r = literal_reduction(core, left, right, packing, cover, cm)
            cross_results.append(r)
        all_cross_ok = all(cross_results)
        rec_result = {
            'index': idx,
            'key': list(key),
            'degree_compatible': deg_ok,
            'is_canonical': canon_ok,
            'all_16_cross_ok': all_cross_ok,
            'cross_fail_masks': [cm for cm in range(16) if not cross_results[cm]],
            'packing_size': len(packing),
            'cover_size': len(cover),
            'tight': len(cover) == 2 * len(packing),
        }
        task1_results.append(rec_result)
        if not (deg_ok and canon_ok and all_cross_ok):
            all_pass = False

    n_deg_fail = sum(1 for r in task1_results if not r['degree_compatible'])
    n_canon_fail = sum(1 for r in task1_results if not r['is_canonical'])
    n_cross_fail = sum(1 for r in task1_results if not r['all_16_cross_ok'])
    n_tight = sum(1 for r in task1_results if r['tight'])
    total_cross_checks = 1144 * 16

    print(f"  Total records: 1144")
    print(f"  Duplicate keys: {dup_count}")
    print(f"  Degree budget failures: {n_deg_fail}")
    print(f"  Non-canonical keys: {n_canon_fail}")
    print(f"  Cross-extension failures (any mask): {n_cross_fail}")
    print(f"  Total cross extensions checked: {total_cross_checks}")
    print(f"  Tight records (|cover|=2|packing|): {n_tight}/1144")
    print(f"  ALL PASS: {all_pass and dup_count == 0}")

    # ─── Task 2: Packing statistics ─────────────────────────────────────────────
    print("\n=== TASK 2: Packing statistics ===")
    task2_results = []
    # Global accumulators
    global_hub_counter = Counter()
    global_partition_counter = Counter()
    global_uv_location = Counter()  # 'packing', 'cover', 'both', 'neither'

    for idx, (core, left, right, packing, cover) in enumerate(parsed):
        key = (core, left, right)
        # Build full edge set at cross_mask=0 for reference
        edges0 = guaranteed_graph(core, left, right, 0)

        # Hub classification of packing triangles
        hub_cls = Counter()
        for tri in packing:
            cls = classify_triangle_hub(tri)
            hub_cls[cls] += 1
            global_hub_counter[cls] += 1

        # Partition types of non-hub (neither) packing triangles
        partition_types = []
        for tri in packing:
            if U not in tri and V not in tri:
                pt = partition_type(tri)
                partition_types.append(pt)
                global_partition_counter[pt] += 1

        # Cover decomposition
        cover_spokes = [e for e in cover if edge_is_spoke(e)]
        cover_rims = [e for e in cover if edge_is_rim(e)]

        # Spoke sub-classification
        spoke_detail = Counter()
        for e in cover_spokes:
            hub, cat = classify_spoke(e)
            spoke_detail[f"{hub}_{'u' if hub == U else 'v'}_{cat}"] += 1

        # External S-edge union: cover rim edges that are NOT core edges
        # Core edges on global vertices:
        core_global_edges = frozenset(
            (min(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]), max(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
            for x, y in core_edges_from_mask(core)
        )
        # Side edges on global vertices (left side):
        left_global_edges = set()
        for i, (c, ex) in enumerate(SIDE_EDGES):
            if (left >> i) & 1:
                if c < 4:
                    gc = CORE_TO_GLOBAL[c]
                    ga = LEFT[ex - 4]
                    left_global_edges.add((min(gc, ga), max(gc, ga)))
                else:
                    left_global_edges.add((6, 7))
        right_global_edges = set()
        for i, (c, ex) in enumerate(SIDE_EDGES):
            if (right >> i) & 1:
                if c < 4:
                    gc = CORE_TO_GLOBAL[c]
                    gb = RIGHT[ex - 4]
                    right_global_edges.add((min(gc, gb), max(gc, gb)))
                else:
                    right_global_edges.add((8, 9))
        # All S-edges (structural non-core, non-hub edges from the packing key)
        s_edges_global = left_global_edges | right_global_edges
        # Rim edges in cover that are NOT in core or S-edges → "external"
        external_rim_in_cover = [e for e in cover_rims if e not in core_global_edges and e not in s_edges_global]

        # Extra rim edges: rim edges in cover beyond those needed for packing's non-hub edges
        packing_nonhub_edges = set()
        for tri in packing:
            for e in triangle_edge_set(tri):
                if edge_is_rim(e):
                    packing_nonhub_edges.add(e)
        extra_rim_in_cover = [e for e in cover_rims if e not in packing_nonhub_edges]

        # Whether uv (edge (0,1)) belongs to packing S or cover X
        uv_in_packing = any((U, V) in triangle_edge_set(tri) for tri in packing)
        uv_in_cover = (U, V) in cover
        uv_loc = 'both' if (uv_in_packing and uv_in_cover) else \
                 'packing_only' if uv_in_packing else \
                 'cover_only' if uv_in_cover else 'neither'
        global_uv_location[uv_loc] += 1

        # Residual hub links after deleting rim edges from the guaranteed graph
        # Hub links = edges incident to u or v in the guaranteed graph
        # After removing all rim edges (non-hub edges), what spoke edges remain?
        # Actually, I think the intent is: in the packing, after removing the "structural"
        # non-hub edges (rim edges of packing triangles), what hub-incident edges still used?
        packing_hub_edges = set()
        for tri in packing:
            for e in triangle_edge_set(tri):
                if edge_is_spoke(e):
                    packing_hub_edges.add(e)
        # These are the "active hub links" from the packing

        # Full hub links available in guaranteed graph (cross_mask=0 baseline)
        all_hub_edges = set()
        for e in edges0:
            if edge_is_spoke(e):
                all_hub_edges.add(e)

        # Residual = hub edges in guaranteed graph NOT consumed by packing
        residual_hub = all_hub_edges - packing_hub_edges

        rec_stat = {
            'index': idx,
            'key': list(key),
            'packing_size': len(packing),
            'cover_size': len(cover),
            'tight': len(cover) == 2 * len(packing),
            'hub_both': hub_cls.get('both', 0),
            'hub_u_only': hub_cls.get('u', 0),
            'hub_v_only': hub_cls.get('v', 0),
            'hub_neither': hub_cls.get('neither', 0),
            'partition_types': partition_types,
            'cover_spoke_count': len(cover_spokes),
            'cover_rim_count': len(cover_rims),
            'cover_spoke_detail': dict(spoke_detail),
            'external_rim_in_cover': [list(e) for e in sorted(external_rim_in_cover)],
            'extra_rim_in_cover': [list(e) for e in sorted(extra_rim_in_cover)],
            'uv_location': uv_loc,
            'packing_hub_edge_count': len(packing_hub_edges),
            'residual_hub_edge_count': len(residual_hub),
            'residual_hub_edges': [list(e) for e in sorted(residual_hub)],
        }
        task2_results.append(rec_stat)

    print(f"  Hub triangle distribution (all packings): {dict(global_hub_counter)}")
    print(f"  Non-hub partition types: {dict(global_partition_counter)}")
    print(f"  UV edge location: {dict(global_uv_location)}")
    packing_size_hist = Counter(r['packing_size'] for r in task2_results)
    print(f"  Packing size histogram: {dict(sorted(packing_size_hist.items()))}")
    tight_count = sum(1 for r in task2_results if r['tight'])
    print(f"  Tight: {tight_count}/1144")

    # ─── Task 3: Canonicalize packings under Gamma ──────────────────────────────
    print("\n=== TASK 3: Packing canonicalization under Gamma (192 maps) ===")
    gamma = build_gamma()

    packing_orbits = {}  # canonical_rep -> list of record indices
    packing_orbit_witnesses = {}  # canonical_rep -> representative packing
    record_canonical = {}  # record_index -> canonical_rep

    for idx, (core, left, right, packing, cover) in enumerate(parsed):
        canon = canonical_packing(packing, gamma)
        key_c = canon  # already a sorted tuple of sorted triangles
        if key_c not in packing_orbits:
            packing_orbits[key_c] = []
            packing_orbit_witnesses[key_c] = list(canon)
        packing_orbits[key_c].append(idx)
        record_canonical[idx] = key_c

    n_orbits = len(packing_orbits)
    orbit_sizes = [len(v) for v in packing_orbits.values()]
    print(f"  Exact packing orbits: {n_orbits}")
    print(f"  Orbit size distribution: {dict(Counter(orbit_sizes))}")

    # Also try (S,X) canonicalization: orbit of the pair
    # For this we apply the same Gamma to both packing and cover
    sx_orbits = {}
    sx_witnesses = {}
    record_sx_canonical = {}

    for idx, (core, left, right, packing, cover) in enumerate(parsed):
        ps = frozenset(packing)
        cs = cover
        # Canonical form = min over all 192 permutations of (permuted_packing, permuted_cover)
        best = None
        for perm in gamma:
            cp = frozenset(apply_perm_to_triangle(perm, t) for t in ps)
            cc = frozenset((min(perm[a], perm[b]), max(perm[a], perm[b])) for a, b in cs)
            candidate = (tuple(sorted(cp)), tuple(sorted(cc)))
            if best is None or candidate < best:
                best = candidate
        key_sx = (list(best[0]), list(best[1]))
        # Serialize for dict key
        key_sx_str = json.dumps(key_sx)
        if key_sx_str not in sx_orbits:
            sx_orbits[key_sx_str] = []
            sx_witnesses[key_sx_str] = key_sx
        sx_orbits[key_sx_str].append(idx)
        record_sx_canonical[idx] = key_sx_str

    n_sx_orbits = len(sx_orbits)
    sx_orbit_sizes = [len(v) for v in sx_orbits.values()]
    print(f"  Exact (S,X) orbits: {n_sx_orbits}")
    print(f"  (S,X) orbit size distribution: {dict(Counter(sx_orbit_sizes))}")

    # ─── Save results ───────────────────────────────────────────────────────────
    print("\nSaving results...")
    output = {
        'input_sha256': input_sha,
        'task1': {
            'description': 'Independent reducibility verification (all 16 cross extensions)',
            'duplicate_keys': dup_count,
            'degree_budget_failures': n_deg_fail,
            'non_canonical_keys': n_canon_fail,
            'cross_extension_failures': n_cross_fail,
            'total_cross_checks': total_cross_checks,
            'tight_count': n_tight,
            'all_pass': all_pass and dup_count == 0,
            'per_record': task1_results,
        },
        'task2': {
            'description': 'Packing and cover statistics',
            'global_hub_distribution': dict(global_hub_counter),
            'global_partition_types': dict(global_partition_counter),
            'global_uv_location': dict(global_uv_location),
            'packing_size_histogram': dict(sorted(packing_size_hist.items())),
            'tight_count': tight_count,
            'per_record': task2_results,
        },
        'task3': {
            'description': 'Packing canonicalization under Gamma (192 maps: S4 x Z2 x Z2 x Z2)',
            'note': 'Measures literal witness shapes under this specific group action. '
                    'Not a claim about minimum structural templates.',
            'packing_orbits': n_orbits,
            'packing_orbit_sizes': dict(Counter(orbit_sizes)),
            'sx_orbits': n_sx_orbits,
            'sx_orbit_sizes': dict(Counter(sx_orbit_sizes)),
            'packing_orbit_witnesses': {json.dumps(k): v for k, v in packing_orbit_witnesses.items()},
            'record_to_packing_orbit': {str(k): v for k, v in record_canonical.items()},
            'record_to_sx_orbit': {str(k): v for k, v in record_sx_canonical.items()},
        },
    }
    with open(OUTPUT_JSON, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2)
    print(f"  Saved: {OUTPUT_JSON}")

    # ─── Compact report ─────────────────────────────────────────────────────────
    print("Writing report...")
    lines = []
    lines.append("=== Role B: Codegree-4 Certificate Analysis Report ===\n")
    lines.append(f"Input file SHA256: {input_sha}")
    lines.append(f"Total records: 1144\n")

    lines.append("--- Task 1: Reducibility Verification ---")
    lines.append(f"Duplicates: {dup_count}")
    lines.append(f"Degree budget failures: {n_deg_fail}")
    lines.append(f"Non-canonical keys: {n_canon_fail}")
    lines.append(f"Any cross-extension failure (out of 16 each): {n_cross_fail}")
    lines.append(f"Total cross-extension checks: {total_cross_checks}")
    lines.append(f"Tight (|cover|=2|packing|): {n_tight}/1144")
    lines.append(f"OVERALL: {'ALL RECORDS VALID' if all_pass and dup_count==0 else 'FAILURES DETECTED'}")
    lines.append("")

    lines.append("--- Task 2: Packing Statistics ---")
    lines.append(f"Hub-triangle type distribution (total across all packings):")
    for k in sorted(global_hub_counter.keys()):
        lines.append(f"  {k}: {global_hub_counter[k]}")
    lines.append(f"\nNon-hub partition types:")
    for k in sorted(global_partition_counter.keys()):
        lines.append(f"  {k}: {global_partition_counter[k]}")
    lines.append(f"\nUV edge location:")
    for k in sorted(global_uv_location.keys()):
        lines.append(f"  {k}: {global_uv_location[k]}")
    lines.append(f"\nPacking size histogram:")
    for k in sorted(packing_size_hist.keys()):
        lines.append(f"  size {k}: {packing_size_hist[k]} records")
    lines.append(f"\nAll tight: {'YES' if tight_count == 1144 else f'NO ({tight_count}/1144)'}")
    lines.append("")

    lines.append("--- Task 3: Gamma Orbits ---")
    lines.append(f"Group: S4(permute 4 common) x Z2(swap A-vertices) x Z2(swap B-vertices) x Z2(swap uA<->vB) = 192 elements")
    lines.append(f"Note: This measures literal witness shapes under this group, not minimum structural templates.")
    lines.append(f"\nPacking-only orbits: {n_orbits} distinct")
    lines.append(f"Packing orbit size distribution: {dict(sorted(Counter(orbit_sizes).items()))}")
    lines.append(f"\n(S,X) pair orbits: {n_sx_orbits} distinct")
    lines.append(f"(S,X) orbit size distribution: {dict(sorted(Counter(sx_orbit_sizes).items()))}")
    lines.append(f"\nCompression ratio (packing): 1144 records → {n_orbits} orbits = {n_orbits/1144:.4f}")
    lines.append(f"Compression ratio (S,X):     1144 records → {n_sx_orbits} orbits = {n_sx_orbits/1144:.4f}")
    lines.append("")

    lines.append("--- Key Findings ---")
    if n_orbits < 1144:
        lines.append(f"Gamma action on packings alone reveals {n_orbits} distinct shapes.")
    if n_sx_orbits < n_orbits:
        lines.append(f"Including cover X in the orbit refines to {n_sx_orbits} classes.")
    lines.append("No claim that saved keys cover all theoretical admissible graphs.")

    with open(REPORT_TXT, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"  Saved: {REPORT_TXT}")

    print("\nDone.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
