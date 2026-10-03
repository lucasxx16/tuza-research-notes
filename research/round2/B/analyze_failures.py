#!/usr/bin/env python3
"""Analyze failures: check if extra rim edges resolve them."""
import json
from collections import Counter, defaultdict
from itertools import combinations, product

U, V = 0, 1
COMMON = (2, 3, 4, 5)
LEFT = (6, 7)
RIGHT = (8, 9)
C4 = tuple(range(4))
CORE_TO_GLOBAL = {c: c + 2 for c in C4}
CORE_EDGES_LOCAL = tuple(combinations(C4, 2))
SIDE_EDGES_LOCAL = tuple((c, 4) for c in C4) + tuple((c, 5) for c in C4) + ((4, 5),)
JU_VERTS = (2, 3, 4, 5, 6, 7)
JV_VERTS = (2, 3, 4, 5, 8, 9)


def normalize_edge(a, b):
    return (min(a, b), max(a, b))


def build_Ju(core_mask, left_mask):
    edges = set()
    for i, (x, y) in enumerate(CORE_EDGES_LOCAL):
        if (core_mask >> i) & 1:
            edges.add(normalize_edge(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (left_mask >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                ga = LEFT[ex - 4]
                edges.add(normalize_edge(gc, ga))
            else:
                edges.add(normalize_edge(6, 7))
    return frozenset(edges)


def build_Jv(core_mask, right_mask):
    edges = set()
    for i, (x, y) in enumerate(CORE_EDGES_LOCAL):
        if (core_mask >> i) & 1:
            edges.add(normalize_edge(CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]))
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (right_mask >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                gb = RIGHT[ex - 4]
                edges.add(normalize_edge(gc, gb))
            else:
                edges.add(normalize_edge(8, 9))
    return frozenset(edges)


def packing_rim_edges(packing):
    rim = set()
    for tri in packing:
        for a, b in combinations(tri, 2):
            if a != U and a != V and b != U and b != V:
                rim.add(normalize_edge(a, b))
    return frozenset(rim)


def vc_min_size(edges, vertices):
    """Min vertex cover size over edges restricted to vertices."""
    n = len(vertices)
    vset = set(vertices)
    valid = [(a, b) for a, b in edges if a in vset and b in vset]
    if not valid:
        return 0
    best = n
    for mask in range(1 << n):
        sz = bin(mask).count('1')
        if sz >= best:
            continue
        subset = frozenset(vertices[i] for i in range(n) if (mask >> i) & 1)
        if all(a in subset or b in subset for a, b in valid):
            best = sz
    return best


with open('B_cover_optimization.json', 'r') as f:
    data = json.load(f)

fails = [r for r in data['per_record'] if not r['feasible']]
print(f"=== Failing records: {len(fails)} ===")
print(f"All at epsilon=-1: {all(r['epsilon'] == -1 for r in fails)}")

core_dist = Counter(r['key'][0] for r in fails)
print(f"Failing by core_mask: {dict(sorted(core_dist.items()))}")

s_dist = Counter(r['S_size'] for r in fails)
print(f"Failing by S_size: {dict(sorted(s_dist.items()))}")

outside_dist = Counter(r['outside_tri_count'] for r in fails)
print(f"Failing by outside_tri_count: {dict(sorted(outside_dist.items()))}")

# For failures: check if the shared core edges in Ju_res AND Jv_res explain it
# Strategy: try adding ONE extra rim edge (from Ju|Jv minus R) and see if cost drops
print("\n=== Testing: add 1 extra rim edge to resolve failures ===")

with open('..\\shared\\B_codegree4_certificates.json', 'r') as f:
    doc = json.load(f)
records = doc['records']

resolved = 0
still_fail = 0
for fr in fails:
    key = tuple(fr['key'])
    idx = fr['index']
    rec = records[idx]
    core = rec['core_mask']
    left = rec['left_side_mask']
    right = rec['right_side_mask']
    packing = [tuple(t) for t in rec['packing']]
    budget = fr['budget']

    R = packing_rim_edges(packing)
    Ju = build_Ju(core, left)
    Jv = build_Jv(core, right)
    Ju_res = frozenset(e for e in Ju if e not in R)
    Jv_res = frozenset(e for e in Jv if e not in R)

    # Shared edges between Ju_res and Jv_res (these are core edges not in R)
    shared = Ju_res & Jv_res
    # All candidate extra rim edges (in Ju or Jv but not in R)
    all_extra = (Ju_res | Jv_res)

    # Try each extra edge
    found = False
    for extra in all_extra:
        Ju_new = Ju_res - {extra}
        Jv_new = Jv_res - {extra}
        # Option 1: R + extra + uv + vc(Ju_new) + vc(Jv_new)
        cost1 = len(R) + 1 + 1 + vc_min_size(Ju_new, JU_VERTS) + vc_min_size(Jv_new, JV_VERTS)
        if cost1 <= budget:
            found = True
            break
        # Option 2: R + extra + joint VC
        cost2_no_uv = vc_min_size(Ju_new, JU_VERTS) + vc_min_size(Jv_new, JV_VERTS)
        # Need joint check, approximate with min of individual
        cost2 = len(R) + 1 + cost2_no_uv
        if cost2 <= budget:
            found = True
            break

    if found:
        resolved += 1
    else:
        still_fail += 1

print(f"  Resolved with 1 extra rim edge: {resolved}/{len(fails)}")
print(f"  Still failing with 1 extra: {still_fail}/{len(fails)}")

# Also check: how many failures have shared core edges in residual?
print("\n=== Failure mechanism analysis ===")
has_shared = 0
for fr in fails:
    idx = fr['index']
    rec = records[idx]
    core = rec['core_mask']
    left = rec['left_side_mask']
    right = rec['right_side_mask']
    packing = [tuple(t) for t in rec['packing']]
    R = packing_rim_edges(packing)
    Ju = build_Ju(core, left)
    Jv = build_Jv(core, right)
    Ju_res = frozenset(e for e in Ju if e not in R)
    Jv_res = frozenset(e for e in Jv if e not in R)
    shared = Ju_res & Jv_res
    if shared:
        has_shared += 1
print(f"  Failures with shared core edges in both residuals: {has_shared}/{len(fails)}")
print(f"  (These benefit from one extra rim edge covering both sides simultaneously)")
