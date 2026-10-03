#!/usr/bin/env python3
"""Supplementary: orbit decomposition patterns and potential stronger compressions."""

from collections import Counter, defaultdict
from itertools import combinations, permutations
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESULTS_PATH = HERE / "B_analysis_results.json"
CERT_PATH = HERE.parent / "shared" / "B_codegree4_certificates.json"

# Load
with open(RESULTS_PATH, 'r') as f:
    res = json.load(f)
with open(CERT_PATH, 'r') as f:
    doc = json.load(f)

records = doc['records']

# Get packing orbit assignments (values are lists from JSON, convert to tuple-of-tuples for hashing)
record_to_orbit = {int(k): tuple(tuple(t) for t in v) for k, v in res['task3']['record_to_packing_orbit'].items()}
record_to_sx_orbit = {int(k): v for k, v in res['task3']['record_to_sx_orbit'].items()}  # string keys are hashable

# Build orbit membership
packing_orbit_members = defaultdict(list)
for idx, okey in record_to_orbit.items():
    packing_orbit_members[okey].append(idx)

sx_orbit_members = defaultdict(list)
for idx, okey in record_to_sx_orbit.items():
    sx_orbit_members[okey].append(idx)

# Stats per core_mask for packing orbits
print("=== Packing orbit count by core_mask ===")
core_orbit_map = defaultdict(set)  # core -> set of orbit keys
for idx, okey in record_to_orbit.items():
    core = records[idx]['core_mask']
    core_orbit_map[core].add(okey)

for core in sorted(core_orbit_map.keys()):
    n_records_core = sum(1 for r in records if r['core_mask'] == core)
    n_orbits_core = len(core_orbit_map[core])
    print(f"  core={core:2d}: {n_records_core} records -> {n_orbits_core} packing orbits "
          f"(ratio {n_orbits_core/n_records_core:.3f})")

# Packing orbits that span multiple core_masks (cross-core equivalences)
print("\n=== Packing orbits spanning multiple core_masks ===")
cross_core = 0
for okey, members in packing_orbit_members.items():
    cores = set(records[i]['core_mask'] for i in members)
    if len(cores) > 1:
        cross_core += 1
print(f"  Orbits spanning >1 core_mask: {cross_core} / {len(packing_orbit_members)}")

# (S,X) orbits that merge different packing orbits
print("\n=== (S,X) vs packing orbit refinement ===")
# For each (S,X) orbit, which packing orbits does it touch?
sx_to_packing = defaultdict(set)
for idx, sxkey in record_to_sx_orbit.items():
    sx_to_packing[sxkey].add(record_to_orbit[idx])
# An (S,X) orbit can only be a subset of one packing orbit
# (since (S,X) equivalence implies S equivalence)
# Verify
for sxkey, pkeys in sx_to_packing.items():
    if len(pkeys) > 1:
        print(f"  BUG: SX orbit spans {len(pkeys)} packing orbits!")
        break
else:
    print("  OK: each (S,X) orbit is contained in exactly one packing orbit.")

# How many packing orbits split into multiple (S,X) orbits?
packing_to_sx = defaultdict(set)
for idx, pkey in record_to_orbit.items():
    packing_to_sx[pkey].add(record_to_sx_orbit[idx])
split_count = sum(1 for pkey, sxkeys in packing_to_sx.items() if len(sxkeys) > 1)
print(f"  Packing orbits split by (S,X): {split_count} / {len(packing_to_sx)}")

# Cover size histogram
print("\n=== Cover size statistics ===")
cover_sizes = Counter()
for r in records:
    cover_sizes[len(r['cover'])] += 1
for k in sorted(cover_sizes):
    print(f"  |cover|={k}: {cover_sizes[k]} records")

# Rim vs spoke split in cover
print("\n=== Cover rim/spoke breakdown ===")
U, V = 0, 1
rim_counts = []
spoke_counts = []
for r in records:
    cover = [tuple(e) for e in r['cover']]
    rims = [e for e in cover if U not in e and V not in e]
    spokes = [e for e in cover if U in e or V in e]
    rim_counts.append(len(rims))
    spoke_counts.append(len(spokes))

rc = Counter(rim_counts)
sc = Counter(spoke_counts)
print(f"  Rim edges per cover: {dict(sorted(rc.items()))}")
print(f"  Spoke edges per cover: {dict(sorted(sc.items()))}")

# Packing triangles: how many hub edges (spokes) are used in packing?
print("\n=== Packing edge consumption ===")
total_packing_edges = 0
total_spoke_edges_in_packing = 0
total_rim_edges_in_packing = 0
for r in records:
    packing = [tuple(t) for t in r['packing']]
    for tri in packing:
        for a, b in combinations(tri, 2):
            e = (min(a,b), max(a,b))
            total_packing_edges += 1
            if U in e or V in e:
                total_spoke_edges_in_packing += 1
            else:
                total_rim_edges_in_packing += 1
print(f"  Total packing edge-slots: {total_packing_edges}")
print(f"  Spoke (hub-incident) edges used: {total_spoke_edges_in_packing}")
print(f"  Rim (non-hub) edges used: {total_rim_edges_in_packing}")
print(f"  Ratio spoke/total: {total_spoke_edges_in_packing/total_packing_edges:.3f}")

# Hub link analysis: uv edge as spoke
print("\n=== UV edge usage ===")
uv_in_packing_count = 0
uv_in_cover_count = 0
for r in records:
    packing = [tuple(t) for t in r['packing']]
    cover = [tuple(e) for e in r['cover']]
    uv_edges = []
    for tri in packing:
        for a, b in combinations(tri, 2):
            if (min(a,b), max(a,b)) == (0, 1):
                uv_in_packing_count += 1
    if (0, 1) in cover:
        uv_in_cover_count += 1
print(f"  Records where uv is an edge of some packing triangle: {uv_in_packing_count}")
print(f"  Records where uv is in cover: {uv_in_cover_count}")

# External rim edges in cover (not in core or side structure)
print("\n=== Structural decomposition of cover rims ===")
C4 = tuple(range(4))
CORE_EDGES = tuple(combinations(C4, 2))
CORE_TO_GLOBAL = {c: c + 2 for c in C4}
SIDE_EDGES_LOCAL = tuple((c, 4) for c in C4) + tuple((c, 5) for c in C4) + ((4, 5),)

core_rim_total = 0
side_rim_total = 0
cross_rim_total = 0
ab_rim_total = 0
other_rim_total = 0
for r in records:
    core = r['core_mask']
    left = r['left_side_mask']
    right = r['right_side_mask']
    cover = [tuple(e) for e in r['cover']]
    rims = [e for e in cover if U not in e and V not in e]

    # Compute core global edges
    core_global = set()
    for i, (x, y) in enumerate(CORE_EDGES):
        if (core >> i) & 1:
            gx, gy = CORE_TO_GLOBAL[x], CORE_TO_GLOBAL[y]
            core_global.add((min(gx, gy), max(gx, gy)))

    # Side edges (left side) global
    left_global = set()
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (left >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                ga = 6 + (ex - 4)
                left_global.add((min(gc, ga), max(gc, ga)))
            else:
                left_global.add((6, 7))

    right_global = set()
    for i, (c, ex) in enumerate(SIDE_EDGES_LOCAL):
        if (right >> i) & 1:
            if c < 4:
                gc = CORE_TO_GLOBAL[c]
                gb = 8 + (ex - 4)
                right_global.add((min(gc, gb), max(gc, gb)))
            else:
                right_global.add((8, 9))

    structural = core_global | left_global | right_global
    # Cross edges: (a,b) for a in {6,7}, b in {8,9}
    cross_set = {(a, b) for a in (6, 7) for b in (8, 9)}

    for e in rims:
        if e in core_global:
            core_rim_total += 1
        elif e in left_global or e in right_global:
            side_rim_total += 1
        elif e in cross_set:
            cross_rim_total += 1
        elif e in structural:
            side_rim_total += 1
        else:
            other_rim_total += 1

print(f"  Rim cover edges that are CORE edges: {core_rim_total}")
print(f"  Rim cover edges that are SIDE edges: {side_rim_total}")
print(f"  Rim cover edges that are CROSS (A-B) edges: {cross_rim_total}")
print(f"  Rim cover edges OTHER (not in guaranteed graph): {other_rim_total}")

# Check for potential further compression: does orbit size correlate with packing size?
print("\n=== Orbit size vs packing size correlation ===")
orbit_size_by_psize = defaultdict(list)
for pkey, members in packing_orbit_members.items():
    psize = len(records[members[0]]['packing'])
    orbit_size_by_psize[psize].append(len(members))

for ps in sorted(orbit_size_by_psize):
    sizes = orbit_size_by_psize[ps]
    print(f"  packing_size={ps}: mean orbit={sum(sizes)/len(sizes):.2f}, max={max(sizes)}, n_orbits={len(sizes)}")
