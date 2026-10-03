import json, sys, os
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
CORE = {2, 3, 4, 5, 6}
HUBS = {0, 1}

# Independently generate graph from definition (not from witness)
edges = set()
edges.add((0, 1))                      # uv
for c in CORE:                         # u to CORE and 7
    edges.add(tuple(sorted((0, c))))
    edges.add(tuple(sorted((7, c))))
edges.add((0, 7))
for c in CORE:                         # v to CORE and 8,9
    edges.add(tuple(sorted((1, c))))
    edges.add(tuple(sorted((8, c))))
    edges.add(tuple(sorted((9, c))))
edges.add((1, 8)); edges.add((1, 9)); edges.add((8, 9))
for a, b in combinations(sorted(CORE), 2):   # core complete except 2-3
    if {a, b} != {2, 3}:
        edges.add((a, b))
E = edges

def tri_exists(t):
    a, b, c = t
    return (tuple(sorted((a, b))) in E and tuple(sorted((a, c))) in E
            and tuple(sorted((b, c))) in E)

def canon(t):
    return tuple(sorted(t))

with open(os.path.join(HERE, "repaired_fano.json")) as f:
    w = json.load(f)
S = [tuple(t) for t in w["S"]]
X_raw = [tuple(sorted(e)) for e in w["X"]]
X = set(X_raw)
E_raw = [tuple(sorted(e)) for e in w["edges"]]
fail = []

if len(E_raw) != len(set(E_raw)) or set(E_raw) != E:
    fail.append(f"witness graph differs from generated graph: missing={sorted(E-set(E_raw))}, extra={sorted(set(E_raw)-E)}")
if len(X_raw) != len(X):
    fail.append("duplicate X edge")

# 1. distinct 3 vertices per triangle
if any(len(set(t)) != 3 or len(t) != 3 for t in S):
    fail.append("triangle with non-distinct vertices")

# 2. every triangle exists in graph
for t in S:
    if len(t) == 3 and len(set(t)) == 3 and not tri_exists(t):
        fail.append(f"triangle {t} does not exist in graph")

# 3. edge disjointness of S
seen = set()
for t in S:
    for a, b in combinations(t, 2):
        e = tuple(sorted((a, b)))
        if e in seen:
            fail.append(f"edge {e} shared between triangles")
        seen.add(e)

# 4. X subset E
for e in X:
    if e not in E:
        fail.append(f"X edge {e} not in graph")

# 5. cardinalities
if len(S) != 7: fail.append(f"|S|={len(S)} != 7")
if len(X) != 14: fail.append(f"|X|={len(X)} != 14")
if len(X) > 2 * len(S): fail.append("|X| > 2|S|")

# 6. all graph triangles touching {0,1} are hit by X
graph_tris = set()
for tri in combinations(range(10), 3):
    if tri_exists(tri):
        graph_tris.add(tri)
for t in graph_tris:
    if HUBS & set(t) and not any(tuple(sorted(e)) in X for e in combinations(t, 2)):
        fail.append(f"hub triangle {t} not hit by X")

# 7. every packed edge (edge of some triangle in S) with both endpoints NOT in {0,1} is in X
packed = set()
for t in S:
    for a, b in combinations(t, 2):
        packed.add(tuple(sorted((a, b))))
for e in packed:
    if e[0] in HUBS or e[1] in HUBS:
        continue
    if e not in X:
        fail.append(f"packed edge {e} not in X")

result = {
    "num_vertices": 10, "num_edges": len(E), "num_S": len(S), "num_X": len(X),
    "num_graph_triangles": len(graph_tris),
    "num_hub_triangles": sum(bool(HUBS & set(t)) for t in graph_tris),
    "witness_graph_equals_generated_ok": not any("witness graph differs" in m for m in fail),
    "X_distinct_ok": len(X_raw) == len(X),
    "distinct_vertices_ok": not any("non-distinct" in m for m in fail),
    "triangles_exist_ok": not any("does not exist" in m for m in fail),
    "edge_disjoint_ok": not any("shared" in m for m in fail),
    "X_subset_E_ok": not any("not in graph" in m for m in fail),
    "cardinalities_ok": len(S) == 7 and len(X) == 14 and len(X) <= 2 * len(S),
    "hub_triangles_hit_ok": not any("not hit" in m for m in fail),
    "packed_edges_in_X_ok": not any("packed edge" in m for m in fail),
    "failures": fail,
}
print(json.dumps(result, indent=2))
if fail:
    sys.exit(1)
