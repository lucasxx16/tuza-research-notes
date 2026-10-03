import json, itertools, os
U, V, B = 0, 1, 8
HUBS = {U, V}
CORE = tuple(range(2, 8))
MISSING = [(2, 3), (4, 5)]
hub_edges = [(a, b) for a, b in itertools.combinations(CORE, 2) if (a, b) not in MISSING]
E = sorted(tuple(sorted(e)) for e in (
    [(U, V)] + [(U, h) for h in CORE] + [(V, h) for h in CORE]
    + hub_edges + [(V, B)] + [(B, h) for h in CORE]))
Es = set(E)
# hand witness, normalized edges
S = sorted(tuple(sorted(t)) for t in [(0,1,6),(0,2,4),(0,3,5),(1,4,3),(1,5,2)])
X = sorted(tuple(sorted(e)) for e in [(0,1),(0,6),(0,7),(1,6),(1,7),(1,8),
                                      (2,4),(3,4),(3,5),(2,5)])
adj = {i: set() for i in range(9)}
for a, b in E: adj[a].add(b); adj[b].add(a)
def lit_tri(t):
    a, b, c = t
    return b in adj[a] and c in adj[a] and c in adj[b]
core_adj = {i: set() for i in range(8)}
for a, b in E:
    if a < 8 and b < 8: core_adj[a].add(b); core_adj[b].add(a)
# packed triangles allowed: literal triangles entirely on 0..7
packed_tris = sorted(tuple(sorted(t)) for t in itertools.combinations(range(8), 3)
                     if lit_tri(t))
tris01 = sorted({tuple(sorted((x, y, z))) for x in (U, V)
                 for y, z in itertools.combinations(sorted(adj[x]), 2) if z in adj[y]})
tri_edges = lambda t: [tuple(sorted(e)) for e in itertools.combinations(t, 2)]
used = {}
for t in S:
    for e in tri_edges(t): used[e] = used.get(e, 0) + 1
Xs = set(X)
checks = {
  "S_are_literal_packed_triangles_on_0_7": all(t in packed_tris for t in S),
  "packing_avoids_vertex_8": all(8 not in t for t in S),
  "packing_edge_disjoint": all(v == 1 for v in used.values()),
  "X_has_distinct_edges": len(X) == len(Xs),
  "X_subset_E": all(e in Es for e in X),
  "X_hits_every_graph_triangle_touching_0_or_1": all(
      any(e in Xs for e in tri_edges(T)) for T in tris01),
  "X_contains_selected_packed_edges_avoiding_hubs": all(
      e in Xs for t in S for e in tri_edges(t)
      if e[0] not in HUBS and e[1] not in HUBS),
  "bound_10le2x5": len(X) <= 2 * len(S),
  "forced_X_1_8": (1, 8) in Xs,
  "no_u_b_edge_in_X": (0, 8) not in Xs,
}
obj = len(X) - 2 * len(S)
out = {"witness": {"S": [list(t) for t in S], "X": [list(e) for e in X]},
       "counts": {"|S|": len(S), "|X|": len(X),
                  "objective_|X|-2|S|": obj, "n_packed_triangles_available": len(packed_tris),
                  "n_graph_tris_touching_01": len(tris01)},
       "graph_edges_E": [list(e) for e in E],
       "literal_tris01": [list(t) for t in tris01],
       "verification": checks, "all_checks_pass": all(checks.values())}
d = os.path.dirname(os.path.abspath(__file__))
json.dump(out, open(os.path.join(d, "witness.json"), "w"), indent=1)
print("all_checks_pass:", all(checks.values()), "| obj:", obj)
for k, v in checks.items(): print(" ", k, "=", v)
if not all(checks.values()):
    raise SystemExit(1)
