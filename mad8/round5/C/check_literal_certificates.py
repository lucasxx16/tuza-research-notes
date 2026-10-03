"""Independent exact checker for the two fixed round-five B instances.

This uses only the Python standard library. It reconstructs each graph from
its stated definition, compares any exported graph, and tests all three
reducibility conditions. It performs no certificate search.
"""

import json
from itertools import combinations
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "B"
HUBS = {0, 1}


def edge(a, b):
    if a == b:
        raise ValueError("loop")
    return tuple(sorted((a, b)))


def graph_p3_k2():
    edges = set()

    def add(a, b):
        edges.add(edge(a, b))

    core = range(2, 7)
    add(0, 1)
    for c in core:
        add(0, c)
        add(1, c)
        add(7, c)
        add(8, c)
        add(9, c)
    add(0, 7)
    add(1, 8)
    add(1, 9)
    add(8, 9)
    for a, b in combinations(core, 2):
        if (a, b) not in {(2, 3), (3, 4)}:
            add(a, b)
    return 10, edges


def graph_mutual_center():
    edges = set()

    def add(a, b):
        edges.add(edge(a, b))

    core = range(2, 6)
    add(0, 1)
    for c in core:
        add(0, c)
        add(1, c)
        for a in (6, 7, 8, 9):
            add(a, c)
    for a in (6, 7):
        add(0, a)
    for b in (8, 9):
        add(1, b)
    add(6, 7)
    add(8, 9)
    for a, b in combinations(core, 2):
        if (a, b) != (2, 3):
            add(a, b)
    return 10, edges


def graph_triangles(n, edges):
    return {t for t in combinations(range(n), 3)
            if all(edge(a, b) in edges for a, b in combinations(t, 2))}


def audit(data, n, edges, *, p3_restrictions=False):
    problems = []
    graph_record = data.get("instance", {}).get("edges")
    if graph_record is not None:
        exported = [edge(*e) for e in graph_record]
        if len(exported) != len(set(exported)) or set(exported) != edges:
            problems.append("exported graph differs from independently reconstructed graph")

    raw_s = data.get("S", [])
    raw_x = data.get("X", [])
    try:
        s = [tuple(sorted(t)) for t in raw_s]
        x_list = [edge(*e) for e in raw_x]
    except (TypeError, ValueError):
        return ["malformed S or X entry"], 0, 0
    x = set(x_list)
    triangles = graph_triangles(n, edges)
    hub_triangles = [t for t in triangles if HUBS.intersection(t)]

    if any(len(t) != 3 or len(set(t)) != 3 for t in s):
        problems.append("S has a non-triple or repeated vertex")
    if len(s) != len(set(s)):
        problems.append("S repeats a triangle")
    if any(t not in triangles for t in s):
        problems.append("S contains a nontriangle")
    used = [edge(a, b) for t in s if len(t) == 3 for a, b in combinations(t, 2)]
    if len(used) != 3 * len(s) or len(used) != len(set(used)):
        problems.append("S is not edge-disjoint")
    if len(x) != len(x_list):
        problems.append("X repeats an edge")
    if not x.issubset(edges):
        problems.append("X contains a nongraph edge")
    for t in hub_triangles:
        if not any(edge(a, b) in x for a, b in combinations(t, 2)):
            problems.append(f"uncovered hub triangle {t}")
            break
    for e in used:
        if not HUBS.intersection(e) and e not in x:
            problems.append(f"packed external edge {e} absent from X")
            break
    if len(x) > 2 * len(s):
        problems.append("budget violation")
    if p3_restrictions:
        if any({8, 9}.intersection(t) for t in s):
            problems.append("S violates no-B restriction")
        if not {(1, 8), (1, 9)}.issubset(x):
            problems.append("forced v-B spokes absent")
        if any({8, 9}.intersection(e) and e not in {(1, 8), (1, 9)} for e in x):
            problems.append("forbidden B-incident X edge")
    return problems, len(triangles), len(hub_triangles)


def check_case(filename, graph_builder, *, p3_restrictions=False):
    n, edges = graph_builder()
    data = json.loads((ROOT / filename).read_text(encoding="utf-8"))
    problems, nt, nh = audit(data, n, edges, p3_restrictions=p3_restrictions)
    if problems:
        raise AssertionError(f"{filename}: {problems}")

    # Negative controls: each mutation must be rejected for the intended reason.
    s = data["S"]
    x = data["X"]
    external = next(edge(a, b) for t in s for a, b in combinations(t, 2)
                    if not HUBS.intersection((a, b)))
    bad = dict(data, X=[e for e in x if edge(*e) != external])
    issues, _, _ = audit(bad, n, edges, p3_restrictions=p3_restrictions)
    assert any("packed external edge" in issue for issue in issues)

    bad = dict(data, X=x + [[0, 9]])
    issues, _, _ = audit(bad, n, edges, p3_restrictions=p3_restrictions)
    assert any("nongraph edge" in issue for issue in issues)

    bad = dict(data, S=s + [s[0]])
    issues, _, _ = audit(bad, n, edges, p3_restrictions=p3_restrictions)
    assert any("repeats a triangle" in issue or "not edge-disjoint" in issue
               for issue in issues)
    return {"case": filename, "edges": len(edges), "triangles": nt,
            "hub_triangles": nh, "packing": len(s), "cover": len(x),
            "all_conditions": True, "negative_controls": 3}


if __name__ == "__main__":
    print(check_case("witness.json", graph_p3_k2, p3_restrictions=True))
    print(check_case("mutual_centers_witness.json", graph_mutual_center))
    # Separately printed human 8/16 control in B's second report.
    human = {
        "S": [[0, 2, 6], [0, 3, 7], [0, 4, 5], [1, 2, 4],
              [1, 3, 5], [1, 8, 9], [2, 5, 9], [3, 4, 9]],
        "X": [[2, 4], [2, 5], [3, 4], [3, 5], [4, 5],
              [2, 9], [3, 9], [4, 9], [5, 9], [2, 6],
              [3, 7], [8, 9], [0, 1], [0, 6], [0, 7], [1, 8]],
    }
    problems, _, _ = audit(human, *graph_mutual_center())
    assert not problems, problems
    print({"case": "reported human 8/16 control", "all_conditions": True})
