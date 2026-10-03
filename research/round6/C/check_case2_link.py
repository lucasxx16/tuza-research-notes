"""One specified diagnostic for E's proposed diamond case (2), not a search."""
import itertools

core = {frozenset(e) for e in [("p", "q"), ("p", "x"), ("p", "y"),
                                ("q", "x"), ("q", "y")]}


def wke(edges):
    V = {v for e in edges for v in e}
    for r in range(4):
        for q0 in itertools.combinations(V, r):
            Q = set(q0)
            outside = {e for e in edges if not e & Q}
            # Any witness matching must contain all outside edges.
            if len({v for e in outside for v in e}) != 2 * len(outside):
                continue
            for m in range(len(outside), 4):
                for M in itertools.combinations(edges, m):
                    if len({v for e in M for v in e}) == 2 * m and outside <= set(M) and r <= m:
                        return Q, M
    return None


def link(side, priv):
    E = core | {frozenset(("z", c)) for c in ("p", "q", "x", "y")}
    E |= {frozenset(e) for e in side}
    if priv:
        E.add(frozenset((side[0][0], side[-1][0])))
    return E


A = [("a", "p"), ("a", "x"), ("a", "y"),
     ("b", "q"), ("b", "x"), ("b", "y")]
B = [("c", "p"), ("c", "q"), ("d", "x"), ("d", "y")]
for ai, bi in itertools.product((False, True), repeat=2):
    print({"ab": ai, "cd": bi, "A_WKE": wke(link(A, ai)), "B_WKE": wke(link(B, bi))})
