"""Tiny exhaustive checks of seven-vertex links for two fixed four-vertex cores.

This enumerates only the 9 optional edges in one link; it is not the
codegree-four configuration census or a certificate finder.
"""

from itertools import combinations


def connected(edges):
    seen = {6}
    while True:
        new = seen | {v for x, y in edges for v in (x, y)
                      if x in seen or y in seen}
        if new == seen:
            return len(seen) == 7
        seen = new


def matchings(edges):
    yield frozenset()
    for k in range(1, 4):
        for es in combinations(edges, k):
            if len({v for e in es for v in e}) == 2 * k:
                yield frozenset(es)


def wke(edges):
    for matching in matchings(edges):
        for qsize in range(len(matching) + 1):
            for subset in combinations(range(7), qsize):
                q = set(subset)
                if all(e in matching or e[0] in q or e[1] in q for e in edges):
                    return matching, tuple(sorted(q))
    return None


for name, core, leaves in (
    ("P3+isolated", ((0, 1), (1, 2)), (0, 2)),
    ("K1,3", ((0, 1), (0, 2), (0, 3)), (1, 2, 3)),
):
    base = tuple(sorted(core + tuple((c, 6) for c in range(4))))
    optional = tuple((c, a) for c in range(4) for a in (4, 5)) + ((4, 5),)
    examples = {}
    counts = {}
    for mask in range(1 << 9):
        edges = tuple(sorted(base + tuple(e for i, e in enumerate(optional)
                                          if mask & (1 << i))))
        if not connected(edges) or wke(edges) is not None:
            continue
        support = tuple(c for c in leaves if any((c, a) in edges for a in (4, 5)))
        counts[len(support)] = counts.get(len(support), 0) + 1
        examples.setdefault(len(support), edges)
    print(name, "non-WKE connected link counts by actual-leaf support:", counts)
    for k, edges in sorted(examples.items()):
        print("  support", k, "example:", edges)
