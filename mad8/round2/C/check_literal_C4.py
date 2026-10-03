"""Independent check of the fixed five-triangle C4-core witness only."""

import itertools
import json
from pathlib import Path


def edge(x, y):
    return tuple(sorted((x, y)))


def tri_edges(t):
    return {edge(x, y) for x, y in itertools.combinations(t, 2)}


# Literal graph: hubs 0,1; core 2..7 with missing 23,45;
# vertex 8 adjacent to 1 and all six core vertices.
core = tuple(range(2, 8))
E = {edge(0, 1), edge(1, 8)}
E |= {edge(h, c) for h in (0, 1) for c in core}
E |= {edge(8, c) for c in core}
E |= {edge(a, b) for a, b in itertools.combinations(core, 2)
      if edge(a, b) not in {(2, 3), (4, 5)}}

path = Path(__file__).resolve().parents[1] / "B" / "witness.json"
saved = json.loads(path.read_text(encoding="utf-8"))
S = [tuple(t) for t in saved["witness"]["S"]]
X = {tuple(e) for e in saved["witness"]["X"]}
assert len(S) == 5 and len(X) == 10
assert len(X) == len(saved["witness"]["X"]) and X <= E
used = set()
for t in S:
    te = tri_edges(t)
    assert len(t) == len(set(t)) == 3 and te <= E and not (te & used)
    used |= te
assert len(used) == 15
assert all(tri_edges(t) & X for t in itertools.combinations(range(9), 3)
           if (0 in t or 1 in t) and tri_edges(t) <= E)
assert all(e in X for t in S for e in tri_edges(t)
           if 0 not in e and 1 not in e)
print("Independent literal C4 certificate: PASS (5 triangles, 10 cover edges)")
