"""Role B, round 3 -- D request: decode the 21 saved core_mask=63 (K4 core) records.

Bounded scan of persisted witnesses only.  No new graphs are enumerated, no
solver/finder/census is run.  For each K4-core record we:
  * decode every common vertex c0..c3 to its unique A-neighbour and unique
    B-neighbour and VERIFY uniqueness (exactly one on each side),
  * build the 2x2 A-by-B multiplicity matrix (counts of common vertices per
    (A-side, B-side) attachment pair) plus its canonical (row/col permute and
    transpose) form,
  * record the side-edge flags a0a1 and b0b1,
  * print the original packing/cover with readable vertex labels.

Portable paths (relative to this file); pure standard library.
"""

import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "input" / "B_codegree4_certificates.json"

DOCUMENT = json.loads(SOURCE.read_text(encoding="utf-8"))
RECORDS = DOCUMENT["records"]
SIDE_BITS = [tuple(x) for x in DOCUMENT["side_bit_order"]]
LBL = DOCUMENT["vertex_labels"]

# readable label for a real vertex id
NAME = {}
NAME[LBL["u"]] = "u"
NAME[LBL["v"]] = "v"
for i, c in enumerate(LBL["common"]):
    NAME[c] = "c%d" % i
for i, c in enumerate(LBL["left_exclusive"]):
    NAME[c] = "a%d" % i
for i, c in enumerate(LBL["right_exclusive"]):
    NAME[c] = "b%d" % i
def rd(*vs):
    return "+".join(NAME[v] for v in vs)


def decode_side(mask, side_label):
    """Return {common_index: [neighbour real-vertex ids]}, and the private-edge flag."""
    verts = LBL["left_exclusive"] if side_label == "A" else LBL["right_exclusive"]
    nbrs = {}
    for c in range(4):
        got = []
        for i, (x, y) in enumerate(SIDE_BITS):
            if x == c and y in (4, 5) and mask >> i & 1:
                got.append(verts[y - 4])
        nbrs[c] = got
    # bit index for the side-side edge (x>=4) -- 4<->5
    priv = any(mask >> i & 1 for i, (x, y) in enumerate(SIDE_BITS) if x >= 4)
    return nbrs, priv


K4 = [(i, r) for i, r in enumerate(RECORDS) if r["core_mask"] == 63]

def canonical(mat):
    """Smallest 2x2 tuple over row/col swaps and transpose."""
    import itertools
    a = [list(r) for r in mat]
    forms = []
    for rowperm in itertools.permutations(range(2)):
        for colperm in itertools.permutations(range(2)):
            m = [[a[pr][pc] for pc in colperm] for pr in rowperm]
            forms.append(tuple(tuple(r) for r in m))
            t = [[m[j][i] for j in range(2)] for i in range(2)]
            forms.append(tuple(tuple(r) for r in t))
    return min(forms)


rows = []
uniq_ok = True
group = Counter()
for idx, r in K4:
    An, aprv = decode_side(r["left_side_mask"], "A")
    Bn, bprv = decode_side(r["right_side_mask"], "B")
    bad = [c for c in range(4) if len(An[c]) != 1 or len(Bn[c]) != 1]
    if bad:
        uniq_ok = False
    a0, a1 = LBL["left_exclusive"]
    mat = [[0, 0], [0, 0]]        # row: A-neighbour (a0,a1), col: B-neighbour (b0,b1)
    per_vertex = {}
    for c in range(4):
        ai = 0 if An[c] and An[c][0] == a0 else 1
        b0v = LBL["right_exclusive"][0]
        bi = 0 if Bn[c] and Bn[c][0] == b0v else 1
        mat[ai][bi] += 1
        per_vertex["c%d" % c] = {"A": rd(*An[c]), "B": rd(*Bn[c])}
    rows.append(dict(
        record_index=idx,
        key=[r["core_mask"], r["left_side_mask"], r["right_side_mask"]],
        unique_each_side=not bad, nonunique_common=bad,
        per_vertex=per_vertex,
        mult2x2_rows_a0a1_cols_b0b1=[mat[0], mat[1]],
        canonical_mult=canonical(mat),
        a0a1_edge=aprv, b0b1_edge=bprv,
        packing=[[NAME[x] for x in tt] for tt in r["packing"]],
        cover=[sorted([NAME[x] for x in e]) for e in r["cover"]],
    ))
    group[canonical(mat)] += 1

A0, A1 = LBL["left_exclusive"]
B0, B1 = LBL["right_exclusive"]
summary = dict(
    note=("Catalogue-only decode of the 21 saved K4-core (core_mask=63) records; "
          "no new graphs enumerated, no solver/finder."),
    source=SOURCE.name,
    num_core63_records=len(K4),
    all_common_vertices_have_unique_A_and_B_neighbour=uniq_ok,
    side_edge_legend={"A0": NAME[A0], "A1": NAME[A1], "B0": NAME[B0], "B1": NAME[B1]},
    mult_matrix_legend="2x2: rows=A-neighbour(a0,a1) x cols=B-neighbour(b0,b1); entry=#common vertices; total=4",
    canonical_matrix_group_counts={
        "flat" + "".join(str(v) for row in m for v in row): {"matrix": [list(r) for r in m], "count": c}
        for m, c in sorted(group.items())
    },
    records=rows,
)
(HERE / "k4_saved_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

lines = []
lines.append("Role B round3 -- D request: 21 saved core_mask=63 (K4) records. Catalogue only;")
lines.append("no new graphs enumerated, no solver/finder. JSON: k4_saved_summary.json")
lines.append("")
lines.append("UNIQUENESS CHECK: every c0..c3 has exactly one A-neighbour and one B-neighbour"
             " in all %d records: %s" % (len(K4), uniq_ok))
lines.append("2x2 matrix legend: rows = A-neighbour (%s,%s); cols = B-neighbour (%s,%s); entry = #common." %
             (NAME[A0], NAME[A1], NAME[B0], NAME[B1]))
lines.append("")
lines.append("Distinct canonical multiplicity patterns (count):")
for m, c in sorted(group.items()):
    lines.append("  %s x%d" % ([list(r) for r in m], c))
lines.append("")
for row in rows:
    lines.append("record %d  key=%s  a0a1=%s b0b1=%s  unique=%s" %
                 (row["record_index"], row["key"], row["a0a1_edge"], row["b0b1_edge"],
                  row["unique_each_side"]))
    lines.append("   per-common: " + " ".join("%s->A:%s B:%s" % (k, v["A"], v["B"])
                                              for k, v in sorted(row["per_vertex"].items())))
    lines.append("   2x2 [[a0b0,a0b1],[a1b0,a1b1]]= %s   canonical=%s" %
                 (row["mult2x2_rows_a0a1_cols_b0b1"], [list(x) for x in row["canonical_mult"]]))
    lines.append("   packing: " + " ".join("+".join(t) for t in row["packing"]))
    lines.append("   cover:   " + " ".join("".join(e) for e in row["cover"]))
    lines.append("")
(HERE / "k4_saved_summary.txt").write_text("\n".join(lines), encoding="utf-8")

print("core63 records:", len(K4), " unique attachments verified:", uniq_ok)
print("distinct canonical multiplicity patterns:", len(group))
for m, c in sorted(group.items()):
    print("  ", [list(r) for r in m], "x", c)
print("Wrote", HERE / "k4_saved_summary.txt", "and", HERE / "k4_saved_summary.json")
