"""Role B, round 3 -- bounded scan of SAVED 1144 certificates only.

No graph census and no certificate finder are re-run.  Everything below reads
the already-persisted witnesses in ``compression/input/B_codegree4_certificates.json``
and the already-exported nine templates in ``compression/templates/optimal_templates.json``.
Paths are portable (resolved relative to this file).  Pure standard-library Python.

The 7-vertex link used for the WKE test is the SAME notion used by
``compression/round3/C/check_leaf_links.py``: hub vertex 6, four common vertices
0..3 (``C``), two private/side vertices 4,5 (``A`` or ``B``).  Fixed edges are the
four hub--common spokes plus the core edges selected by ``core_mask``; the nine
optional edges are selected by the side mask via the document's ``side_bit_order``.
"""

import json
from collections import Counter
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "input" / "B_codegree4_certificates.json"
TEMPLATES = HERE.parent.parent / "templates" / "optimal_templates.json"

DOCUMENT = json.loads(SOURCE.read_text(encoding="utf-8"))
RECORDS = DOCUMENT["records"]
SIDE_BITS = [tuple(x) for x in DOCUMENT["side_bit_order"]]
CORE_BITS = [tuple(x) for x in DOCUMENT["core_bit_order"]]
LABELS = DOCUMENT["vertex_labels"]
CORE = list(LABELS["common"])                       # c0..c3 -> real labels 2..5
SIDES = {"left": list(LABELS["left_exclusive"]),    # a0,a1 -> 6,7
         "right": list(LABELS["right_exclusive"])}  # b0,b1 -> 8,9

# The two cores named by the E request (given in the saved core_bit_order labelling).
FOCUS_CORES = (3, 7)


# --------------------------------------------------------------------------- #
# decoders
# --------------------------------------------------------------------------- #
def core_edges(mask):
    return {CORE_BITS[i] for i in range(6) if mask >> i & 1}


def side_edges(mask):
    """Abstract side edges in the 7-vertex link: (c,4)/(c,5) plus (4,5)."""
    out = set()
    for i, (x, y) in enumerate(SIDE_BITS):
        if mask >> i & 1:
            out.add((x, y) if x < 4 else (4, 5))
    return out


def real_side_edges(mask, side):
    """Real-vertex attachment edges for one side (for evidence listing)."""
    a0, a1 = SIDES[side]
    pair = {4: a0, 5: a1}
    out = []
    for i, (x, y) in enumerate(SIDE_BITS):
        if mask >> i & 1:
            if x < 4:
                out.append(sorted((CORE[x], pair[y])))
            else:
                out.append(sorted((a0, a1)))
    return out


def core_profile(mask):
    """Return (leaves, isolated, center) of the core graph by degree."""
    deg = Counter()
    for u, v in core_edges(mask):
        deg[u] += 1
        deg[v] += 1
    leaves = sorted(v for v in range(4) if deg[v] == 1)
    isolated = sorted(v for v in range(4) if deg[v] == 0)
    center = max(range(4), key=lambda v: (deg[v], -v))
    return leaves, isolated, center


# WKE test identical in spirit to round3/C/check_leaf_links.py ------------- #
def connected(edges):
    seen = {6}
    while True:
        new = seen | {v for e in edges for v in e if set(e) & seen}
        if new == seen:
            return len(seen) == 7
        seen = new


def _matchings(edges):
    yield frozenset()
    for k in range(1, 4):
        for es in combinations(edges, k):
            if len({v for e in es for v in e}) == 2 * k:
                yield frozenset(es)


def is_wke(edges):
    for m in _matchings(edges):
        for qsize in range(len(m) + 1):
            for subset in combinations(range(7), qsize):
                q = set(subset)
                if all(e in m or e[0] in q or e[1] in q for e in edges):
                    return True
    return False


def link_edges(core_mask, side_mask):
    return core_edges(core_mask) | {(c, 6) for c in range(4)} | side_edges(side_mask)


# --------------------------------------------------------------------------- #
# per-side classification over the saved records
# --------------------------------------------------------------------------- #
def record_key(idx):
    r = RECORDS[idx]
    return [r["core_mask"], r["left_side_mask"], r["right_side_mask"]]


side_rows = []          # every analysed side of every record (all cores)
focus_sides = []        # named-core sides whose actual-leaf support <= 1
sig = {}                # (core, side) -> Counter of signature -> count / sample keys
for idx, r in enumerate(RECORDS):
    cm = r["core_mask"]
    leaves, isolated, center = core_profile(cm)
    for side in ("left", "right"):
        sm = r[side + "_side_mask"]
        E = side_edges(sm)
        L = link_edges(cm, sm)
        wke = is_wke(L)
        conn = connected(L)
        # star leaves = degree-1 common vertices; isolated excluded automatically
        sup_leaves = sorted(c for c in leaves if (c, 4) in E or (c, 5) in E)
        center_att = sorted(pair for pair in (4, 5) if (center, pair) in E)
        private = (4, 5) in E
        row = dict(core_mask=cm, side=side, side_mask=sm,
                   leaves=leaves, isolated=isolated, center=center,
                   leaf_support=len(sup_leaves), leaf_support_set=sup_leaves,
                   center_attach_deg=len(center_att), private_edge=private,
                   wke=wke, connected=conn, key=record_key(idx), index=idx)
        side_rows.append(row)
        if cm in FOCUS_CORES:
            s = (row["leaf_support"], row["center_attach_deg"], int(private))
            bucket = sig.setdefault((cm, side), {"counter": Counter(), "example": {}})
            bucket["counter"][s] += 1
            bucket["example"].setdefault(s, [record_key(idx), idx])
            if row["leaf_support"] <= 1:
                focus_sides.append(row)

# global tally (whole saved catalogue, all cores) --------------------------- #
global_wke = Counter((row["wke"], row["connected"]) for row in side_rows)

# --------------------------------------------------------------------------- #
# hypotheses (tested against saved data only)
# --------------------------------------------------------------------------- #
def counterexamples(pred):
    return [row["key"] for row in side_rows if pred(row)]

H_star_nonWKE_ge2 = counterexamples(
    lambda r: r["core_mask"] == 7 and (not r["wke"]) and r["leaf_support"] < 2)
H_p3_ge1 = counterexamples(
    lambda r: r["core_mask"] == 3 and r["leaf_support"] < 1)
H_p3_singleton_center = counterexamples(
    lambda r: r["core_mask"] == 3 and r["leaf_support"] == 1 and r["center_attach_deg"] != 2)
p3_singleton_count = sum(1 for r in side_rows
                         if r["core_mask"] == 3 and r["leaf_support"] == 1)

# --------------------------------------------------------------------------- #
# coverage matrix: 9 saved core masks x 9 prior templates (from assignments)
# --------------------------------------------------------------------------- #
TDATA = json.loads(TEMPLATES.read_text(encoding="utf-8"))
CANDIDATE_IDS = TDATA["candidate_ids"]
cov = {}
for a in TDATA["assignments"]:
    cm = RECORDS[a["record_index"]]["core_mask"]
    cov.setdefault(cm, Counter())[a["template"]] += 1
cores_sorted = sorted(cov)
matrix = []
for cm in cores_sorted:
    matrix.append(dict(core_mask=cm,
                       core_profile=list(core_profile(cm)),
                       applies_to_templates=[i for i in range(9) if cov[cm].get(i, 0)],
                       applies_to_candidate_ids=[CANDIDATE_IDS[i] for i in range(9) if cov[cm].get(i, 0)],
                       counts_by_template={str(i): cov[cm].get(i, 0) for i in range(9)},
                       total=sum(cov[cm].values())))

# --------------------------------------------------------------------------- #
# evidence bundle
# --------------------------------------------------------------------------- #
evidence = dict(
    note=("Catalogue-only bounded computation on the saved 1144 records. No census, "
          "no certificate finder, no proof claim."),
    source=str(SOURCE.name),
    num_records=len(RECORDS),
    global_side_link_wke_connected_tally={f"wke={k[0]},connected={k[1]}": v
                                          for k, v in sorted(global_wke.items(), key=str)},
    named_core_signature_catalogue={
        f"core{cm}|{side}": {
            "leaf_support_excludes_isolated": True if cm == 3 else False,
            "star_leaves": core_profile(cm)[0], "isolated": core_profile(cm)[1],
            "center": core_profile(cm)[2],
            "signatures_support_cdeg_private": [
                {"leaf_support": s[0], "center_attach_deg": s[1], "private_edge": bool(s[2]),
                 "count": c, "example_key": sig[(cm, side)]["example"][s][0],
                 "example_index": sig[(cm, side)]["example"][s][1]}
                for s, c in sorted(sig[(cm, side)]["counter"].items())],
        } for (cm, side) in sorted(sig)
    },
    focus_zero_or_one_leaf_sides=dict(
        definition=("named cores 3/7 side links whose attached actual star leaves <= 1"),
        count=len(focus_sides),
        distinct_side_masks=sorted({row["side_mask"] for row in focus_sides}),
        records=[dict(key=row["key"], index=row["index"], core_mask=row["core_mask"],
                      side=row["side"], side_mask=row["side_mask"],
                      leaf_support=row["leaf_support"],
                      attachment_edges_real=real_side_edges(row["side_mask"], row["side"]))
                 for row in focus_sides],
    ),
    hypotheses=dict(
        scope="saved records only; NOT a census-free proof",
        H_star_nonWKE_leaf_support_ge2=dict(
            statement="every non-WKE side of core 7 (K1,3) has leaf support >= 2",
            holds=not H_star_nonWKE_ge2, counterexamples=H_star_nonWKE_ge2[:50],
            num_counterexamples=len(H_star_nonWKE_ge2)),
        H_p3_leaf_support_ge1=dict(
            statement="every side of core 3 (P3+isolated) has leaf support >= 1",
            holds=not H_p3_ge1, counterexamples=H_p3_ge1[:50],
            num_counterexamples=len(H_p3_ge1)),
        H_p3_singleton_center_both=dict(
            statement=("if a core-3 side has singleton leaf support then the center "
                       "attaches to BOTH private vertices"),
            num_p3_singleton_sides=p3_singleton_count,
            holds=(p3_singleton_count == 0) or (not H_p3_singleton_center),
            vacuous=(p3_singleton_count == 0),
            counterexamples=H_p3_singleton_center[:50],
            num_counterexamples=len(H_p3_singleton_center)),
    ),
    coverage_by_core_matrix=dict(
        row_order=cores_sorted,
        template_candidate_ids=CANDIDATE_IDS,
        rows=matrix),
)

(HERE / "e_core3_7_analysis.json").write_text(json.dumps(evidence, indent=2), encoding="utf-8")

print("saved records:", len(RECORDS), " sides analysed:", len(side_rows))
print("global side-link (wke,connected) tally:",
      {f"wke={k[0]},conn={k[1]}": v for k, v in global_wke.items()})
for cm in FOCUS_CORES:
    lv, iso, cen = core_profile(cm)
    print(f"core {cm}: star_leaves={lv} isolated={iso} center={cen}")
print("focus (zero/one leaf) sides:", len(focus_sides))
print("H_star_ge2 holds:", not H_star_nonWKE_ge2,
      "| H_p3_ge1 holds:", not H_p3_ge1,
      "| p3 singletons:", p3_singleton_count,
      "| H_singleton holds:", (p3_singleton_count == 0) or (not H_p3_singleton_center))
print("coverage matrix written; cores:", cores_sorted)
print("Wrote", HERE / "e_core3_7_analysis.json")
