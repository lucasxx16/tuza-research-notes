"""Role B, round 3 -- focused E request on SAVED core_mask=13 records only.

core_mask 13 = core_bit_order bits {0,2,3} = edges c0c1, c0c3, c1c2, which is the
four-vertex path  c3-c0-c1-c2  (a P4).  The path order p-q-r-s is DERIVED from the
core graph's degrees (endpoints = degree 1, internal = degree 2), never assumed
from indices.

Condition under test (a structural signal for the known 5-triangle template):
    does there exist a pair of common vertices at core graph-distance 2 such that
    one is attached (via its side mask) to an A-vertex and the other to a
    B-vertex?  Either orientation counts ("allow reversal").

A "failure" = a saved record with NO such cross distance-2 pair.

Bounded scan of persisted witnesses only: no new graphs enumerated, no finder,
no solver, no census.  Pure standard library, portable (relative) paths.
"""

import json
from collections import Counter, deque
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "input" / "B_codegree4_certificates.json"

DOCUMENT = json.loads(SOURCE.read_text(encoding="utf-8"))
RECORDS = DOCUMENT["records"]
SIDE_BITS = [tuple(x) for x in DOCUMENT["side_bit_order"]]
CORE_BITS = [tuple(x) for x in DOCUMENT["core_bit_order"]]
LBL = DOCUMENT["vertex_labels"]
CORE = list(LBL["common"])                 # c0..c3 -> 2,3,4,5
A0, A1 = LBL["left_exclusive"]
B0, B1 = LBL["right_exclusive"]
NAME = {LBL["u"]: "u", LBL["v"]: "v"}
for i, c in enumerate(CORE):
    NAME[c] = "c%d" % i
NAME[A0], NAME[A1], NAME[B0], NAME[B1] = "a0", "a1", "b0", "b1"


def core_edges(mask):
    return {CORE_BITS[i] for i in range(6) if mask >> i & 1}


def dist2_pairs(mask):
    """All unordered common-vertex pairs at core graph-distance exactly 2."""
    ce = core_edges(mask)
    adj = {v: set() for v in range(4)}
    for u, v in ce:
        adj[u].add(v)
        adj[v].add(u)
    out = []
    for s in range(4):
        d = {s: 0}
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in d:
                    d[y] = d[x] + 1
                    dq.append(y)
        out += [tuple(sorted((s, t))) for t in range(4) if d.get(t) == 2]
    return sorted(set(out))


def p4_path(mask):
    """Return (p,q,r,s) common indices by degree (endpoints first/last)."""
    ce = core_edges(mask)
    deg = Counter()
    for u, v in ce:
        deg[u] += 1
        deg[v] += 1
    adj = {v: sorted({w for e in ce for w in e if v in e and w != v}) for v in range(4)}
    ends = sorted(v for v in range(4) if deg[v] == 1)
    if len(ends) != 2:
        return None
    p = ends[0]
    path = [p]
    prev, cur = None, p
    while len(path) < 4:
        nxt = next(w for w in adj[cur] if w != prev)
        path.append(nxt)
        prev, cur = cur, nxt
    return tuple(path)


def attached_common(mask):
    """Common indices with at least one side edge (to either exclusive vertex)."""
    out = set()
    for i, (x, y) in enumerate(SIDE_BITS):
        if mask >> i & 1 and x < 4:
            out.add(x)
    return out


def private_edge(mask):
    return any(mask >> i & 1 for i, (x, y) in enumerate(SIDE_BITS) if x >= 4)


def att_matrix(r):
    """For each common vertex, the A-neighbours and B-neighbours it is attached to."""
    m = {}
    for c in range(4):
        a = [NAME[v] for i, (x, y) in enumerate(SIDE_BITS)
             if x == c and y == 4 and r["left_side_mask"] >> i & 1 for v in [A0]]
        a += [NAME[A1] for i, (x, y) in enumerate(SIDE_BITS) if x == c and y == 5 and r["left_side_mask"] >> i & 1]
        b = [NAME[B0] for i, (x, y) in enumerate(SIDE_BITS) if x == c and y == 4 and r["right_side_mask"] >> i & 1]
        b += [NAME[B1] for i, (x, y) in enumerate(SIDE_BITS) if x == c and y == 5 and r["right_side_mask"] >> i & 1]
        m["c%d" % c] = {"A": sorted(a), "B": sorted(b)}
    return m


M13 = [(i, r) for i, r in enumerate(RECORDS) if r["core_mask"] == 13]

records_out = []
failures = []
for idx, r in M13:
    L, R = r["left_side_mask"], r["right_side_mask"]
    La, Ra = attached_common(L), attached_common(R)
    cond_pairs = []
    for (x, y) in dist2_pairs(13):
        if (x in La and y in Ra) or (y in La and x in Ra):
            cond_pairs.append([x, y])
    ok = bool(cond_pairs)
    row = dict(
        record_index=idx,
        key=[r["core_mask"], L, R],
        p4_path_by_degree=["c%d" % v for v in p4_path(13)],
        dist2_common_pairs=[["c%d" % x, "c%d" % y] for (x, y) in dist2_pairs(13)],
        A_attached_common=sorted("c%d" % v for v in La),
        B_attached_common=sorted("c%d" % v for v in Ra),
        a0a1_private_edge=private_edge(L),
        b0b1_private_edge=private_edge(R),
        condition_holds=ok,
        witnessed_dist2_pairs=cond_pairs,
        attachment_matrix=att_matrix(r),
    )
    records_out.append(row)
    if not ok:
        failures.append(row)

# Distinct left/right support sets + private-edge flags among failures ---- #
fail_classes = Counter(
    (tuple(f["A_attached_common"]), tuple(f["B_attached_common"]),
     f["a0a1_private_edge"], f["b0b1_private_edge"])
    for f in failures)

smallest3 = sorted(failures, key=lambda f: f["record_index"])[:3]

summary = dict(
    note=("Bounded decode of the %d saved core_mask=13 (P4) records only. No new "
          "graphs, no finder/solver/census." % len(M13)),
    source=SOURCE.name,
    condition=("exists core-distance-2 common pair with one A-attached and one "
               "B-attached endpoint (reversal allowed)"),
    path_legend="core 13 = P4 c3-c0-c1-c2; order derived from degrees",
    num_records=len(M13),
    num_failures=len(failures),
    num_condition_holds=len(M13) - len(failures),
    distinct_failure_support_and_private=[
        dict(A_attached=list(a), B_attached=list(b), a0a1=pa, b0b1=pb, count=c)
        for (a, b, pa, pb), c in sorted(fail_classes.items(), key=lambda kv: (-kv[1], kv[0]))
    ],
    smallest_three_failures=smallest3,
)
(HERE / "p4_distance_two_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

lines = []
lines.append("Role B round3 E-request: %d saved core_mask=13 (P4) records. Catalogue only;" % len(M13))
lines.append("no new graphs/finder/solver. JSON: p4_distance_two_summary.json")
lines.append("")
lines.append("Core 13 is P4 c3-c0-c1-c2 (path order read from degrees). Distance-2 common")
lines.append("pairs = (c3,c1),(c0,c2). Condition = one A-attached + one B-attached endpoint,")
lines.append("reversal allowed (a signal for the known 5-triangle template).")
lines.append("")
lines.append("CONDITION HOLDS: %d / %d ; FAILURES: %d" %
             (len(M13) - len(failures), len(M13), len(failures)))
lines.append("")
lines.append("Distinct failure (A-support, B-support, a0a1, b0b1) classes and counts:")
for (a, b, pa, pb), c in sorted(fail_classes.items(), key=lambda kv: (-kv[1], kv[0])):
    lines.append("  A=%s B=%s a0a1=%s b0b1=%s  x%d" % (list(a), list(b), pa, pb, c))
lines.append("")
for f in smallest3:
    lines.append("failure #%d key=%s  A-sup=%s B-sup=%s a0a1=%s b0b1=%s" %
                 (f["record_index"], f["key"], f["A_attached_common"], f["B_attached_common"],
                  f["a0a1_private_edge"], f["b0b1_private_edge"]))
    lines.append("   attachment matrix:")
    for cv, av in sorted(f["attachment_matrix"].items()):
        lines.append("     %s -> A:%s B:%s" % (cv, av["A"], av["B"]))
    lines.append("")
(HERE / "p4_distance_two_summary.txt").write_text("\n".join(lines), encoding="utf-8")

print("core13 records:", len(M13), " condition holds:", len(M13) - len(failures),
      " failures:", len(failures))
print("failure classes:", len(fail_classes))
for k, v in sorted(fail_classes.items(), key=lambda kv: -kv[1]):
    print("  A=%s B=%s a0a1=%s b0b1=%s  x%d" % (k[0], k[1], k[2], k[3], v))
print("smallest-3 failure indices:", [f["record_index"] for f in smallest3])
print("Wrote", HERE / "p4_distance_two_summary.txt")
