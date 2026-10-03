"""Role B, round 3 -- final bounded validation of D/k4_human_proof.txt.

Implements the proof's TWO explicit six-triangle recipes (G generic and E
exceptional d-switch) on ONLY the 21 saved core_mask=63 (K4) records.

* Reconstructs the binary maps alpha:C->A and beta:C->B from the saved side
  masks (uniqueness was verified separately; re-checked here).
* Chooses a valid labelling by BOUNDED RECIPE INSTANTIATION over the fixed set
  of 24 core permutations x (2 A-names x 2 B-names) private choices -- the SAME
  graph, only renamed.  No new graph, no certificate finder, no solver, no census.
* Rebuilds S (6 triangles), R (7 external edges) and X=R u {5 hub edges} (12 edges).
* Independently checks the three local reduction conditions (as in
  verification/check_saved_orbits.py): every cover edge present; packing triangles
  present AND edge-disjoint; |X|<=2|S|; every hub triangle met by X; every
  packing edge avoiding {u,v} lies in X.  Also asserts all recipe edges present.

Pure standard library; portable (relative) paths.
"""

import json
import sys
from itertools import combinations, permutations
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "input" / "B_codegree4_certificates.json"

DOC = json.loads(SOURCE.read_text(encoding="utf-8"))
RECORDS = DOC["records"]
SIDE_BITS = [tuple(x) for x in DOC["side_bit_order"]]
CORE_BITS = [tuple(x) for x in DOC["core_bit_order"]]
LBL = DOC["vertex_labels"]
U, V = LBL["u"], LBL["v"]
C = list(LBL["common"])            # c0..c3 -> 2,3,4,5
A = list(LBL["left_exclusive"])    # 6,7
B = list(LBL["right_exclusive"])   # 8,9
VERTICES = [U, V] + C + A + B
NAME = {U: "u", V: "v"}
for i, x in enumerate(C):
    NAME[x] = "c%d" % i
for i, x in enumerate(A):
    NAME["A%d" % i] = NAME[x] = "a%d" % i
for i, x in enumerate(B):
    NAME["B%d" % i] = NAME[x] = "b%d" % i


def e(x, y):
    return tuple(sorted((x, y)))


def edges_of(r):
    """Local graph edge set of a saved record (all core edges since mask=63)."""
    E = {e(U, V)}
    E |= {e(U, x) for x in C + A}
    E |= {e(V, x) for x in C + B}
    for x, y in CORE_BITS:
        E.add(e(C[x], C[y]))                       # core_mask 63 => all present
    for field, side in (("left_side_mask", A), ("right_side_mask", B)):
        m = r[field]
        for i, (x, y) in enumerate(SIDE_BITS):
            if m >> i & 1:
                E.add(e(C[x], side[y - 4]) if x < 4 else e(*side))
    return E


def tri_edges(t):
    return {e(x, y) for x, y in combinations(t, 2)}


def all_triangles(E):
    return [set(t) for t in combinations(VERTICES, 3) if tri_edges(t) <= E]


def build_maps(r):
    """alpha[cidx]=A-vertex, beta[cidx]=B-vertex; assert uniqueness; priv flags."""
    def decode(m, side):
        nbr, bad = {}, []
        for i, (x, y) in enumerate(SIDE_BITS):
            if m >> i & 1 and x < 4:
                nbr.setdefault(x, []).append(side[y - 4])
        for c in range(4):
            got = nbr.get(c, [])
            if len(got) != 1:
                bad.append(c)
            nbr[c] = got
        priv = any(m >> i & 1 for i, (x, y) in enumerate(SIDE_BITS) if x >= 4)
        return nbr, bad, priv
    an, abad, aa = decode(r["left_side_mask"], A)
    bn, bbad, bb = decode(r["right_side_mask"], B)
    # guard empty/malformed neighbour lists so uniqueness can be reported, not crash
    alpha = {c: (an[c][0] if len(an.get(c, [])) == 1 else None) for c in range(4)}
    beta = {c: (bn[c][0] if len(bn.get(c, [])) == 1 else None) for c in range(4)}
    unique_ok = not abad and not bbad
    return alpha, beta, aa, bb, unique_ok


# --------------------------------------------------------------------------- #
# recipes
# --------------------------------------------------------------------------- #
def recipe_G(alpha, beta):
    """Return first valid (x,y,z,w,a-,b+,..., S, R, X) or None. Bounded 24x4 search."""
    for (xi, yi, zi, wi) in permutations(range(4)):
        for am in A:
            ap = next(v for v in A if v != am)
            if not set(i for i in range(4) if alpha[i] == am) <= {wi, zi}:
                continue
            for bm in B:
                bp = next(v for v in B if v != bm)
                if not set(i for i in range(4) if beta[i] == bm) <= {wi, yi}:
                    continue
                X_, Y_, Z_, W_ = C[xi], C[yi], C[zi], C[wi]
                az, by = alpha[zi], beta[yi]
                S = [{X_, Y_, Z_}, {U, V, X_}, {U, Y_, W_},
                     {V, Z_, W_}, {U, Z_, az}, {V, Y_, by}]
                R = {e(X_, Y_), e(X_, Z_), e(Y_, Z_), e(Y_, W_),
                     e(Z_, W_), e(Z_, az), e(Y_, by)}
                Xc = R | {e(U, V), e(U, W_), e(V, W_), e(U, ap), e(V, bp)}
                lab = dict(x=NAME[X_], y=NAME[Y_], z=NAME[Z_], w=NAME[W_],
                           a_minus=NAME[am], a_plus=NAME[ap],
                           b_minus=NAME[bm], b_plus=NAME[bp])
                return lab, S, R, Xc
    return None


def recipe_E(alpha, beta, aa):
    """(E): balanced alpha/beta with identical partitions. 24-perm instantiation."""
    pa = {frozenset(i for i in range(4) if alpha[i] == v) for v in A}
    pb = {frozenset(i for i in range(4) if beta[i] == v) for v in B}
    if not all(len(b) == 2 for b in pa) or not all(len(b) == 2 for b in pb):
        return None
    if pa != pb:
        return None
    for (xi, yi, zi, wi) in permutations(range(4)):
        # block1={x,y} must be a joint fiber, block2={z,w} the other
        if frozenset((xi, yi)) not in pa or frozenset((zi, wi)) not in pa:
            continue
        if alpha[xi] != alpha[yi] or alpha[zi] != alpha[wi] or alpha[xi] == alpha[zi]:
            continue
        if beta[xi] != beta[yi] or beta[zi] != beta[wi] or beta[xi] == beta[zi]:
            continue
        a, a2 = alpha[xi], alpha[zi]
        b, b2 = beta[xi], beta[zi]
        X_, Y_, Z_, W_ = C[xi], C[yi], C[zi], C[wi]
        d = a if aa else W_            # d-switch: d=a if aa' (a0a1) present else w
        S = [{a, X_, Y_}, {U, V, X_}, {U, Y_, Z_},
             {U, a2, d}, {V, Y_, b}, {V, Z_, W_}]
        R = {e(a, X_), e(a, Y_), e(X_, Y_), e(Y_, Z_),
             e(a2, d), e(Y_, b), e(Z_, W_)}
        Xc = R | {e(U, Z_), e(U, W_), e(V, X_), e(V, Y_), e(V, b2)}
        lab = dict(x=NAME[X_], y=NAME[Y_], z=NAME[Z_], w=NAME[W_],
                   a=NAME[a], a_prime=NAME[a2], b=NAME[b], b_prime=NAME[b2],
                   d=NAME[d], d_switch=("a (aa' present)" if aa else "w (aa' absent)"))
        return lab, S, R, Xc
    return None


def audit(S, Xc, E):
    """Three local reduction conditions + all-specified-edges-present."""
    res = {}
    res["packing_size6"] = len(S) == 6
    res["cover_size12"] = len(Xc) == 12 and all(len(frozenset(t)) == 3 for t in S)
    res["cover_subset_edges"] = Xc <= E
    used, all_present, disjoint = set(), True, True
    for t in S:
        te = tri_edges(t)
        all_present &= te <= E
        if te & used:
            disjoint = False
        used |= te
    res["triangles_present"] = all_present
    res["triangles_edge_disjoint"] = disjoint
    res["size_bound_le_2S"] = len(Xc) <= 2 * len(S)
    hub_tris = [t for t in all_triangles(E) if U in t or V in t]
    res["all_hub_triangles_met"] = all(tri_edges(t) & Xc for t in hub_tris)
    res["num_hub_triangles_checked"] = len(hub_tris)
    ext_pack_edges = {ed for t in S for ed in tri_edges(t) if U not in ed and V not in ed}
    res["ext_packing_edges_in_cover"] = ext_pack_edges <= Xc
    res["recipe_edges_all_present"] = all(ed in E for ed in Xc)
    res["PASS"] = all(v for k, v in res.items() if k != "num_hub_triangles_checked")
    return res


# --------------------------------------------------------------------------- #
def main():
    K4 = [(i, r) for i, r in enumerate(RECORDS) if r["core_mask"] == 63]
    out, problems = [], []
    for idx, r in K4:
        E = edges_of(r)
        alpha, beta, aa, bb, uniq = build_maps(r)
        rec = dict(record_index=idx, key=[r["core_mask"], r["left_side_mask"], r["right_side_mask"]],
                   alpha=({("c%d" % k): NAME[v] for k, v in alpha.items()} if uniq else None),
                   beta=({("c%d" % k): NAME[v] for k, v in beta.items()} if uniq else None),
                   a0a1=aa, b0b1=bb, unique_alpha_beta=uniq)
        if not uniq:
            problems.append((idx, "non-unique attachment map"))
            out.append(rec | {"construction": "SKIP"})
            continue
        got = recipe_E(alpha, beta, aa)
        kind = "E"
        if got is None:
            got = recipe_G(alpha, beta)
            kind = "G"
        if got is None:
            problems.append((idx, "no valid labelling for either recipe"))
            out.append(rec | {"construction": "NO_RECIPE"})
            continue
        lab, S, R, Xc = got
        res = audit(S, Xc, E)
        rec |= dict(construction=kind, labelling=lab,
                    packing=[sorted(t) for t in S],
                    cover_edges=[sorted(ed) for ed in sorted(Xc)],
                    triangles=[sorted(NAME[x] for x in t) for t in S],
                    cover=sorted("".join(NAME[x] for x in ed) for ed in Xc),
                    cover_size=len(Xc), audit=res)
        if not res["PASS"]:
            problems.append((idx, "audit fail", {k: v for k, v in res.items() if not v}))
        out.append(rec)

    distinct_keys = sorted({(r["core_mask"], r["left_side_mask"], r["right_side_mask"])
                            for _, r in K4})
    if len(K4) != 21:
        problems.append(("record-count", "expected exactly 21 K4 records", len(K4)))
    if len(distinct_keys) != len(K4):
        problems.append(("distinct-keys", "duplicate record keys", len(K4) - len(distinct_keys)))

    summary = dict(
        note=("Bounded validation of the two D/k4_human_proof recipes (G,E) on the 21 "
              "saved core_mask=63 records. Recipe instantiation over 24 core perms x "
              "2x2 private-name choices only; no new graph, no finder/solver/census."),
        source=SOURCE.name,
        num_k4=len(K4),
        num_distinct_record_keys=len(distinct_keys),
        exactly_21_distinct_keys=(len(K4) == 21 and len(distinct_keys) == 21),
        constructions={"G": sum(1 for o in out if o.get("construction") == "G"),
                       "E": sum(1 for o in out if o.get("construction") == "E")},
        all_unique_maps=all(o.get("unique_alpha_beta") for o in out),
        all_pass=all(o.get("audit", {}).get("PASS") for o in out),
        problems=problems,
        witnesses=out,
    )
    (HERE / "k4_recipe_check.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    lines = ["Role B round3 -- bounded validation of D/k4_human_proof recipes on 21 saved K4 records.",
             "No new graph, no finder/solver/census. JSON: k4_recipe_check.json", "",
             "exactly 21 distinct K4 record keys: %s (records=%d distinct=%d)" %
             (summary["exactly_21_distinct_keys"], summary["num_k4"], summary["num_distinct_record_keys"]),
             "unique alpha/beta maps on all records: %s" % summary["all_unique_maps"],
             "construction usage: G=%d  E=%d" % (summary["constructions"]["G"], summary["constructions"]["E"]),
             "E-recipe d-switch: aa' present->d=a=%d ; aa' absent->d=w=%d" % (
                 sum(1 for o in out if o.get("construction") == "E" and o["labelling"]["d_switch"].startswith("a")),
                 sum(1 for o in out if o.get("construction") == "E" and o["labelling"]["d_switch"].startswith("w"))),
             "ALL 21 recipes PASS the three local reduction conditions: %s" % summary["all_pass"],
             "problems: %s" % (problems if problems else "none"), ""]
    lines.append("per-record: idx key recipe |S| |X| hubtris_checked PASS")
    for o in out:
        a = o.get("audit", {})
        lines.append("  %4d %s %s %s %s %s %s" % (
            o["record_index"], o["key"], o.get("construction"),
            6 if a.get("packing_size6") else "?", o.get("cover_size", "?"),
            a.get("num_hub_triangles_checked", "?"), a.get("PASS", "SKIP")))
    (HERE / "k4_validation_report.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print("K4 records:", len(K4), " distinct keys:", len(distinct_keys),
          " G:", summary["constructions"]["G"], " E:", summary["constructions"]["E"])
    print("all unique maps:", summary["all_unique_maps"], " all audit PASS:", summary["all_pass"])
    print("problems:", problems if problems else "none")
    print("Wrote", HERE / "k4_recipe_check.json", "and", HERE / "k4_validation_report.txt")

    ok = (summary["exactly_21_distinct_keys"] and summary["all_unique_maps"]
          and summary["all_pass"] and not problems)
    print("OVERALL:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
