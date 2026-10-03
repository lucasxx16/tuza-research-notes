#!/usr/bin/env python3
"""
B2 independent checker (PORTABLE, pure standard library -- no numpy, no scipy,
no .npy caches).  Needs ONLY the original ../D/finite_cover_incidence.json plus
the saved certificate files selected_cover.json and lower_bound.json.

It re-derives, with integer arithmetic alone, that the finite-dictionary set-cover
optimum equals the claimed value:

  LOWER BOUND (packing): a set P of k records with NO candidate covering two of
      them => every cover uses >= k candidates.  => OPT >= k.   (pure counting)
  UPPER BOUND (cover):   a set C of m candidates whose covered_records union is
      the full record set.  => OPT <= m.   (exact boolean union)
  CROSS-CHECK (dual):    exact rational record weights w_j >= 0 with every
      candidate weight-sum <= 1 and total W => OPT >= ceil(W).

Verdict OPT == m == k is a self-contained proof over the supplied candidates;
explicitly NOT a claim over all conceivable templates.

Malformed input / certificates are HARD FAILURES (exit 1), never silently skipped.
Run:  python independent_check.py
"""

import json, os, sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
INC = os.path.normpath(os.path.join(HERE, "..", "D", "finite_cover_incidence.json"))

fails = []


def check(name, cond, detail=""):
    print(("[PASS] " if cond else "[FAIL] ") + name + ((" -- " + detail) if detail else ""))
    if not cond:
        fails.append(name)


def die(msg):
    print("[FAIL] " + msg)
    print("CHECK FAILURES (fatal):", [msg])
    sys.exit(1)


def load_json(path, label):
    if not os.path.exists(path):
        die(f"missing {label}: {path}")
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        die(f"unparseable {label} ({type(e).__name__}): {e}")


def to_int(x, label):
    try:
        return int(x)
    except Exception:
        die(f"{label} is not an integer: {x!r}")


def ceil_frac(fr):
    return -((-fr.numerator) // fr.denominator)


# ------------------------------------------------------------------ load raw input
inc = load_json(INC, "incidence JSON")
for key in ("record_count", "candidate_count", "record_keys", "candidates"):
    if key not in inc:
        die(f"incidence JSON missing required key {key!r}")
NREC = to_int(inc["record_count"], "record_count")
NCAND = to_int(inc["candidate_count"], "candidate_count")

# record_keys: correct count AND unique
rkeys = inc["record_keys"]
check("input: record_keys length == record_count", len(rkeys) == NREC, f"{len(rkeys)} vs {NREC}")
rkey_t = [tuple(to_int(v, "record_key elem") if isinstance(v, int) else v for v in rk)
          if isinstance(rk, (list, tuple)) else rk for rk in rkeys]
check("input: record_keys all unique", len(set(rkey_t)) == NREC, f"{len(set(rkey_t))} unique")

# candidates: ids unique + exactly contiguous 0..NCAND-1
raw_ids = [to_int(c["id"], "candidate id") for c in inc["candidates"]]
check("input: len(candidates) == candidate_count", len(inc["candidates"]) == NCAND,
      f"{len(inc['candidates'])} vs {NCAND}")
check("input: candidate ids unique", len(set(raw_ids)) == NCAND, f"{len(set(raw_ids))} unique")
check("input: candidate ids == contiguous 0..NCAND-1",
      sorted(raw_ids) == list(range(NCAND)), f"min={min(raw_ids)} max={max(raw_ids)}")

# covered_sets keyed by id, indices in range
covered = {}
bad_idx = 0
for c in inc["candidates"]:
    i = to_int(c["id"], "candidate id")
    cr = [to_int(x, "covered_record idx") for x in c["covered_records"]]
    bad_idx += sum(1 for x in cr if not (0 <= x < NREC))
    covered[i] = set(cr)
check("input: all covered_record indices in [0,NREC)", bad_idx == 0, f"{bad_idx} out of range")

# instance feasibility
union_all = set()
for s in covered.values():
    union_all |= s
check("input: instance coverable (every record in some candidate)",
      len(union_all) == NREC, f"{len(union_all)}/{NREC}")

# ------------------------------------------------------------------ cover certificate
sc = load_json(os.path.join(HERE, "selected_cover.json"), "selected_cover.json")
for key in ("selected_candidate_ids", "cover_size"):
    if key not in sc:
        die(f"selected_cover.json missing required key {key!r}")
cover = [to_int(x, "selected id") for x in sc["selected_candidate_ids"]]
claimed = to_int(sc["cover_size"], "cover_size")
check("cover: selected candidate ids distinct", len(cover) == len(set(cover)),
      f"{len(cover)} listed, {len(set(cover))} unique")
check("cover: size matches selected list", len(cover) == claimed, f"{len(cover)} vs {claimed}")
check("cover: ids are valid candidate ids", all(0 <= i < NCAND for i in cover))
union = set()
for i in cover:
    union |= covered[i]
check("cover: union covers all records", len(union) == NREC, f"{len(union)}/{NREC}")
m = len(set(cover))
print(f"     => UPPER BOUND  OPT <= {m}")

# ------------------------------------------------------------------ packing certificate
lb = load_json(os.path.join(HERE, "lower_bound.json"), "lower_bound.json")
for key in ("packing_size", "packing_record_indices"):
    if key not in lb:
        die(f"lower_bound.json missing required key {key!r}")
P = [to_int(x, "packing idx") for x in lb["packing_record_indices"]]
Ps = set(P)
check("packing: indices distinct", len(P) == len(Ps), f"{len(P)} listed, {len(Ps)} unique")
check("packing: claimed size matches", len(Ps) == to_int(lb["packing_size"], "packing_size"),
      f"{len(Ps)} vs {lb['packing_size']}")
check("packing: indices in [0,NREC)", all(0 <= j < NREC for j in P))

# packing_record_keys must equal record_keys[idx] for each index (recoverability link)
if "packing_record_keys" in lb:
    prk = lb["packing_record_keys"]
    keymatch = (len(prk) == len(P) and
                all(tuple(prk[t]) == tuple(rkeys[P[t]]) for t in range(len(P))))
    check("packing: packing_record_keys match record_keys[indices]", keymatch)
else:
    check("packing: packing_record_keys present", False, "field absent")

# the core combinatorial lower bound: no candidate covers two packing records
worst = 0
for i in range(NCAND):
    hit = len(covered[i] & Ps)
    if hit > worst:
        worst = hit
check("packing: NO candidate covers two packing records (all candidates)",
      worst <= 1, f"max records-of-P per candidate = {worst}")
k = len(Ps)
print(f"     => LOWER BOUND  OPT >= {k}  (pure counting)")

# ------------------------------------------------------------------ exact rational dual (REQUIRED, fail if malformed)
if "exact_rational_dual" not in lb:
    die("lower_bound.json missing required key 'exact_rational_dual'")
rd = lb["exact_rational_dual"]
if "weights_over_records" not in rd:
    die("exact_rational_dual missing 'weights_over_records'")
wts = {}
for a, b in rd["weights_over_records"].items():
    j = to_int(a, "dual record index")
    try:
        v = Fraction(str(b))
    except Exception:
        die(f"dual weight for record {j} is not a rational: {b!r}")
    if not (0 <= j < NREC):
        die(f"dual index {j} out of range [0,{NREC})")
    if v < 0:
        die(f"dual weight for record {j} is negative: {v}")
    wts[j] = v
tot = sum(wts.values(), Fraction(0))
maxsum = max((sum((wts.get(j, Fraction(0)) for j in covered[i]), Fraction(0))
              for i in range(NCAND)), default=Fraction(0))
check("dual: all weights >= 0 and indices valid", len(wts) == len(rd["weights_over_records"]))
check("dual: every candidate weight-sum <= 1 (exact rationals)", maxsum <= 1, f"max={maxsum}")
check("dual: total weight == claimed",
      tot == Fraction(str(rd.get("total_weight", "0"))), f"total={tot}")
dual_lb = ceil_frac(tot)
check("dual: implied ceil(total) matches claimed",
      dual_lb == to_int(rd.get("implied_lb_ceil_total", -1), "implied_lb"),
      f"ceil({tot})={dual_lb}")
check("dual: support set == packing set (two LB certificates agree)",
      set(j for j, v in wts.items() if v > 0) == Ps,
      f"|support|={len([1 for v in wts.values() if v>0])} |P|={k}")
print(f"     => rational-dual LOWER BOUND  OPT >= ceil({tot}) = {dual_lb}")

# ------------------------------------------------------------------ verdict
print("-" * 56)
if fails:
    print("CHECK FAILURES:", fails)
    sys.exit(1)
if m == k == dual_lb:
    print(f"CERTIFIED finite-dictionary min set cover = {m}  (cover {m} == packing {k} "
          f"== dual {dual_lb}); gap 0.")
    sys.exit(0)
elif m >= k:
    print(f"BOUNDS OK but not closed: OPT in [{k},{m}], gap {m - k}.")
    sys.exit(0)
else:
    print(f"INCONSISTENT: cover UB {m} < packing LB {k}.")
    sys.exit(1)
