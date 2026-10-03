"""Read-only audit of the single bounded Round11/B diagnostic output.

Checks aggregate bookkeeping and re-solves three saved examples, not the full search.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "B"))
from verify_witness import verify

data = json.loads((ROOT / "B" / "instances.json").read_text(encoding="utf-8"))
st = data["stats"]
assert st["attempts"] == st["unique"] + st["repeats"] == 6029
assert st["eligible"] == sum(x["eligible"] for x in st["per_n"].values()) == 994
assert all(x["eligible"] == x["quota"] == 142 for x in st["per_n"].values())
assert sum(st["hist_s"].values()) == sum(st["hist_tau_over_p"].values()) == 994
assert sum(st["hist_max_red_pages"].values()) == 994
assert st["hist_s"]["True"] == sum(v for k, v in st["hist_max_red_pages"].items() if int(k) > 1) == 263
assert not st["disagreements"] and not st["witness_alarm"]

chosen = [data["best_by_stratum"]["s0"][0],
          data["best_by_stratum"]["sp"][0],
          next(r for r in data["retained"]["s_positive"] if r["p"] == 3)]
out = []
for rec in chosen:
    fresh = verify(rec["n"], rec["colorstring"],
                   {k: rec[k] for k in ("p", "p_private", "tau", "r", "s")})
    assert fresh["verified"] and fresh["certified"] and fresh["eligible"]
    assert all(fresh[k] == rec[k] for k in ("p", "p_private", "tau", "r", "s"))
    assert fresh["nonprivate_red_edges"] == [[e[:2], e[2]]
                                                  for e in rec["nonprivate_red_page_counts"]]
    out.append({k: rec[k] for k in ("name", "n", "p", "p_private", "tau", "r", "s")})
print({"attempts": st["attempts"], "unique": st["unique"],
       "eligible": st["eligible"], "s_positive": st["hist_s"]["True"],
       "max_ratio_s_positive": max(r["tau_over_p"] for r in data["retained"]["s_positive"]),
       "rechecked": out})
