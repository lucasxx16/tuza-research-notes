"""Round10 / Role B: exact-input LP experiment on the 7-variable normalized domain.

Maximize z subject to
    a+m<=1, d<=c<=b<=m, h<=c, all vars >=0,
    plus the four Wang upper bounds on z.
Sensitivity: hypothetical extra row d+h >= eta*c (NOT a graph-theoretic fact).
Numerical evidence only; nothing here is a proof. Run:  python lp_experiment.py
"""
from fractions import Fraction as F
import json, time
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
VARS = ["a", "b", "c", "d", "h", "m", "z"]
IDX = {v: i for i, v in enumerate(VARS)}
N = len(VARS)
EPS = 1e-9


def mk(name, coeffs, rhs):
    row = [0.0] * N
    for k, v in coeffs.items():
        row[IDX[k]] = float(v)
    return {"name": name, "row": row, "rhs": float(rhs),
            "exact": {k: str(v) for k, v in coeffs.items()}, "exact_rhs": str(rhs)}


BASE = [
    mk("a+m<=1", {"a": F(1), "m": F(1)}, F(1)),
    mk("d<=c", {"c": F(-1), "d": F(1)}, F(0)),
    mk("c<=b", {"b": F(-1), "c": F(1)}, F(0)),
    mk("b<=m", {"b": F(1), "m": F(-1)}, F(0)),
    mk("h<=c", {"c": F(-1), "h": F(1)}, F(0)),
    mk("W1 z<=3-a", {"a": F(1), "z": F(1)}, F(3)),
    mk("W2 z<=3/2+5a/2+3b/2-c+3h/8",
       {"a": F(-5, 2), "b": F(-3, 2), "c": F(1), "h": F(-3, 8), "z": F(1)}, F(3, 2)),
    mk("W3 z<=3-c-d", {"c": F(1), "d": F(1), "z": F(1)}, F(3)),
    mk("W4 z<=3-b+9c/4+3d/2-h/4",
       {"b": F(1), "c": F(-9, 4), "d": F(-3, 2), "h": F(1, 4), "z": F(1)}, F(3)),
]


def marg(res, attr):
    node = getattr(res, attr, None)
    m = getattr(node, "marginals", None)
    if m is None:
        return []
    return [float(v) for v in (m if hasattr(m, "__iter__") else [m])]


def solve(extra=None):
    rows = BASE + list(extra or [])
    res = linprog(c=[0.0] * (N - 1) + [-1.0],
                  A_ub=[r["row"] for r in rows], b_ub=[r["rhs"] for r in rows],
                  bounds=[(0.0, None)] * N, method="highs",
                  options={"time_limit": 30.0, "presolve": True, "dual_feasibility_tolerance": 1e-10})
    duals = marg(res, "ineqlin")
    x = list(res.x) if res.x is not None else [None] * N
    out = {"status": int(res.status), "success": bool(res.success),
           "message": str(res.message), "z": (-res.fun if res.success else None),
           "wall_s": None, "point": {v: x[i] for i, v in enumerate(VARS)},
           "point_rational": {v: (F(x[i]).limit_denominator(10 ** 6) if x[i] is not None else None)
                              for i, v in enumerate(VARS)},
           "rows": []}
    for i, r in enumerate(rows):
        s = (None if res.x is None else r["rhs"] - sum(r["row"][j] * x[j] for j in range(N)))
        out["rows"].append({"name": r["name"], "exact": r["exact"], "rhs": r["exact_rhs"],
                            "slack": s, "active": (s is not None and abs(s) <= 1e-7),
                            "dual": (duals[i] if i < len(duals) else None)})
    out["lower_duals"] = {v: marg(res, "lower")[i] for i, v in enumerate(VARS)} if marg(res, "lower") else {}
    out["z_rational"] = (F(out["z"]).limit_denominator(10 ** 6) if out["z"] is not None else None)
    return out


def main():
    t0 = time.time()
    cases = {"baseline_165_59_domain": {}}
    for eta in [F(1, 20), F(1, 10), F(1, 4), F(1, 2), F(1)]:
        cases[f"hyp_d+h>=eta*c[eta={eta}]"] = [mk(f"S d+h>={eta}*c",
                                                  {"c": eta, "d": F(-1), "h": F(-1)}, F(0))]
    runs = {}
    for name, extra in cases.items():
        s = time.time()
        r = solve(extra)
        r["wall_s"] = round(time.time() - s, 4)
        runs[name] = r

    # Implementation validation (known values, not derived here).
    pt = {v: F(0) for v in VARS}
    pt.update(a=F(12, 59), b=F(39, 59), c=F(12, 59), d=F(0), h=F(0), m=F(39, 59), z=F(165, 59))
    checks = {}
    for r in BASE:
        lhs = sum(F(r["exact"][v]) * pt[v] for v in r["exact"])
        checks[r["name"]] = {"lhs": str(lhs), "rhs": r["exact_rhs"], "tight": lhs == F(r["exact_rhs"])}
    known = {"point": {k: str(v) for k, v in pt.items()}, "row_checks": checks,
             "all_rows_feasible": all(F(c["lhs"]) <= F(c["rhs"]) for c in checks.values()),
             "tight_count": sum(1 for c in checks.values() if c["tight"])}
    known["feasible_under_extra"] = {k: (pt["d"] + pt["h"] >= eta * pt["c"])
                                     for k, eta in [("1/20", F(1, 20)), ("1/10", F(1, 10)),
                                                    ("1/4", F(1, 4)), ("1/2", F(1, 2)), ("1", F(1))]}
    payload = {"kind": "LP relaxation, maximize z (scipy HiGHS, time_limit 30s)",
               "disclaimer": "Numerical/computational evidence only. No proof. The extra "
                             "d+h>=eta*c row is a hypothetical, not a graph-theoretic fact.",
               "vars": VARS, "runs": runs, "known_point_validation": known,
               "total_wall_s": round(time.time() - t0, 3)}
    (HERE / "results.json").write_text(json.dumps(payload, indent=1, default=str), encoding="utf-8")
    write_report(payload)
    for k, r in runs.items():
        print(f"{k:34s} z={r['z']} status={r['status']} actives="
              f"{[x['name'] for x in r['rows'] if x['active']]}")
    print("written:", HERE / "results.json")


def write_report(p):
    L = ["# Round10 / Role B - exact-input LP (maximize z) on the 7-var domain",
         "",
         "Domain: `a+m<=1`, `d<=c<=b<=m`, `h<=c`, all of `a,b,c,d,h,m,z >= 0`; objective max z.",
         "Wang rows W1..W4 as given. Solver status alone is not a proof; the exact",
         "face below certifies only this LP relaxation. The `d+h>=eta*c` rows are",
         "hypothetical and have no graph-theoretic justification here.",
         "",
         "| case | z* (LP) | nearest rational | a,b,c,d,h,m,z at argmax | active rows |",
         "|---|---|---|---|---|"]
    for k, r in p["runs"].items():
        if not r["success"]:
            L.append(f"| {k} | status {r['status']} | - | - | - |")
            continue
        pt = r["point_rational"]
        L.append("| {} | {:.10f} | {} | {} | {} |".format(
            k, r["z"], r["z_rational"],
            ",".join(str(pt[v]) for v in p["vars"]),
            "; ".join(x["name"] for x in r["rows"] if x["active"])))
    kn = p["known_point_validation"]
    L += ["", "## Implementation validation (known inputs, re-derived rows only)",
          f"- point `{kn['point']}`: feasible={kn['all_rows_feasible']}, tight rows={kn['tight_count']}/9,",
          f"  z=165/59={165/59:.10f} matches baseline LP optimum: "
          f"{abs(p['runs']['baseline_165_59_domain']['z'] - 165/59) < 1e-9}",
          f"- known point satisfies extra row `d+h>=eta*c`: {kn['feasible_under_extra']}",
          "", "## Active-row duals (for Role C exact-certificate work)",
          "- see `results.json` -> runs[*].rows[*].dual (HiGHS marginals) and lower_duals,"]
    for k, r in p["runs"].items():
        if r["success"]:
            L.append(f"  - {k}: " + ", ".join(f"{x['name']}={x['dual']}" for x in r["rows"]
                                              if x["dual"] is not None and abs(x["dual"]) > 1e-12))
    L += ["", "## Quantitative targets handed to mainline",
          f"- Baseline LP optimum over the stated domain: z* = {p['runs']['baseline_165_59_domain']['z_rational']}"
          f" ({p['runs']['baseline_165_59_domain']['z']:.10f}); wall {p['total_wall_s']}s for 6 solves.",
          "- Under each hypothetical eta floor, the LP gap versus 165/59 (see table) is the only",
          "  thing this round measures: eta-sensitivity of the relaxation, not of the graph problem.",
          "- Scope note: no graph enumeration performed; no new source read; no graph theorem claimed.",
          "", "## Exact rational face and upper certificate",
          "- The nonnegative weights (20,8,19,12)/59 on W1..W4 give",
          "  z+d/59<=165/59, so z<=165/59 since d>=0.",
          "- For every 0<=eta<=1, take a=c=12/59, d=0, h=eta*c,",
          "  b=39/59-h/4, m=47/59, z=165/59. This point satisfies the",
          "  domain and d+h>=eta*c, and ALL four Wang rows are equalities.",
          "  This feasible equality face, together with the upper certificate,",
          "  proves the LP optimum remains 165/59. An upper cap alone would",
          "  not prove that the optimum cannot be lower.",
          "- The displayed points are abstract LP parameters, not claimed",
          "  realizable by any graph. The extra eta row is hypothetical."]
    (HERE / "report.txt").write_text("\n".join(L) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
