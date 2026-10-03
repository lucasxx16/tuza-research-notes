# Tuza research: equality graphs and certificate compression

Private research record, started 2026-10-03 (Asia/Shanghai).

Round 1 selected question: does a finite simple connected 7-regular graph with
positive triangle packing number satisfy tau(G) = 2 nu(G)? This is the
existence subquestion of Question 12.3 in Anish Gupta,
Tuza's conjecture for graphs of maximum degree at most seven,
https://arxiv.org/html/2608.06538v1.

Source repository: https://github.com/agupta/tuza-maximum-degree-seven
Source commit inspected: bf8415fac44f4eeed6c0f7a2273b843d689b065e.
The upstream codegree census and certificate search are not being rerun.

Roles: A (Westlake HPC), literature and scope; B (Westlake HPC), exact
computations only; C (GPT-6 Sol), adversarial review; D (GPT-6 Astra xhigh),
independent first draft; E (GPT-6 Astra xhigh), main mathematical research.
The parent coordinates, reviews evidence, and records mathematical status.

## Round 2: 1,144 certificates compressed into nine templates

**Nine templates cover all 1,144 supplied codegree-four records, and nine is
optimal within the declared dictionary of 499 catalogue-derived signed-pattern
orbits.** This is not a global minimum over arbitrary structural templates.

Each template has required-present and required-absent rim edges, together with
a fixed triangle packing and deletion recipe. A universal transfer lemma proves
that every graph satisfying the pattern has a reducible hub pair. The 499
candidates are obtained from the original saved witnesses, with symmetry group
of order 192. No original local-graph census or certificate finder was rerun.

The upper bound is an explicit nine-template cover. The lower bound consists of
nine records such that every candidate covers at most one. C independently rebuilt
all 499 patterns and incidence lists from the raw input, checked both bounds,
and checked 1,144 transferred witnesses. The proof of optimality uses integer
counting, not a numerical solver's status.

A separate human proof settles the entire **2K2 core subcase** under connected,
non-WKE link hypotheses. It needs neither the catalogue nor the degree budget.
The other core types still lack a complete human argument forcing the templates.

- [Accepted results and scope in Chinese](results/round2_accepted.txt)
- [The nine literal templates and their interpretations](research/round2/D/optimal_patterns.txt)
- [Universal signed-template proof](research/round2/D/proof.txt)
- [Nine templates with record assignments](research/round2/D/optimal_templates.json)
- [All 1,144 transferred witnesses](research/round2/D/optimal_transformed_certificates.json)
- [Exact nine-record lower bound](research/round2/B2/lower_bound.json)
- [Census-free 2K2 proof](research/round2/E/human_case_2k2.txt)
- [Matching/cover normal form and exchange lemmas](research/round2/E/proof.txt)
- [Independent adversarial review](research/round2/C/review.txt)
- [Parent acceptance and correction record](research/round2/acceptance_review.txt)
- [Input provenance and attribution](research/round2/shared/PROVENANCE.txt)

From the repository root, the main independent check needs only standard Python:

```powershell
python research/round2/C/check_B2_optimum.py
python research/round2/B2/independent_check.py
python research/round2/C/check_optimal_export.py
```

The first command reconstructs the dictionary and all incidence lists from the
raw saved certificates, then verifies the exact optimum and transferred witnesses.
The second checks the upper/lower certificates against the saved incidence matrix.
The third repeats the main audit and checks the final exported files against it.
None invokes a solver. Do not run these assertion-based checks with `python -O`.
The original greedy eleven-template stage is retained as research history; its
statistics must not be substituted for those of the final nine. The final assignment
uses five, six, or seven triangles (888, 254, and 2 records, respectively), at most
one hub-free triangle, and no triangle wholly inside the four-vertex core.

## Round 1 accepted result

The selected existence question has an affirmative answer:

$$G=K_4\square K_5,\qquad |V(G)|=20,\quad d(v)=7,\quad
\nu(G)=13,\quad\tau(G)=26=2\nu(G).$$

The vertices are the cells of a 4 by 5 grid, adjacent when in the same row
or column. Every triangle belongs to a single row or column. The four K5
rows and five K4 columns have disjoint edge sets, so their packing and
covering optima add: nu=4(2)+5(1)=13 and tau=4(4)+5(2)=26.
The graph is connected, and every edge belongs to a triangle.

- [Full accepted proof in Chinese](results/accepted_result.txt)
- [Independent first proof by D](research/round1/D/proof.txt)
- [Explicit graph, packing, and cover](research/round1/D/certificates.json)
- [Adversarial review by C](research/round1/C/review.txt)
- [General Cartesian additivity and second proof](research/round1/E/addendum.txt)
- [Independent exact computation by B](research/round1/B/result_20.json)
- [Parent acceptance and correction record](research/round1/acceptance_review.txt)

An additional accepted family is K4 square H for any connected triangle-free
4-regular graph H. It has nu=|V(H)| and tau=2|V(H)|. The original
[E proof](research/round1/E/proof.txt) gives an explicit unbounded family.

For arbitrary finite simple factors, both invariants satisfy Cartesian
additivity: f(F square H)=|V(H)|f(F)+|V(F)|f(H), for f=nu,tau.

## Verification

The proof is elementary and independent of the source paper's finite
classification. B reconstructed both candidate graphs from adjacency rules,
enumerated their triangles, discovered triangle-edge-incidence components,
and computed exact optima by exhaustive searches confined to components
with at most 10 edges. The parent reviewed and reran that script:

```powershell
cd research/round1/B
python verify_candidate.py
```

From the repository root, `python tools/check_records.py` independently
checks the exported D witness and its agreement with B's generated graph.
The saved result is [record_check.json](results/record_check.json).

This answers the regular-existence subquestion, not the full equality
classification. Model agreement alone is not proof. No novelty,
minimum-order, or human peer-review claim is made.

Open after these stages: human structural coverage for all codegree-four cores,
minimum template count beyond the fixed dictionary, equality classification,
and Tuza's conjecture for maximum average degree < 8.
