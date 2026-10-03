# Tuza equality research

Private research record, started 2026-10-03 (Asia/Shanghai).

Selected first question: does a finite simple connected 7-regular graph with
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

## Accepted result

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

Deferred questions: compression of the 1,144 codegree-four certificates into
structural templates, and Tuza's conjecture for maximum average degree < 8.
