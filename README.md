# Tuza research notes

AI-assisted research on triangle packing and covering, with explicit proofs,
certificate data, and independently written verification programs. These are
research notes, not a claim of formal proof-assistant verification or human peer
review. No claim of novelty or a smallest equality graph is made.

The starting questions come from Anish Gupta,
[Tuza's conjecture for graphs of maximum degree at most seven](https://arxiv.org/html/2608.06538v1)
and its [companion repository](https://github.com/agupta/tuza-maximum-degree-seven),
pinned to commit `bf8415fac44f4eeed6c0f7a2273b843d689b065e`.

## Results and limits

### Maximum average degree below eight

**The full implication `mad(G)<8 => tau(G)<=2nu(G)` remains unresolved here.**
The latest round forces a reducible pair when minimum degree is at least
seven, average degree is below eight, and every degree-seven link has
complement a matching, P3 plus four isolated vertices, or P4 plus three
isolated vertices. The new P4 case permits two exceptional neighbors.
In the absence of the listed reducible pairs, sending charge only along
the seven, six, or five certified incidences for these three types gives
an explicit positive density surplus when vertices of degree at least
nine are present. These are conditional local
forcing results; their extra hypotheses need not survive deletion.

The independent route proves sharp local patch-density bounds, an eight-triangle
reduction valid beyond the old common-neighbor degree budget, and closure
across separators of order at most three. A smallest counterexample must
therefore be 4-connected. The latest independent theorem also excludes
every edge cut of size at most seven unless it isolates one vertex. A small
cut can therefore be the incident edges of a degree-five, six, or seven
vertex; this does not assert eight-edge-connectivity. Degree-five/six
vertices and degree-seven links outside the matching/P3/P4 families remain unresolved.

- [Latest results and limits in Chinese](docs/mad8-round4.zh-CN.txt)
- [P4-complement extension and selected-incidence density bound](mad8/round4/E/p4_complement_links.txt)
- [No nontrivial edge cut below eight](mad8/round4/D/seven_edge_cuts.txt)
- [Round-four coordinator review](mad8/round4/review_summary.txt)
- [Round-four exact-file mainline review](mad8/round4/C/review_E_full.txt)
- [Round-four exact-file independent review](mad8/round4/C/review_D_full.txt)
- [Round-three results and limits in Chinese](docs/mad8-round3.zh-CN.txt)
- [P3-complement links and high-degree-neighbor discharging](mad8/round3/E/p3_complement_links.txt)
- [General counting criterion and the five-neighbor specialization](mad8/round3/E/charge_tradeoff.txt)
- [Small-edge-cut theorem](mad8/round3/D/small_edge_cuts.txt)
- [Round-three coordinator review and computational scope](mad8/round3/review_summary.txt)
- [Round-two results in Chinese](docs/mad8-round2.zh-CN.txt)
- [Three constructions and all matching-complement degree-seven links](mad8/round2/E/matching_complement_links.txt)
- [Three-edge boundary theorem and 4-connectivity](mad8/round2/D/three_edge_boundary.txt)
- [Round-two coordinator review](mad8/round2/review_summary.txt)
- [Results, proof ideas, and limits in Chinese](docs/mad8-progress.zh-CN.txt)
- [Mixed-degree Fano reduction and sharp conditional density bound](mad8/round1/E/mixed_fano_and_density.txt)
- [Why maximum average degree alone cannot prune the old local patches](mad8/round1/D/local_density_obstruction.txt)
- [Dense-patch certificate without the old degree budget](mad8/round1/D/dense_pair_certificate.txt)
- [Gluing along an edge and minimal-counterexample structure](mad8/round1/D/two_separator_gluing.txt)
- [Independent proof review](mad8/round1/C/review_full_candidates.txt)
- [Coordinator decision and remaining obligations](mad8/round1/review_summary.txt)

### Certificate compression

**Nine signed templates cover all 1,144 supplied codegree-four records. Nine is
optimal within the specified dictionary of 499 catalogue-derived pattern orbits.**
It is not a global minimum over arbitrary structural templates.

Every selected template has a universal packing/deletion construction proving
reducibility whenever its required-present and required-absent edge conditions
hold. The upper bound is an explicit nine-template cover. The lower bound is nine
records such that every candidate covers at most one. The independent verifier
rebuilds the entire dictionary and incidence relation from the original witnesses,
then checks both bounds and all 1,144 exported certificates. No solver's floating
point status is needed for this proof of optimality.

Human-readable proofs now settle five entire core types: **P3 plus an isolated
vertex, K1,3, 2K2, P4, and K4**. Together these types account for 574 of the 1,144
saved records; the proofs do not use those counts or the catalogue as premises.
Empty and single-edge cores are also excluded structurally, using explicit WKE
witnesses and Puleo's Corollary 4.12. Four types remain: triangle plus isolated
vertex, paw, C4, and diamond (570 saved records). The upstream graph census and
original certificate finder were not rerun.

- [Latest structural results and remaining cases, in Chinese](docs/structural-progress.zh-CN.txt)
- [New sparse-core proofs: P3 plus isolated and K1,3](compression/round3/E/sparse_star_cores.txt)
- [P4 proof and perfect-matching support lemma](compression/round3/E/path_core.txt)
- [K4 proof using two binary attachment partitions](compression/round3/D/k4_human_proof.txt)
- [Empty/single-edge exclusions](compression/round3/E/zero_core_exclusions.txt)
- [Final independent scope review](compression/round3/C/final_scope_review.txt)

- [Results and scope in Chinese](docs/compression.zh-CN.txt)
- [Nine literal templates](compression/templates/optimal_patterns.txt)
- [Universal template lemma and historical eleven-template stage](compression/templates/proof.txt)
- [Nine templates and record assignments](compression/templates/optimal_templates.json)
- [All 1,144 exported witnesses](compression/templates/optimal_transformed_certificates.json)
- [Exact nine-record lower bound](compression/set_cover/lower_bound.json)
- [Human-readable 2K2 proof](compression/theory/human_case_2k2.txt)
- [Matching, cover normalization, and exchange lemmas](compression/theory/proof.txt)
- [Independent mathematical review](compression/verification/review.txt)

The final assignment uses 5, 6, or 7 packed triangles on 888, 254, or 2 records,
respectively. Each witness has at most one hub-free triangle and no triangle
wholly inside the four-vertex core. Historical eleven-template results are retained
for comparison; their stronger six-triangle bound does not apply to the final nine.

### Connected 7-regular equality graphs

The graph $G=K_4\square K_5$ is simple, connected, and 7-regular, with 20 vertices,
70 edges, $\nu(G)=13$, and $\tau(G)=26=2\nu(G)$. Every edge lies in a triangle.
Triangles are confined to the four K5 rows and five K4 columns; their edge sets
are disjoint, so packing and covering optima add.

More generally, $K_4\square H$ is a 7-regular equality graph for every connected
triangle-free 4-regular graph H. Cartesian additivity for both invariants is proved
in the notes. This answers the regular-existence subquestion, not the full equality
classification or a minimum-order question.

- [Proof and scope in Chinese](docs/equality.zh-CN.txt)
- [20-vertex construction and proof](equality/construction/proof.txt)
- [Explicit packing and cover](equality/construction/certificates.json)
- [Independent family and Cartesian additivity](equality/theory/addendum.txt)
- [Independent review](equality/review/review.txt)

## Repository map

| Directory | Contents |
| --- | --- |
| `docs/` | Consolidated Chinese result reports |
| `equality/` | Equality constructions, proofs, literature notes, and exact checks |
| `mad8/` | Partial reductions, density barriers, source audits, and named-graph checks |
| `compression/input/` | Unmodified, attributed upstream certificate catalogue |
| `compression/templates/` | Signed patterns, incidence data, exports, and generators |
| `compression/theory/` | Structural proofs and reusable lemmas |
| `compression/verification/` | Independent decoders, audits, and review notes |
| `compression/set_cover/` | Finite-dictionary optimizer and exact upper/lower certificates |
| `compression/experiments/` | Supplemental fixed-packing cover/exchange experiments |
| `compression/round3/` | New structural proofs, source reading, and bounded witness checks |
| `compression/literature/` | Source survey with explicit reading limits |
| `tools/`, `results/` | Cross-record checks, public-content audit, and artifact hashes |

Historical role letters in reports identify separate implementations/reviews; they
are not mathematical hypotheses. Dispatch prompts, provider configuration, and
session transcripts are excluded from the public record.

## Reproduce the checks

Run from the repository root with Python 3.10 or newer. These checks require only
the standard library. Do not use `python -O`, which disables assertions.

For the new maximum-average-degree notes:

```shell
python mad8/round1/B/check_named_graphs.py
python mad8/round2/B/check_core_matching.py
python mad8/round2/C/check_literal_C4.py
python mad8/round2/B/check_repaired_fano.py
```

This checks the literal reductions on K9 minus one edge and the maximal
codegree-four patch, and computes exact maximum average degrees for three named
graphs. It uses rational arithmetic over their vertex subsets; it does not run
a graph census. The round-two checks additionally verify the literal induced-C4
and repaired-Fano certificates. The general lemmas are proved in the text.

Round three's proofs use previously checked certificates and human arguments.
Its optional diagnostic `python mad8/round3/B/search_p3_center.py` requires
NumPy and SciPy and makes one bounded MILP call on a fixed graph. It imposes
extra packing/cover restrictions; solver infeasibility is not a theorem about
unrestricted pair reducibility and is not a premise of the proofs.

For the certificate-compression archive:

```shell
python tools/check_records.py
python compression/verification/check_optimal_export.py
python compression/set_cover/independent_check.py
```

The export check also runs the independent dictionary/optimality reconstruction.
For the original eleven-template stage, optionally run
`python compression/verification/check_D_templates.py`.

For the new human constructions, these standard-library checks use only saved
records and independently check 536 sparse/path witnesses and 21 K4 witnesses:

```shell
python compression/round3/C/check_sparse_witnesses.py
python compression/round3/C/check_k4_export.py
```

The K4 witnesses can be regenerated from the two explicit recipes with
`python compression/round3/B/check_k4_recipes.py`. These scans are supplementary
checks of the constructions, not premises of the human forcing arguments. The
one-link diagnostic `check_leaf_links.py` is retained as research history, is not
part of these reproduction commands, and is not used in any proof.

For independent exact computation of the equality graphs:

```shell
cd equality/computation
python verify_candidate.py
```

This last command regenerates that directory's graph/result files and timing report.
The bounded set-cover search in `compression/set_cover/solve_cover.py` additionally
requires NumPy and SciPy; `compression/templates/compress.py` uses NumPy. Neither
is needed to verify the saved exact result.

`results/artifact_sha256.json` records hashes of committed Git blobs. Hashes check
artifact integrity, not mathematical correctness. The upstream input's exact bytes
are preserved across platforms; see its [provenance and license notice](compression/input/PROVENANCE.txt).

## Public repository maintenance

Before publishing changes, run `python tools/check_public_content.py --history`.
It checks tracked files and reachable Git history for selected credential patterns,
personal filesystem paths, and internal session artifacts, printing locations only.
It is a focused check, not a guarantee that every possible secret format is detected.
Local session files, credentials, and editor settings are ignored by Git.

Open mathematical work: a census-free structural proof for the remaining cores,
template minimality beyond the fixed dictionary, full equality classification,
and the maximum-average-degree-below-eight question.
