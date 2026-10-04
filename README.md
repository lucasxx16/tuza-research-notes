# Tuza research notes

AI-assisted research on triangle packing and covering, with explicit proofs,
certificate data, and independently written verification programs. These are
research notes, not a claim of formal proof-assistant verification or human peer
review. No claim of novelty or a smallest equality graph is made.

## Manuscript preprint

**A structural proof for codegree four and seven-regular equality examples in Tuza's conjecture**, by Yanzhong Xu (Westlake University), October 3, 2026.

The [v0.1.0-preprint release](https://github.com/lucasxx16/tuza-research-notes/releases/tag/v0.1.0-preprint) contains the clean 25-page PDF, matching LaTeX source, and SHA-256 checksums.

The manuscript gives a human-readable structural proof under A1 (connected non-WKE links) and A2 (the common-neighbor degree budget), implying Proposition 9.1 and addressing Question 12.2 of [Gupta, arXiv:2608.06538v1](https://arxiv.org/abs/2608.06538v1). It also gives $K_4\square K_5$ with $\nu=13$ and $\tau=26$, and an infinite family of connected seven-regular equality graphs, answering the seven-regular existence subquestion following Question 12.3.

The full equality classification and the $\operatorname{mad}(G)<8$ implication remain unresolved here. This AI-assisted preprint has not undergone human peer review or formal proof-assistant verification. arXiv submission is in preparation, with endorsement pending; the manuscript has no arXiv identifier.

The starting questions come from Anish Gupta,
[Tuza's conjecture for graphs of maximum degree at most seven](https://arxiv.org/html/2608.06538v1)
and its [companion repository](https://github.com/agupta/tuza-maximum-degree-seven),
pinned to commit `bf8415fac44f4eeed6c0f7a2273b843d689b065e`.

**Current research target (updated 2026-10-03):** prove a uniform bound
`tau(G)<=c nu(G)` for every finite simple graph with an explicit
`c<165/59`, improving [Wang's bound](https://arxiv.org/html/2609.13831v1).
The user explicitly confirmed the unrestricted graph class. See the
[persistent objective](research/current_objective.txt). This target
does not declare the earlier mad<8 question solved.

## Results and limits

### Universal coefficient: round eleven

**The uniform target `c<165/59` remains unresolved.** The
[round-eleven report](docs/research-round11.zh-CN.txt) proves the additive
strictness statement `59 tau(G)<=165 nu(G)-1` when `nu(G)>0`, excluding
attainment of Wang's exact ratio. The normalized saving tends to zero
with the packing number; this is not a smaller uniform coefficient.

The [mixed-cover theorem](research/round11/E/mixed_cover_page_tails.txt)
allows arbitrary page counts on red edges outside an all-private maximum
packing. Selecting any set `D` of those red edges gives
`tau(H)<=2p+|D|-p^2/(p+2B_D)`, where `B_D` counts the remaining external
pages. It yields `tau(H)<=2p-1` and explicit necessary tails of long books
for ratios approaching two. In particular, a strict counterexample to
the proposed `1.99p` bound requires `p>100`; small-order searches cannot
refute that candidate. A uniform bound on the long-book tail is still missing.

A [realizable connected family](research/round11/E/multipage_matching_gap.txt)
has an unbounded gap between auxiliary ordinary matching and triangle
packing even with one nonprivate red edge, ruling out that simplification.
The [independent route](research/round11/D/packing_label_constraints.txt)
proves original-packing label restrictions and retains the actual cost
of opposite edges in Wang's random cover. A [seven-vertex graph with a hand proof](research/round11/D/actual_counterexample.txt)
refutes `a+b+c<=n` for arbitrary legal packing choices; existence of a
suitable optimized choice remains unresolved. The associated `467/167`
coefficient is only a conditional calculation.

### Universal coefficient: round ten

**No unconditional coefficient below `165/59` is proved here.**
The [round-ten report](docs/research-round10.zh-CN.txt) records an explicit
retained-slack inequality and a red-edge-budget route. In a red-blue graph
whose every triangle has exactly one red edge, if all participating red
edges are private and their number is at most three times the maximum
triangle packing number `p`, an auxiliary triangle-free graph gives
`tau<=9p/5`. A further cover bound quantifies the obstruction from
nonprivate red edges.

The remaining conjectural extension asks for `tau<=(2-epsilon)p` when
only the red edges of some maximum packing are required to be private,
under the same red-edge budget. The [main proof](research/round10/E/red_budget_reduction.txt)
shows that this extension, **if proved**, would imply the explicit universal
coefficient `165/59-epsilon/10000`. The extension itself remains unproved.
See the [independent route](research/round10/D/colored_slack_and_private_red_barrier.txt),
[main proof review](research/round10/C/review_E_full.txt), and
[independent proof review](research/round10/C/review_D_full.txt).

### Maximum average degree below eight

**The full implication `mad(G)<8 => tau(G)<=2nu(G)` remains unresolved here.**
Round five forces a reducible pair when minimum degree is at least
seven, average degree is below eight, and every degree-seven link has
complement a matching, P3, P4, or P3+K2, padded with isolated vertices to
order seven. Two new universal seven-triangle constructions handle P3+K2;
one was found by a bounded HPC-model search and then proved symbolically.
In the absence of the listed reducible pairs, sending charge only along
the seven, six, five, or six certified incidences for these four types gives
an explicit positive density surplus when vertices of degree at least
nine are present. These are conditional local
forcing results; their extra hypotheses need not survive deletion.

The independent route proves sharp local patch-density bounds, an eight-triangle
reduction valid beyond the old common-neighbor degree budget, and closure
across separators of order at most three. A smallest counterexample must
therefore be 4-connected. Another independent theorem excludes
every edge cut of size at most seven unless it isolates one vertex. A small
cut can therefore be the incident edges of a degree-five, six, or seven
vertex; this does not assert eight-edge-connectivity. Degree-five/six
vertices and degree-seven links outside the matching/P3/P4/P3+K2 families remain unresolved.

The equality route gives packing-loss bounds under edge deletion and the
exact packing/cover profile required on one side of the unresolved
three-shared-edge separator obstruction. Round six now proves, for every
finite simple graph with packing number one or two, that any prescribed
triangle edge belongs to a triangle cover of size at most twice that packing
number. Thus every triangle edge of a tight graph with packing number two
belongs to some minimum cover. This excludes the rich boundary profile at
packing number two, for both P4 and three-edge-star boundaries and without
an order bound. A possible rich side must have packing number at least three.
The earlier 906-graph atlas check is retained as historical finite evidence;
it is not a premise of this proof.

Round six also gives a twelve-vertex logical barrier: robustness, all conclusions
of Puleo's existing low-degree lemma, the treated degree-seven link condition,
and the previous connectivity bounds can hold simultaneously in a graph with
maximum average degree below eight. These necessary inputs alone cannot close
the joint counting argument. The example is not asserted irreducible and is
not a counterexample to Tuza's conjecture.

**Attribution correction (2026-10-03):** that example already violates
Botler--Fernandes--Gutiérrez (2020), Lemma 3.3. It is only a barrier to the
listed Puleo inputs, not to the complete known low-degree baseline.
That lemma already implies the following in every robust irreducible graph:

| Degrees | Maximum common neighbors | Equality condition |
| --- | --- | --- |
| 5, 5 | 3 | Both neighborhoods induce K5 |
| 5, 6 | 3 | No extra condition asserted here |
| 6, 6 | 4 | No extra condition asserted here |

See the [primary source, Lemma 3.3](https://arxiv.org/html/2002.07925v2#S3)
and the [persistent literature baseline](research/known_results.txt).
Our round-two literature review had already recorded this result. Later rounds
failed to carry it forward; the five/six bounds below are not new progress.

Round seven gives an explicit six-triangle/twelve-cover reduction of the example
and proves two general reductions for nonadjacent vertices with
a chosen common K4 and specified extra attachments, for degree sums at most
eleven or twelve. In a robust graph with no reducible set, these forbid a
degree-five/six pair from sharing K4. For a degree-six/six pair sharing a chosen K4, each
link's sole missing edge must join its two vertices outside that K4. These
are constructive restrictions, with the five/six conclusion already implied
by the cited literature. The global joint counting argument remains incomplete.

Round eight gives an alternative explicit reduction of the five/six
common-diamond case, including thin and non-thin six-links, recovering the
known codegree bound of three. The universal
selected-diamond construction uses six triangles and a cover whose size equals
the two nonadjacent centers' degree sum, allowing sums at most twelve under
its specified attachments. The generic recipe remains valid, but its five/six
consequence does not advance the known constraints on a minimal counterexample.

Round nine completely reduces the six/six case with exactly four common
neighbors, beyond the union-at-most-seven hypothesis of BFG Lemma 3.3.
The only possible common cores are C4, diamond, and K4; explicit constructions
have packing/cover sizes 4/8, 5/10, and 7/14. Their proofs allow arbitrary
ambient edges and require no numerical search. Combined with the published
bound of four, this gives **at most three common neighbors for every six/six
pair in a robust irreducible graph**. Thus all pairs of degree-five/six
vertices obey the same bound of three. This is a reviewed extension of our
documented baseline, not a claim of literature priority or a full mad<8 proof.

The combined overlap bounds give joint low-neighbor caps of **2, 3, and 3
at degrees 7, 8, and 9**, respectively. A degree-eight vertex with three
low neighbors must have two degree-five and one degree-six neighbors;
its other five neighbors induce K5 and all have degree at least nine.
An injective assignment to low-neighbor pairs bounds sharing among these
profiles: a degree-nine vertex can neighbor at most one such degree-eight
vertex. The argument applies to arbitrary robust irreducible graphs and
spends no surplus at degree eight. Funding the full degree-five/six/seven
deficit remains unresolved.

- [Round-nine correction, proofs, and limits in Chinese](docs/research-round9.zh-CN.txt)
- [Joint low-neighbor counts and the degree-eight profile](research/round9/E/joint_low_degree_counting.txt)
- [Exact-file review of the joint counts](research/round9/C/review_E_full.txt)
- [Round-nine coordinator decision and scope](research/round9/review_summary.txt)
- [Complete six/six exact-codegree-four reduction](research/round9/D/six_six_codegree_four.txt)
- [Exact-file review of all three six/six cases](research/round9/C/review_D_full.txt)
- [Known literature baseline and separately identified project extensions](research/known_results.txt)
- [Bounded source audit](research/round9/A/report.txt)
- [Round-eight results and completed structural subproblem in Chinese](docs/research-round8.zh-CN.txt)
- [Round-eight coordinator review](research/round8/review_summary.txt)
- [Common-diamond reduction and five/six codegree at most three](research/round8/D/diamond_overlap_reduction.txt)
- [Exact-file review of the diamond-overlap theorem](research/round8/C/review_D_full.txt)
- [Round-seven results and limits in Chinese](docs/research-round7.zh-CN.txt)
- [Round-seven coordinator review](research/round7/review_summary.txt)
- [Two low-pair reductions and overlap restrictions](research/round7/D/low_degree_overlap_reductions.txt)
- [Exact-file review of the low-pair theorems](research/round7/C/review_D_full.txt)
- [One bounded fixed-pair experiment](research/round7/B/report.txt)
- [Round-six consolidation and limits in Chinese](docs/research-round6.zh-CN.txt)
- [Prescribed-edge covers for packing number at most two](research/round6/D/prescribed_edge_cover_k2.txt)
- [Exact-file review of the prescribed-edge theorem](research/round6/C/review_D_full.txt)
- [Twelve-vertex barrier to the existing joint degree caps](research/round6/D/joint_caps_barrier.txt)
- [Exact-file review of the joint-counting barrier](research/round6/C/review_D_joint_caps.txt)
- [Round-six coordinator review](research/round6/review_summary.txt)
- [Round-five results and limits in Chinese](docs/mad8-round5.zh-CN.txt)
- [P3+K2 extension and two universal seven-triangle certificates](mad8/round5/E/p3_plus_edge_complements.txt)
- [Equality, edge deletion, and the exact boundary profile](mad8/round5/D/equality_boundary_profiles.txt)
- [Two fixed MILP instances and their witnesses](mad8/round5/B)
- [Independent exact certificate verifier](mad8/round5/C/check_literal_certificates.py)
- [Bounded atlas experiment and its limits](mad8/round5/B_D/report.txt)
- [Round-five coordinator review](mad8/round5/review_summary.txt)
- [Round-four results in Chinese](docs/mad8-round4.zh-CN.txt)
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

**The human structural-reducibility proof for all original A1+A2 configurations
is now complete.** Empty and single-edge cores are excluded by WKE arguments;
all nine other four-vertex core types have reviewed constructive proofs:
P3 plus isolate, 2K2, K1,3, P4, triangle plus isolate, paw, C4, diamond, and K4.
These types correspond to all 1,144 saved records, but neither the counts nor
catalogue completeness is a premise. The final triangle-plus-isolate proof
establishes support separately, without assuming a core perfect matching.

The combined theorem retains connected non-WKE links (A1) and the original
common-vertex degree budget (A2). Its component recipes need not be the same
nine catalogue templates. Structural completeness, record coverage, and the
finite-dictionary minimum are separate results; no unrestricted template
minimum or full mad<8 implication follows. The upstream graph census and
original certificate finder were not rerun for these structural proofs.

- [Complete structural theorem and proof index](compression/theory/complete_structural_proof.txt)
- [Latest structural results and precise limits, in Chinese](docs/research-round8.zh-CN.txt)
- [Final dependency and scope review](research/round8/C/structural_scope.txt)
- [Complete human paw-core proof](research/round8/E/paw_core.txt)
- [Exact-file paw review](research/round8/C/review_E_full.txt)
- [Complete human triangle-plus-isolate proof](research/round8/E/triangle_isolate_core.txt)
- [Exact-file triangle-plus-isolate review](research/round8/C/review_tri_full.txt)
- [Complete human C4-core proof](research/round7/E/c4_core.txt)
- [Exact-file C4 proof review](research/round7/C/review_E_full.txt)
- [Complete human diamond-core proof](research/round6/E/diamond_core.txt)
- [Exact-file diamond proof review](research/round6/C/review_E_full.txt)
- [Independent check of the 42-record Lemma-K transfer](research/round6/C/check_diamond_transfer_literal.py)
- [Earlier five-core structural results](docs/structural-progress.zh-CN.txt)
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
| `research/round6/` | Diamond proof, prescribed-edge theorem, joint-counting barrier, source audits, and saved-record checks |
| `research/round7/` | C4 proof, low-degree overlap reductions, bounded fixed-graph search, and independent reviews |
| `research/round8/` | Final two core proofs, diamond-overlap reduction, completed structural scope, and source audits |
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

Round eight's proofs are symbolic and have no numerical-check premise. The two
planned fixed-patch searches were cancelled after the explicit construction
was found; no numerical candidate was supplied to the independent researcher.

Round seven's independent fixed-graph check rebuilds J and its neighborhood
patch, checks both the 7/13 and 6/12 certificates against all ambient hub
triangles, and rejects five damaged controls. It does not rerun the MILP:

```shell
python research/round7/C/check_J_pair_literal.py
```

The optional `research/round7/B/search_low_pair.py` uses NumPy and SciPy for
one sixty-second-capped MILP. It proposes a fixed-instance candidate; the
general reductions and complete C4 proof are separate symbolic arguments.

Round six's mathematical proofs are self-contained symbolic arguments. The
following independent check reads the saved catalogue, verifies the 42 literal
Lemma-K transfer witnesses and rejects 126 damaged controls. It is a diagnostic
for that subset, not a premise or verification of the complete diamond proof:

```shell
python research/round6/C/check_diamond_transfer_literal.py
```

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

Open mathematical work: template minimality beyond the fixed dictionary, full
equality classification, the maximum-average-degree-below-eight question, and an
unconditional uniform coefficient below 165/59 for all finite simple graphs.
