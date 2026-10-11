# TuzaFormal

Lean 4 + Mathlib formalization of the seven-regular equality example from
*A structural proof for codegree four and seven-regular equality examples in Tuza's conjecture* (Yanzhong Xu), §8.

## Main result

`Tuza.K4K5.main`: the Cartesian product K4□K5 (vertices `Fin 4 × Fin 5`) is
connected, 7-regular, has 20 vertices and 70 edges, every edge lies in a triangle, and

- triangle packing number ν = 13,
- triangle cover (transversal) number τ = 26 = 2ν,

so it attains equality in Tuza's conjecture.

`Tuza.Family.infinite_family` (Prop 8.3): for every k ≥ 4 (stated as k = m + 4),
G_k = K4□J_{2k}, where J_{2k} is the circulant on ZMod (2k) with t ~ t±1, t±3,
is connected, 7-regular, has 8k vertices and 28k edges, ν = 2k and τ = 4k = 2ν.
This is proved for general k (no enumeration over k). The general statements are
`box_regular` (K4□J is (d+3)-regular when J is d-regular), `box_connected`, and
`box_nu` / `box_tau` (ν = |V(J)|, τ = 2|V(J)| when J is triangle-free).

## Files

- `TuzaFormal/Basic.lean`: triangle packings/covers, ν, τ, codegree; lemmas turning a bound plus a witness into equality.
- `TuzaFormal/Local.lean`: ν(K5) ≤ 2, τ(K5) ≥ 4, ν(K4) ≤ 1, τ(K4) ≥ 2.
- `TuzaFormal/Transfer.lean`: transfers those bounds to each row (K5) and column (K4) of K4□K5.
- `TuzaFormal/Family.lean`: K4□J for triangle-free J, the circulant J_{2k}, and Prop 8.3.
- `TuzaFormal/K4K5.lean`: the graph, the paper's 13-triangle packing and 26-edge cover, ν ≤ 4·2 + 5·1 and τ ≥ 4·4 + 5·2, and the main theorem.

## Notes

- No `sorry`. Some finite checks use `native_decide`, so they trust the Lean compiler in addition to the kernel.
- Not formalized: Prop 8.1 for arbitrary factors (only the K4□J and K4□K5 cases are used).
- In `Family.lean`, `native_decide` is used only for fixed facts about K4.

## Theorem 1.3 (in progress)

- `TuzaFormal/Reducibility.lean`: Defs 1.1–1.2; **proved** `reduction_bridge` (Lemma 2.1).
- `TuzaFormal/CodegreeFour.lean`: `HubConfig`, (A1)/(A2), `core_edge_bound`.
  **Axiom:** `puleo_large_indep`.
  **Proved:** full `prop31`; Prop 4.2 (`matching_core_reducible`);
  Lemma 4.1(1)–(3) full; Lemmas 4.3 and 4.4(1);
  **Lemma 4.5** (`lemma45_certificate`) Fin-10 packing/cover;
  **Prop 4.6** (`star_core_reducible`) full;
  **Lemma 4.4(2)** (`path_center_both_privates`) full;
  **Prop 4.7** (`path_core_reducible`) full (crossed + same-singleton+(A2));
  **Lemma 4.8** (`lemma48_certificate`) full Fin-10 packing/cover;
  **Lemma 3.2** / **Prop 4.9** full; **Lemma 5.1** (`lemma51`) full;
  Prop 5.3(G)/(E) fully proved; Lemma 5.2 fully proved;
  **G packing generalized** to α(z)/β(y) via 4 Fin-10 variants;
  **`k4_core_reducible` fully proved** (no sorry); K₄ wired into
  `structural_codegree_four`; remaining sorry is only diamond/C₄/paw/K₃+K₁.

  Paper note: G packing now matches paper Prop 5.3(G) with general α(z),β(y).
  **Lemma 6.1 fully proved** (including same-singleton via lemma32).
  Diamond: Fin-10 D1 packing/cover infra + `diamond_full_support` proved;
  `diamond_certificate_D1` / D2–D5 / exhaustion still sorry.
  C₄/paw/K₃+K₁ still sorry. Next: discharge D1 coversZ, then D2–D5.

## Build

```
lake exe cache get
lake build
```
A clean build takes about 8 minutes.

## Progress (diamond D1)

- `diamond_certificate_D1` fully proved (packing, cover edges, size, external, coversZ via rim deletion).
- Remaining sorries: `diamond_core_reducible` (force D1–D5), `c4_core_reducible`, `paw_core_reducible`, `k3k1_core_reducible`, residual in `structural_codegree_four`.

## Progress (diamond D3 + D5)

- `diamond_certificate_D3` fully proved (unused privates).
- `diamond_certificate_D5` fully proved (private edges + double center).
- Still open: D2, D4 certificates; `diamond_core_reducible` forcing; C₄/paw/K₃+K₁; residual structural sorry.

## Progress (Prop 6.2 certificates complete)

- Fully proved diamond certificates **D1, D2, D3, D4, D5** (packing, cover, external, coversZ).
- `diamond_center_unique`: centres p,q have unique A/B neighbours (coreDeg 3 + A2 + full_support).
- `diamond_core_reducible` still sorry on the paper's attachment classification that forces one of D1–D5.
- Still sorry: `c4_core_reducible`, `paw_core_reducible`, `k3k1_core_reducible`, residual in `structural_codegree_four`.
- No paper gaps found in Prop 6.2 certificate statements; forcing argument not yet checked in Lean.

## Progress (diamond forcing partial)

- D1–D5 certificates: fully proved.
- D1 force helpers + condition (3) failure → D1: proved in `diamond_core_reducible`.
- Oriented lemmas: `diamond_sparse_split_A` (→ D2/D3), `diamond_paired_D5`.
- Remaining in `diamond_core_reducible`: Cases 1–3 classification (sparse/dense/paired) still sorry after centre-unique setup.
- Still sorry: C₄, paw, K₃+K₁, structural residual.

## Soundness fix: (A1) link connectivity (2026-10-11)

**Bug.** Earlier commits defined (A1) with `(linkGraph G u).Connected` on all of `V`. In any
hub config the hub `u` is isolated in its own link, so this was unsatisfiable (and the helper
`card_of_link_connected` derived `|V| = 7`, contradicting the 8 vertices `u ∪ N(u)`). Every
theorem with (A1) as a hypothesis was therefore vacuously true in those commits.

**Fix.**
- New `LinkConnected G z`: any two vertices of `N(z)` are joined in `linkGraph G z`
  (connectivity of the link induced on `N(z)`, as in the paper). (A1) now uses it.
- `card_of_link_connected` removed.
- `puleo_large_indep` (still an axiom, Puleo Cor 4.12) restated on the link: `6 ≤ |N(z)|`,
  `LinkConnected G z`, an independent `I ⊆ N(z)` with `|I| = |N(z)| − 3` ⇒ `IsWKE (linkGraph G z)`.
  (Vertices outside `N(z)` are isolated in `linkGraph`, so this matches WKE of the induced link.)
- `TuzaFormal/Sanity.lean`: a concrete `HubConfig` on `Fin 10` with both hub links
  `LinkConnected` (so connectivity no longer forces `|V| = 7`). Not checked: a concrete
  example that also satisfies the non-WKE part of (A1).

**Status after the fix (full `lake build` passes, against the new definitions).**
No proof used `exfalso` on the broken hypothesis. The only route to the contradiction was
`card_of_link_connected`, and that lemma is now gone. These results are re-verified:
Prop 3.1 (`prop31`, `one_edge_is_wke`), Lemma 4.1 / Prop 4.2 (matching), Lemmas 4.3/4.4 and
Props 4.6/4.7 (star, path), Lemma 4.8 / Prop 4.9 (P₄), Lemma 3.2, Lemma 5.1/5.2 / Prop 5.3 /
`k4_core_reducible`, Lemma 6.1, D1–D5 certificates, `diamond_center_unique`, and the
condition (3) → D1 branch of the diamond case.
Still `sorry` (5): the diamond Cases 1–3 classification, `c4_core_reducible`,
`paw_core_reducible`, `k3k1_core_reducible`, and the residual in `structural_codegree_four`.

**Also fixed:** the committed HEAD (`781d372`) did not compile when checked with
`lake env lean`. The cause was `rcases … rfl` / `obtain ⟨_, _, rfl⟩` removing named variables
in the `packing53G_*`, `cover53G_card`, `packing*_disjoint`, and diamond-forcing proofs. It is
fixed by substituting in the other direction (`subst αz βy`, `subst w`, `_` placeholders).

## Status update (Oct 12, 2026): Theorem 1.3 has no `sorry` left

`structural_codegree_four` builds with a full `lake build` and **zero `sorry` warnings**.
`#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`, the stated axiom
`puleo_large_indep` (Puleo Cor. 4.12), and the `native_decide` auxiliary axioms from the
older Fin-10 card checks.

- Lemma 2.2 (`Classify.lean`): a generated 64-case split that classifies every graph on 4 vertices.
- Prop 6.2 (diamond): Cases 1–3 forced with a hand-written proof (`DiamondCtx`).
- `GenericCert.lean`: a certificate (or WKE witness) is written on `Fin 10` labels. Its finite
  conditions are checked with `decide +kernel` (not `native_decide`), and
  `reducible_of_spec` / `wke_of_spec` carry them over to `G`.
- Props 6.3 (C₄), 6.4 (paw) and 6.7 (K₃+K₁) in `CodegreeFourMain.lean`: a Python generator
  (`gen/*.py`, not committed) found the case trees over the private-attachment bits. Every leaf
  is closed by a certificate, support, the budget (2), link connectivity, or an explicit non-WKE
  witness. Lean checks every leaf. The generator found no uncovered configuration, so the
  paper's case analysis holds at this finite level.
