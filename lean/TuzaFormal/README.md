# TuzaFormal

Lean 4 + Mathlib formalization of
*A structural proof for codegree four and seven-regular equality examples in Tuza's conjecture*
(Yanzhong Xu).

## Final status (Oct 13, 2026)

Formalized, with no `sorry`, no `native_decide` and no custom axioms:

| Paper | Lean | File |
|---|---|---|
| Theorem 1.3 (codegree-four structural theorem) | `Tuza.CodegreeFour.structural_codegree_four` | `CodegreeFour.lean`, `GenericCert.lean`, `CodegreeFourMain.lean` |
| Lemma 2.1, Defs 1.1–1.2 | `reduction_bridge` | `Reducibility.lean` |
| Lemma 2.2 (graphs on 4 vertices) | 64-case classification | `Classify.lean` |
| Puleo Cor. 4.12 (as used in the paper) | `puleo_large_indep` (theorem) | `Puleo.lean` |
| Proposition 8.1 (ν, τ of `F □ J`, arbitrary finite `F`, `J`) | `Tuza.Product.prop_8_1` | `Product.lean` |
| Lemma 8.2 (ν, τ of K₄, K₅) | `nu_K4`, `tau_K4`, `nu_K5`, `tau_K5` | `ProductExamples.lean` |
| Theorem 1.4 (K₄□K₅: 7-regular, ν = 13, τ = 26 = 2ν) | `Tuza.K4K5.main` | `K4K5.lean` + `ProductExamples.lean` |
| Proposition 8.3 (infinite family G_k = K₄□C_{2k}(1,3), k ≥ 4) | `Tuza.Family.infinite_family` | `Family.lean` + `ProductExamples.lean` |

The ν/τ parts of `K4K5.main` and `infinite_family` are derived from Prop 8.1 + Lemma 8.2
(via `K4K5_via_prod` and `infinite_family_via_prod`); the earlier stand-alone packing/cover
proofs were removed. The two theorems are therefore stated at the end of
`ProductExamples.lean` (same names and statements as before), because `Product.lean`
needs the graph definitions from `K4K5.lean` / `Family.lean`.

**Axiom audit.** `lake env lean Axioms.lean` prints:

```
'Tuza.K4K5.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tuza.Family.infinite_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tuza.CodegreeFour.structural_codegree_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tuza.Product.prop_8_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tuza.Product.K4K5_via_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tuza.Product.infinite_family_via_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All finite checks use `decide +kernel` (checked by the Lean kernel) or structured proofs.

**Known limitations.**
- Puleo's Corollary 4.12 is formalized only for `|N(z)| = 7` with `|I| = 4`, the only case the
  paper uses (both call sites have `|N(u)| = 7`). The general `n ≥ 6` statement is not formalized.
- The case trees for Props 6.3/6.4/6.7 were found by a Python generator that is not committed;
  Lean checks every leaf, so the generator is not trusted.
- `Sanity.lean` shows the hypotheses (A1), (A2) of Theorem 1.3 are satisfiable (non-vacuity).

No mathematical errors were found in the paper. A few steps are terse (all in Prop 8.3: the
"triangle lies in one column" argument, the triangle-free hypothesis on J, and the 2k ≥ 8 bound).
The formalization fills them in.

## Files

- `TuzaFormal.lean`: root module importing everything.
- `Axioms.lean`: `#print axioms` on the main theorems.
- `TuzaFormal/Basic.lean`: triangle packings/covers, ν, τ, codegree; bound + witness ⇒ equality lemmas.
- `TuzaFormal/Local.lean`: ν(K5) ≤ 2, τ(K5) ≥ 4, ν(K4) ≤ 1, τ(K4) ≥ 2 on `Fin 5` / `Fin 4`.
- `TuzaFormal/Transfer.lean`: transfer of packing/cover bounds along embeddings.
- `TuzaFormal/K4K5.lean`: the graph K4□K5; connectivity, 7-regularity, 20 vertices, 70 edges, every edge in a triangle.
- `TuzaFormal/Family.lean`: `box J = K4□J`, its regularity and connectivity, the circulant `C_n(1,3)` (triangle-free, 4-regular, connected for even n ≥ 8).
- `TuzaFormal/Product.lean`: Proposition 8.1 for arbitrary finite factors (fiber decomposition).
- `TuzaFormal/ProductExamples.lean`: Lemma 8.2, `K4K5.G = ⊤□⊤`, `Family.box J = ⊤□J`, and the final `K4K5.main`, `Family.infinite_family`.
- `TuzaFormal/Reducibility.lean`: WKE, reducibility (Defs 1.1–1.2), Lemma 2.1.
- `TuzaFormal/Classify.lean`: Lemma 2.2, classification of 4-vertex graphs.
- `TuzaFormal/Puleo.lean`: Puleo Cor. 4.12, 7-vertex case (Hall's theorem + case analysis).
- `TuzaFormal/CodegreeFour.lean`: `HubConfig`, (A1)/(A2), Props 3.1–5.3, Lemma 6.1, diamond (Prop 6.2).
- `TuzaFormal/GenericCert.lean`: `Fin 10` certificate/WKE-witness transfer (`reducible_of_spec`, `wke_of_spec`).
- `TuzaFormal/CodegreeFourMain.lean`: Props 6.3 (C₄), 6.4 (paw), 6.7 (K₃+K₁) and `structural_codegree_four`.
- `TuzaFormal/Sanity.lean`: a concrete `Fin 10` `HubConfig` satisfying (A1) and (A2).

## History notes

- Soundness fix (Oct 11): an early version of (A1) required the link graph to be connected on all
  of `V`, which is unsatisfiable, so theorems with (A1) as hypothesis were vacuous. (A1) now uses
  `LinkConnected` (connectivity of the link on `N(z)`, as in the paper), and `Sanity.lean` shows it is satisfiable.
- Oct 12: all `native_decide` replaced by `decide +kernel`; the Puleo axiom replaced by a proof.
- Oct 13: Prop 8.1 formalized; Theorem 1.4 / Prop 8.3 rederived from it.

## Build

```
lake exe cache get
lake build
lake env lean Axioms.lean
```
A clean build takes about 8 minutes.
