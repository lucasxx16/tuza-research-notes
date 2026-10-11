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

- `TuzaFormal/Reducibility.lean`: Defs 1.1–1.2; ambient residual packing/cover.
  **Proved:** `reduction_bridge` (Lemma 2.1) — fully, no `sorry`.
- `TuzaFormal/CodegreeFour.lean`: `HubConfig`, (A1)/(A2), `core_edge_bound` (proved).
  **Axiom:** `puleo_large_indep`.
  **Proved (Prop 3.1):** full `prop31` (edgeless via Puleo; one-edge via WKE trichotomy);
  `wke_private_edge`, `wke_private_attach`, `one_edge_is_wke`.
  **Proved (Prop 4.2):** all five local lemmas + `prop42_certificate` (Fin-10 transfer).
  **Proved (sparse-core helpers):** `core4_distinct`, hub/private label lemmas;
  `StarCore.star_empty_outside_center`, `StarCore.star_wke_no_attach_no_priv`
  (zero leaf attachments + no private edge ⇒ WKE);
  `PathCore.path_empty_outside_center` and the corresponding no-attachment case of
  `path_leaf_attachment`.
  **Partial:** `star_two_leaf_attachments` / `path_leaf_attachment` still `sorry` on the
  private-edge and single-attachment branches (paper cases 1–2).
  **Sorry:** `lemma41_cross` (Lemma 4.1(3) crossed matching), `structural_codegree_four`.

  Paper note: Lemma 4.1(3) remains the bottleneck for wiring Prop 4.2 into the top-level
  structural theorem; star/path zero-attachment WKE witnesses match the paper.


## Build

```
lake exe cache get
lake build
```
A clean build takes about 8 minutes.
