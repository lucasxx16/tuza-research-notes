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
  **Proved:** full `prop31`; Prop 4.2 certificate + Fin-10 locals;
  `lemma41_no_private`, `not_adj_hub_priv`, `lemma41_priv_has_core` (Lemma 4.1(1) full);
  **full** Lemmas 4.3 and 4.4(1) (star/path).
  **Partial / sorry:** `lemma41_edge_hit` (setup done; WKE witness deferred),
  `lemma41_cross` part 3, `labels10_of_hub`, `matching_core_reducible`,
  `structural_codegree_four` (excludes ≤1-edge cores; nine certificates open).

  Paper note: Lemma 4.1(2)–(3) WKE witnesses match the paper outline; finishing them
  unlocks Prop 4.2 wiring via `matching_core_reducible`. No gap found in 4.1(1) or 4.3–4.4.

## Build

```
lake exe cache get
lake build
```
A clean build takes about 8 minutes.
