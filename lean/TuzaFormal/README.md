# TuzaFormal

Lean 4 + Mathlib formalization of the seven-regular equality example from
*A structural proof for codegree four and seven-regular equality examples in Tuza's conjecture* (Yanzhong Xu), §8.

## Main result

`Tuza.K4K5.main`: the Cartesian product K4□K5 (vertices `Fin 4 × Fin 5`) is
connected, 7-regular, has 20 vertices and 70 edges, every edge lies in a triangle, and

- triangle packing number ν = 13,
- triangle cover (transversal) number τ = 26 = 2ν,

so it attains equality in Tuza's conjecture.

## Files

- `TuzaFormal/Basic.lean`: triangle packings/covers, ν, τ, codegree; lemmas turning a bound plus a witness into equality.
- `TuzaFormal/Local.lean`: ν(K5) ≤ 2, τ(K5) ≥ 4, ν(K4) ≤ 1, τ(K4) ≥ 2.
- `TuzaFormal/Transfer.lean`: transfers those bounds to each row (K5) and column (K4) of K4□K5.
- `TuzaFormal/K4K5.lean`: the graph, the paper's 13-triangle packing and 26-edge cover, ν ≤ 4·2 + 5·1 and τ ≥ 4·4 + 5·2, and the main theorem.

## Notes

- No `sorry`. Some finite checks use `native_decide`, so they trust the Lean compiler in addition to the kernel.
- Not formalized: Prop 8.1 (general product formula), Prop 8.3 (infinite family), Thm 1.3 (codegree four).

## Build

```
lake exe cache get
lake build
```
A clean build takes about 8 minutes.
