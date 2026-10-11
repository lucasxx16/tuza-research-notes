import TuzaFormal.Basic

/-!
# Reducibility framework (Defs 1.1–1.2) and the reduction bridge (Lemma 2.1)

From Y. Xu, *A structural proof for codegree four and seven-regular equality examples
in Tuza's conjecture*. Case analysis for Theorem 1.3 is in `CodegreeFour.lean`.
-/

open Finset SimpleGraph

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set of edges is a matching if every edge is present and no two share a vertex. -/
def IsEdgeMatching (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset

/-- Weak König–Egerváry (Def 1.1). -/
def IsWKE : Prop :=
  ∃ (M : Finset (Sym2 V)) (Q : Finset V),
    IsEdgeMatching G M ∧ Q.card ≤ M.card ∧
    ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M

/-- Display (1): a concrete WKE witness. -/
def IsWKEWitness (M : Finset (Sym2 V)) (Q : Finset V) : Prop :=
  IsEdgeMatching G M ∧ Q.card ≤ M.card ∧
  ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M

lemma isWKE_of_witness {M : Finset (Sym2 V)} {Q : Finset V}
    (h : IsWKEWitness G M Q) : IsWKE G := ⟨M, Q, h⟩

/-- A reduction certificate for a nonempty vertex set `Z` (Def 1.2). -/
structure ReductionCertificate (Z : Finset V) where
  packing : Finset (Finset V)
  cover : Finset (Sym2 V)
  isPacking : IsTrianglePacking G packing
  size : cover.card ≤ 2 * packing.card
  coversZ : ∀ t ∈ G.cliqueFinset 3, (∃ z ∈ Z, z ∈ t) → ¬ Disjoint cover (triEdges t)
  external : ∀ t ∈ packing, ∀ e ∈ triEdges t, (∀ z ∈ Z, z ∉ e) → e ∈ cover

/-- `Z` is reducible if it admits a reduction certificate. -/
def IsReducible (Z : Finset V) : Prop :=
  Z.Nonempty ∧ Nonempty (ReductionCertificate G Z)

/-- Residual graph `(G - X) - Z`. -/
noncomputable def residual (X : Finset (Sym2 V)) (Z : Finset V) : SimpleGraph {v // v ∉ Z} :=
  (G.deleteEdges X).induce {v | v ∉ Z}

/-- **Lemma 2.1 (Reduction bridge)** [Puleo, Lemma 2.2].
If `Z` is reducible via `(S, X)` and the residual satisfies Tuza's inequality,
then so does `G`.

Proof sketch (paper): take a maximum packing `P` and minimum cover `Y` in the residual;
`P ∪ S` packs in `G`, `X ∪ Y` covers `G`, and `|X| + |Y| ≤ 2|S| + 2|P| ≤ 2ν(G)`. -/
theorem reduction_bridge (Z : Finset V) (cert : ReductionCertificate G Z)
    (hres : ∀ [DecidableRel (residual G cert.cover Z).Adj],
        coverNumber (residual G cert.cover Z) ≤
          2 * packingNumber (residual G cert.cover Z)) :
    coverNumber G ≤ 2 * packingNumber G := by
  sorry

end Tuza
