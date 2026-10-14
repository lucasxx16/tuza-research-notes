import Mathlib

/-!
# Triangle packing / transversal numbers and the seven-regular equality example

Formalizes Theorem 1.4 (first assertion) of Y. Xu, "A structural proof for codegree four
and seven-regular equality examples in Tuza's conjecture": `K₄ □ K₅` is a connected
7-regular graph on 20 vertices with `ν = 13`, `τ = 26`.
-/

open Finset

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three edges of a (vertex-)triangle `t`. -/
def triEdges (t : Finset V) : Finset (Sym2 V) := t.sym2.filter (fun e => ¬ e.IsDiag)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle packing: a set of triangles of `G`, pairwise edge-disjoint. -/
def IsTrianglePacking (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint (triEdges s) (triEdges t)

/-- A triangle transversal (cover): a set of edges of `G` meeting every triangle. -/
def IsTriangleCover (X : Finset (Sym2 V)) : Prop :=
  X ⊆ G.edgeFinset ∧ ∀ t ∈ G.cliqueFinset 3, ¬ Disjoint X (triEdges t)

/-- Triangle packing number `ν(G)`. -/
noncomputable def packingNumber : ℕ :=
  sSup {n | ∃ P, IsTrianglePacking G P ∧ P.card = n}

/-- Triangle transversal number `τ(G)`. -/
noncomputable def coverNumber : ℕ :=
  sInf {n | ∃ X, IsTriangleCover G X ∧ X.card = n}

/-- Codegree of two vertices: number of common neighbours. -/
def codegree (u v : V) : ℕ := (G.neighborFinset u ∩ G.neighborFinset v).card

lemma packingNumber_eq {n : ℕ} (hle : ∀ P, IsTrianglePacking G P → P.card ≤ n)
    (P₀ : Finset (Finset V)) (h₀ : IsTrianglePacking G P₀) (hc : P₀.card = n) :
    packingNumber G = n := by
  apply le_antisymm
  · exact csSup_le ⟨_, P₀, h₀, rfl⟩ (by rintro _ ⟨P, hP, rfl⟩; exact hle P hP)
  · exact le_csSup ⟨n, by rintro _ ⟨P, hP, rfl⟩; exact hle P hP⟩ ⟨P₀, h₀, hc⟩

lemma coverNumber_eq {n : ℕ} (hge : ∀ X, IsTriangleCover G X → n ≤ X.card)
    (X₀ : Finset (Sym2 V)) (h₀ : IsTriangleCover G X₀) (hc : X₀.card = n) :
    coverNumber G = n := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨X₀, h₀, hc⟩
  · exact le_csInf ⟨_, X₀, h₀, rfl⟩ (by rintro _ ⟨X, hX, rfl⟩; exact hge X hX)

end Tuza
