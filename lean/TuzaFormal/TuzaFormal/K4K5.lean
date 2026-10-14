import TuzaFormal.Transfer
import TuzaFormal.Local

/-! # `K₄ □ K₅`: ν = 13, τ = 26 (Theorem 1.4, first assertion). -/

open Finset

namespace Tuza.K4K5

abbrev V := Fin 4 × Fin 5

/-- `K₄ □ K₅`: distinct vertices adjacent iff they agree in exactly one coordinate. -/
def G : SimpleGraph V where
  Adj a b := (a.1 = b.1 ∧ a.2 ≠ b.2) ∨ (a.2 = b.2 ∧ a.1 ≠ b.1)
  symm := ⟨fun a b h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inr ⟨h1.symm, Ne.symm h2⟩⟩
  loopless := ⟨fun a h => by rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h rfl⟩

instance : DecidableRel G.Adj := fun a b => by unfold G; infer_instance

theorem card_V : Fintype.card V = 20 := by rfl

theorem regular : G.IsRegularOfDegree 7 := by
  intro v; rw [← SimpleGraph.card_neighborFinset_eq_degree]; revert v; decide +kernel

theorem card_edges : G.edgeFinset.card = 70 := by decide +kernel

theorem connected : G.Connected := by
  have key : ∀ a b : V, G.Reachable a b := by
    intro a b
    have h1 : G.Reachable a (a.1, b.2) := by
      by_cases h : a.2 = b.2
      · obtain ⟨x, y⟩ := a; simp only at h; subst h; rfl
      · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, h⟩)
    have h2 : G.Reachable (a.1, b.2) b := by
      by_cases h : a.1 = b.1
      · obtain ⟨x, y⟩ := b; simp only at h; subst h; rfl
      · exact SimpleGraph.Adj.reachable (Or.inr ⟨rfl, h⟩)
    exact h1.trans h2
  exact ⟨key⟩



/-- Fibers: `inl i` is the row `{i} × Fin 5` (a `K₅`), `inr j` the column `Fin 4 × {j}` (a `K₄`). -/
def fiberVerts : Fin 4 ⊕ Fin 5 → Finset V
  | .inl i => univ.filter (·.1 = i)
  | .inr j => univ.filter (·.2 = j)

def fiberTris (k : Fin 4 ⊕ Fin 5) : Finset (Finset V) := (fiberVerts k).powersetCard 3

def fiberEdges (k : Fin 4 ⊕ Fin 5) : Finset (Sym2 V) := triEdges (fiberVerts k)


def rowEmb (i : Fin 4) : Fin 5 ↪ V := ⟨fun j => (i, j), fun _ _ h => (Prod.ext_iff.1 h).2⟩
def colEmb (j : Fin 5) : Fin 4 ↪ V := ⟨fun i => (i, j), fun _ _ h => (Prod.ext_iff.1 h).1⟩

theorem rowEmb_apply (i : Fin 4) (j : Fin 5) : rowEmb i j = (i, j) := rfl
theorem colEmb_apply (j : Fin 5) (i : Fin 4) : colEmb j i = (i, j) := rfl

theorem fiberVerts_inl (i : Fin 4) : fiberVerts (.inl i) = univ.map (rowEmb i) := by
  ext ⟨a, b⟩
  simp only [fiberVerts, mem_filter, mem_univ, true_and]
  rw [mem_map]
  constructor
  · rintro rfl; exact ⟨b, mem_univ _, rfl⟩
  · rintro ⟨w, -, h⟩; exact (Prod.ext_iff.1 h).1.symm

theorem fiberVerts_inr (j : Fin 5) : fiberVerts (.inr j) = univ.map (colEmb j) := by
  ext ⟨a, b⟩
  simp only [fiberVerts, mem_filter, mem_univ, true_and]
  rw [mem_map]
  constructor
  · rintro rfl; exact ⟨a, mem_univ _, rfl⟩
  · rintro ⟨w, -, h⟩; exact (Prod.ext_iff.1 h).2.symm

/-- Every fiber 3-set is a triangle (fibers are complete). -/
theorem fiberTris_clique (k) {t : Finset V} (ht : t ∈ fiberTris k) : t ∈ G.cliqueFinset 3 := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 ht
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  have hx' := hsub (mem_coe.1 hx)
  have hy' := hsub (mem_coe.1 hy)
  rcases k with i | j
  · simp only [fiberVerts, mem_filter, mem_univ, true_and] at hx' hy'
    exact Or.inl ⟨hx'.trans hy'.symm, fun h => hxy (Prod.ext (hx'.trans hy'.symm) h)⟩
  · simp only [fiberVerts, mem_filter, mem_univ, true_and] at hx' hy'
    exact Or.inr ⟨hx'.trans hy'.symm, fun h => hxy (Prod.ext h (hx'.trans hy'.symm))⟩

theorem adj3 : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c →
    (a.1 = b.1 ∧ a.1 = c.1) ∨ (a.2 = b.2 ∧ a.2 = c.2) := by decide +kernel

/-- Every triangle lies in a single fiber. -/
theorem tri_in_fiber (t : Finset V) (ht : t ∈ G.cliqueFinset 3) : ∃ k, t ∈ fiberTris k := by
  have hc := (SimpleGraph.mem_cliqueFinset_iff).1 ht
  have h3 := hc.card_eq
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hc
  rcases adj3 a b c hab hac hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨.inl a.1, mem_powersetCard.2 ⟨?_, h3⟩⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [fiberVerts, mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · exact h2.symm
  · refine ⟨.inr a.2, mem_powersetCard.2 ⟨?_, h3⟩⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [fiberVerts, mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · exact h2.symm

theorem every_edge_in_fiber_triangle :
    ∀ e ∈ G.edgeFinset, ∃ k, ∃ t ∈ fiberTris k, e ∈ triEdges t := by decide +kernel

theorem every_edge_in_triangle :
    ∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e ∈ triEdges t := by
  intro e he
  obtain ⟨k, t, ht, het⟩ := every_edge_in_fiber_triangle e he
  exact ⟨t, fiberTris_clique k ht, het⟩

end Tuza.K4K5
