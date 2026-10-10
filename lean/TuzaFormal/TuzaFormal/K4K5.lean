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
  intro v; rw [← SimpleGraph.card_neighborFinset_eq_degree]; revert v; native_decide

theorem card_edges : G.edgeFinset.card = 70 := by native_decide

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

def nuBound : Fin 4 ⊕ Fin 5 → ℕ | .inl _ => 2 | .inr _ => 1
def tauBound : Fin 4 ⊕ Fin 5 → ℕ | .inl _ => 4 | .inr _ => 2

def rowEmb (i : Fin 4) : Fin 5 ↪ V := ⟨fun j => (i, j), fun _ _ h => (Prod.ext_iff.1 h).2⟩
def colEmb (j : Fin 5) : Fin 4 ↪ V := ⟨fun i => (i, j), fun _ _ h => (Prod.ext_iff.1 h).1⟩

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
    (a.1 = b.1 ∧ a.1 = c.1) ∨ (a.2 = b.2 ∧ a.2 = c.2) := by native_decide

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
    ∀ e ∈ G.edgeFinset, ∃ k, ∃ t ∈ fiberTris k, e ∈ triEdges t := by native_decide

theorem every_edge_in_triangle :
    ∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e ∈ triEdges t := by
  intro e he
  obtain ⟨k, t, ht, het⟩ := every_edge_in_fiber_triangle e he
  exact ⟨t, fiberTris_clique k ht, het⟩

theorem fiberTris_disj' : ∀ k l, k ≠ l → fiberTris k ∩ fiberTris l = ∅ := by native_decide

theorem fiberTris_disj (k l) (h : k ≠ l) : Disjoint (fiberTris k) (fiberTris l) :=
  Finset.disjoint_iff_inter_eq_empty.2 (fiberTris_disj' k l h)

theorem fiberEdges_disj : ∀ k l, k ≠ l → Disjoint (fiberEdges k) (fiberEdges l) := by
  intro k l hkl
  rw [Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
  simp only [fiberEdges, triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff,
    forall_eq_or_imp, forall_eq, Sym2.mk_isDiag_iff] at he he'
  obtain ⟨⟨ha, hb⟩, hab⟩ := he
  obtain ⟨⟨ha', hb'⟩, -⟩ := he'
  apply hab
  rcases k with i | j <;> rcases l with i' | j' <;>
    simp only [fiberVerts, mem_filter, mem_univ, true_and] at ha hb ha' hb'
  · exact absurd (congrArg Sum.inl (ha.symm.trans ha')) hkl
  · exact Prod.ext (ha.trans hb.symm) (ha'.trans hb'.symm)
  · exact Prod.ext (ha'.trans hb'.symm) (ha.trans hb.symm)
  · exact absurd (congrArg Sum.inr (ha.symm.trans ha')) hkl

theorem triEdges_sub (k) (t) (ht : t ∈ fiberTris k) : triEdges t ⊆ fiberEdges k :=
  triEdges_mono (mem_powersetCard.1 ht).1

/-- Local packing bound in a fiber, transferred from `K₅`/`K₄`. -/
theorem fiber_pack (k) (S : Finset (Finset V)) (hS : S ⊆ fiberTris k)
    (hP : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) : S.card ≤ nuBound k := by
  rcases k with i | j
  · rw [fiberTris, fiberVerts_inl] at hS; exact pack_transfer _ _ _ k5pack S hS hP
  · rw [fiberTris, fiberVerts_inr] at hS; exact pack_transfer _ _ _ k4pack S hS hP

/-- Local cover bound in a fiber, transferred from `K₅`/`K₄`. -/
theorem fiber_cover (k) (Y : Finset (Sym2 V)) (hY : Y ⊆ fiberEdges k)
    (hC : ∀ t ∈ fiberTris k, (Y ∩ triEdges t).Nonempty) : tauBound k ≤ Y.card := by
  rcases k with i | j
  · rw [fiberEdges, fiberVerts_inl] at hY; rw [fiberTris, fiberVerts_inl] at hC
    exact cover_transfer _ _ _ k5cover Y hY hC
  · rw [fiberEdges, fiberVerts_inr] at hY; rw [fiberTris, fiberVerts_inr] at hC
    exact cover_transfer _ _ _ k4cover Y hY hC

theorem sum_nu : ∑ k, nuBound k = 13 := by rfl
theorem sum_tau : ∑ k, tauBound k = 26 := by rfl

/-- The explicit 13-triangle packing from §8.3 (0-indexed). -/
def P₀ : Finset (Finset V) :=
  (univ.image fun j : Fin 5 => ({(0, j), (1, j), (2, j)} : Finset V)) ∪
  (univ.image fun i : Fin 4 => ({(i, 0), (i, 1), (i, 2)} : Finset V)) ∪
  (univ.image fun i : Fin 4 => ({(i, 0), (i, 3), (i, 4)} : Finset V))

/-- The explicit 26-edge cover from §8.3 (0-indexed). -/
def X₀ : Finset (Sym2 V) :=
  (univ.biUnion fun j : Fin 5 => ({s((0, j), (1, j)), s((2, j), (3, j))} : Finset (Sym2 V))) ∪
  (univ.biUnion fun i : Fin 4 =>
    ({s((i, 0), (i, 1)), s((i, 2), (i, 3)), s((i, 2), (i, 4)), s((i, 3), (i, 4))} :
      Finset (Sym2 V)))

theorem P₀_fib : ∀ t ∈ P₀, ∃ k, t ∈ fiberTris k := by native_decide
theorem P₀_disj : ∀ s ∈ P₀, ∀ t ∈ P₀, s ≠ t → triEdges s ∩ triEdges t = ∅ := by native_decide
theorem P₀_card : P₀.card = 13 := by native_decide

theorem P₀_packing : IsTrianglePacking G P₀ := by
  refine ⟨fun t ht => ?_, fun s hs t ht h => ?_⟩
  · obtain ⟨k, hk⟩ := P₀_fib t ht; exact fiberTris_clique k hk
  · exact Finset.disjoint_iff_inter_eq_empty.2 (P₀_disj s hs t ht h)

theorem X₀_edges : X₀ ⊆ G.edgeFinset := by native_decide
theorem X₀_fib : ∀ k, ∀ t ∈ fiberTris k, (X₀ ∩ triEdges t).Nonempty := by native_decide
theorem X₀_card : X₀.card = 26 := by native_decide

theorem X₀_cover : IsTriangleCover G X₀ := by
  refine ⟨X₀_edges, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := tri_in_fiber t ht
  exact Finset.not_disjoint_iff_nonempty_inter.2 (X₀_fib k t hk)

theorem packing_le (P : Finset (Finset V)) (hP : IsTrianglePacking G P) : P.card ≤ 13 := by
  have hsub : P ⊆ univ.biUnion fiberTris := by
    intro t ht
    obtain ⟨k, hk⟩ := tri_in_fiber t (hP.1 ht)
    exact mem_biUnion.2 ⟨k, mem_univ _, hk⟩
  calc P.card = (univ.biUnion fun k => P ∩ fiberTris k).card := by
        congr 1; ext t; simp only [mem_biUnion, mem_inter, mem_univ, true_and]
        exact ⟨fun h => (mem_biUnion.1 (hsub h)).elim fun k hk => ⟨k, h, hk.2⟩,
          fun ⟨_, h, _⟩ => h⟩
    _ = ∑ k, (P ∩ fiberTris k).card := by
        rw [card_biUnion]; intro k _ l _ h
        exact (fiberTris_disj k l h).mono inter_subset_right inter_subset_right
    _ ≤ ∑ k, nuBound k := by
        apply sum_le_sum; intro k _
        apply fiber_pack k _ inter_subset_right
        intro s hs t ht hst
        exact Finset.disjoint_iff_inter_eq_empty.1
          (hP.2 s (mem_inter.1 hs).1 t (mem_inter.1 ht).1 hst)
    _ = 13 := sum_nu

theorem cover_ge (X : Finset (Sym2 V)) (hX : IsTriangleCover G X) : 26 ≤ X.card := by
  calc 26 = ∑ k, tauBound k := sum_tau.symm
    _ ≤ ∑ k, (X ∩ fiberEdges k).card := by
        apply sum_le_sum; intro k _
        apply fiber_cover k _ inter_subset_right
        intro t ht
        obtain ⟨e, he⟩ := Finset.not_disjoint_iff_nonempty_inter.1
          (hX.2 t (fiberTris_clique k ht))
        obtain ⟨he1, he2⟩ := mem_inter.1 he
        exact ⟨e, mem_inter.2 ⟨mem_inter.2 ⟨he1, triEdges_sub k t ht he2⟩, he2⟩⟩
    _ = (univ.biUnion fun k => X ∩ fiberEdges k).card := by
        rw [card_biUnion]; intro k _ l _ h
        exact (fiberEdges_disj k l h).mono inter_subset_right inter_subset_right
    _ ≤ X.card := card_le_card (biUnion_subset.2 fun _ _ => inter_subset_left)

theorem packingNumber_eq_13 : packingNumber G = 13 :=
  packingNumber_eq G packing_le P₀ P₀_packing P₀_card

theorem coverNumber_eq_26 : coverNumber G = 26 :=
  coverNumber_eq G cover_ge X₀ X₀_cover X₀_card

/-- Theorem 1.4 (first assertion): `K₄ □ K₅` is a connected 7-regular graph on 20 vertices
and 70 edges, every edge lies in a triangle, `ν = 13`, `τ = 26 = 2ν`. -/
theorem main : G.Connected ∧ G.IsRegularOfDegree 7 ∧ Fintype.card V = 20 ∧
    G.edgeFinset.card = 70 ∧ (∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e ∈ triEdges t) ∧
    packingNumber G = 13 ∧ coverNumber G = 26 ∧ coverNumber G = 2 * packingNumber G := by
  refine ⟨connected, regular, card_V, card_edges, every_edge_in_triangle,
    packingNumber_eq_13, coverNumber_eq_26, ?_⟩
  rw [packingNumber_eq_13, coverNumber_eq_26]

end Tuza.K4K5
