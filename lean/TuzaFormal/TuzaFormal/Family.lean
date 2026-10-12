import TuzaFormal.Transfer
import TuzaFormal.Local

/-!
# Proposition 8.3: `K₄ □ J` for triangle-free regular `J`, and the circulant family

For a finite triangle-free `d`-regular graph `J` on `W`, the product `K₄ □ J` is
`(d+3)`-regular, connected when `J` is, and has `ν = |W|`, `τ = 2|W|`.
With `J = C_n(1,3)` (the circulant on `ZMod n`, `n = 2k`, `k ≥ 4`) this gives connected
7-regular graphs on `8k` vertices and `28k` edges with `τ = 2ν = 4k`.
All proofs are for general `J` / `k`; `decide +kernel` is used only for fixed facts about `K₄`.
-/

open Finset

namespace Tuza.Family

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The Cartesian product `K₄ □ J`. -/
def box (J : SimpleGraph W) : SimpleGraph (Fin 4 × W) where
  Adj a b := (a.1 = b.1 ∧ J.Adj a.2 b.2) ∨ (a.2 = b.2 ∧ a.1 ≠ b.1)
  symm := ⟨fun a b h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, Ne.symm h2⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact J.irrefl h
    · exact h rfl⟩

instance (J : SimpleGraph W) [DecidableRel J.Adj] : DecidableRel (box J).Adj :=
  fun a b => by unfold box; infer_instance

/-- The `K₄`-fiber (column) over `w`. -/
def col (w : W) : Finset (Fin 4 × W) := univ.filter (·.2 = w)
def colTris (w : W) : Finset (Finset (Fin 4 × W)) := (col w).powersetCard 3
def colEdges (w : W) : Finset (Sym2 (Fin 4 × W)) := triEdges (col w)

def colEmb (w : W) : Fin 4 ↪ Fin 4 × W := ⟨fun i => (i, w), fun _ _ h => (Prod.ext_iff.1 h).1⟩
def rowEmb (i : Fin 4) : W ↪ Fin 4 × W := ⟨fun w => (i, w), fun _ _ h => (Prod.ext_iff.1 h).2⟩

theorem col_eq (w : W) : col w = univ.map (colEmb w) := by
  ext ⟨a, b⟩
  simp only [col, mem_filter, mem_univ, true_and]
  rw [mem_map]
  constructor
  · rintro rfl; exact ⟨a, mem_univ _, rfl⟩
  · rintro ⟨v, -, h⟩; exact (Prod.ext_iff.1 h).2.symm

section
variable (J : SimpleGraph W) [DecidableRel J.Adj]

theorem colTris_clique (w : W) {t : Finset (Fin 4 × W)} (ht : t ∈ colTris w) :
    t ∈ (box J).cliqueFinset 3 := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.1 ht
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  have hx' := hsub (mem_coe.1 hx)
  have hy' := hsub (mem_coe.1 hy)
  simp only [col, mem_filter, mem_univ, true_and] at hx' hy'
  exact Or.inr ⟨hx'.trans hy'.symm, fun h => hxy (Prod.ext h (hx'.trans hy'.symm))⟩

/-- Every triangle of `K₄ □ J` lies in a column, when `J` is triangle-free. -/
theorem tri_in_col (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False)
    (t : Finset (Fin 4 × W)) (ht : t ∈ (box J).cliqueFinset 3) : ∃ w, t ∈ colTris w := by
  have hc := (SimpleGraph.mem_cliqueFinset_iff).1 ht
  have hcard := hc.card_eq
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hc
  have key : a.2 = b.2 ∧ a.2 = c.2 := by
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hac with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hbc with ⟨h5, h6⟩ | ⟨h5, h6⟩
    all_goals first
      | exact ⟨h1, h3⟩
      | exact (htf _ _ _ h2 h6 h4).elim
      | exact absurd (h1.symm.trans h3) h6
      | exact absurd (h1.trans h5) h4
      | exact absurd (h3.trans h5.symm) (J.ne_of_adj h2)
      | exact absurd (h3.trans h5.symm) h2
      | exact absurd (h1.trans h5) (J.ne_of_adj h4)
      | exact absurd (h1.symm.trans h3) (J.ne_of_adj h6)
  refine ⟨a.2, mem_powersetCard.2 ⟨?_, hcard⟩⟩
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  simp only [col, mem_filter, mem_univ, true_and]
  rcases hx with rfl | rfl | rfl
  · rfl
  · exact key.1.symm
  · exact key.2.symm

end

theorem colTris_disj {w w' : W} (h : w ≠ w') : Disjoint (colTris w) (colTris w') := by
  rw [disjoint_left]
  intro t h1 h2
  obtain ⟨s1, c1⟩ := mem_powersetCard.1 h1
  obtain ⟨s2, -⟩ := mem_powersetCard.1 h2
  obtain ⟨x, hx⟩ : t.Nonempty := by rw [← card_pos, c1]; norm_num
  have a := s1 hx
  have b := s2 hx
  simp only [col, mem_filter, mem_univ, true_and] at a b
  exact h (a.symm.trans b)

theorem colEdges_disj {w w' : W} (h : w ≠ w') : Disjoint (colEdges w) (colEdges w') := by
  rw [disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
  simp only [colEdges, triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff,
    forall_eq_or_imp, forall_eq] at he he'
  obtain ⟨⟨ha, -⟩, -⟩ := he
  obtain ⟨⟨ha', -⟩, -⟩ := he'
  simp only [col, mem_filter, mem_univ, true_and] at ha ha'
  exact h (ha.symm.trans ha')

theorem colEdges_edges (J : SimpleGraph W) [DecidableRel J.Adj] (w : W) :
    colEdges w ⊆ (box J).edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
  simp only [colEdges, triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff,
    forall_eq_or_imp, forall_eq, Sym2.mk_isDiag_iff] at he
  obtain ⟨⟨ha, hb⟩, hab⟩ := he
  simp only [col, mem_filter, mem_univ, true_and] at ha hb
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact Or.inr ⟨ha.trans hb.symm, fun h => hab (Prod.ext h (ha.trans hb.symm))⟩

theorem col_pack (w : W) (S : Finset (Finset (Fin 4 × W))) (hS : S ⊆ colTris w)
    (hP : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) : S.card ≤ 1 := by
  rw [colTris, col_eq] at hS
  exact pack_transfer _ _ _ k4pack S hS hP

theorem col_cover (w : W) (Y : Finset (Sym2 (Fin 4 × W))) (hY : Y ⊆ colEdges w)
    (hC : ∀ t ∈ colTris w, (Y ∩ triEdges t).Nonempty) : 2 ≤ Y.card := by
  rw [colEdges, col_eq] at hY
  rw [colTris, col_eq] at hC
  exact cover_transfer _ _ _ k4cover Y hY hC

section
variable (J : SimpleGraph W) [DecidableRel J.Adj]
  (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False)
include htf

theorem packing_le (P : Finset (Finset (Fin 4 × W))) (hP : IsTrianglePacking (box J) P) :
    P.card ≤ Fintype.card W := by
  have hsub : P ⊆ univ.biUnion colTris := by
    intro t ht
    obtain ⟨w, hw⟩ := tri_in_col J htf t (hP.1 ht)
    exact mem_biUnion.2 ⟨w, mem_univ _, hw⟩
  calc P.card = (univ.biUnion fun w => P ∩ colTris w).card := by
        congr 1; ext t; simp only [mem_biUnion, mem_inter, mem_univ, true_and]
        exact ⟨fun h => (mem_biUnion.1 (hsub h)).elim fun k hk => ⟨k, h, hk.2⟩,
          fun ⟨_, h, _⟩ => h⟩
    _ = ∑ w, (P ∩ colTris w).card := by
        rw [card_biUnion]; intro k _ l _ h
        exact (colTris_disj h).mono inter_subset_right inter_subset_right
    _ ≤ ∑ _w : W, 1 := by
        apply sum_le_sum; intro w _
        apply col_pack w _ inter_subset_right
        intro s hs t ht hst
        exact Finset.disjoint_iff_inter_eq_empty.1
          (hP.2 s (mem_inter.1 hs).1 t (mem_inter.1 ht).1 hst)
    _ = Fintype.card W := by simp

theorem cover_ge (X : Finset (Sym2 (Fin 4 × W))) (hX : IsTriangleCover (box J) X) :
    2 * Fintype.card W ≤ X.card := by
  calc 2 * Fintype.card W = ∑ _w : W, 2 := by simp [mul_comm]
    _ ≤ ∑ w, (X ∩ colEdges w).card := by
        apply sum_le_sum; intro w _
        apply col_cover w _ inter_subset_right
        intro t ht
        obtain ⟨e, he⟩ := Finset.not_disjoint_iff_nonempty_inter.1
          (hX.2 t (colTris_clique J w ht))
        obtain ⟨he1, he2⟩ := mem_inter.1 he
        exact ⟨e, mem_inter.2 ⟨mem_inter.2 ⟨he1, triEdges_mono (mem_powersetCard.1 ht).1 he2⟩,
          he2⟩⟩
    _ = (univ.biUnion fun w => X ∩ colEdges w).card := by
        rw [card_biUnion]; intro k _ l _ h
        exact (colEdges_disj h).mono inter_subset_right inter_subset_right
    _ ≤ X.card := card_le_card (biUnion_subset.2 fun _ _ => inter_subset_left)

end

/-! Witnesses. -/

def tri0 (w : W) : Finset (Fin 4 × W) := ({0, 1, 2} : Finset (Fin 4)).map (colEmb w)
def cov4 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}

theorem cov4_sub : cov4 ⊆ triEdges (univ : Finset (Fin 4)) := by decide +kernel
theorem cov4_hits : ∀ t ∈ (univ : Finset (Fin 4)).powersetCard 3, (cov4 ∩ triEdges t).Nonempty := by
  decide +kernel
theorem cov4_card : cov4.card = 2 := by decide +kernel

def P₀ : Finset (Finset (Fin 4 × W)) := univ.image tri0
def X₀ : Finset (Sym2 (Fin 4 × W)) := univ.biUnion fun w => cov4.map (colEmb w).sym2Map

theorem tri0_mem (w : W) : tri0 w ∈ colTris w := by
  rw [colTris, col_eq, mem_powersetCard]
  exact ⟨map_subset_map.2 (subset_univ _), by rw [tri0, card_map]; rfl⟩

theorem P₀_card : (P₀ : Finset (Finset (Fin 4 × W))).card = Fintype.card W := by
  rw [P₀, card_image_of_injective, card_univ]
  intro w w' h
  have : (colEmb w) 0 ∈ tri0 w := mem_map_of_mem _ (by decide)
  rw [h] at this
  obtain ⟨i, -, hi⟩ := mem_map.1 this
  exact ((Prod.ext_iff.1 hi).2).symm

theorem P₀_packing (J : SimpleGraph W) [DecidableRel J.Adj] : IsTrianglePacking (box J) P₀ := by
  refine ⟨fun t ht => ?_, fun s hs t ht hst => ?_⟩
  · obtain ⟨w, -, rfl⟩ := mem_image.1 ht
    exact colTris_clique J w (tri0_mem w)
  · obtain ⟨w, -, rfl⟩ := mem_image.1 hs
    obtain ⟨w', -, rfl⟩ := mem_image.1 ht
    have hw : w ≠ w' := fun h => hst (h ▸ rfl)
    exact (colEdges_disj hw).mono (triEdges_mono (mem_powersetCard.1 (tri0_mem w)).1)
      (triEdges_mono (mem_powersetCard.1 (tri0_mem w')).1)

theorem X₀_cover (J : SimpleGraph W) [DecidableRel J.Adj]
    (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False) :
    IsTriangleCover (box J) X₀ := by
  refine ⟨?_, fun t ht => ?_⟩
  · intro e he
    obtain ⟨w, -, hw⟩ := mem_biUnion.1 he
    apply colEdges_edges J w
    rw [colEdges, col_eq, triEdges_map]
    exact map_subset_map.2 cov4_sub hw
  · obtain ⟨w, hw⟩ := tri_in_col J htf t ht
    rw [colTris, col_eq, powersetCard_map] at hw
    obtain ⟨t', ht', rfl⟩ := mem_map.1 hw
    obtain ⟨e, he⟩ := cov4_hits t' ht'
    obtain ⟨he1, he2⟩ := mem_inter.1 he
    apply Finset.not_disjoint_iff_nonempty_inter.2
    refine ⟨(colEmb w).sym2Map e, mem_inter.2 ⟨?_, ?_⟩⟩
    · exact mem_biUnion.2 ⟨w, mem_univ _, mem_map_of_mem _ he1⟩
    · simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, triEdges_map]
      exact mem_map_of_mem _ he2

theorem X₀_card_le : (X₀ : Finset (Sym2 (Fin 4 × W))).card ≤ 2 * Fintype.card W := by
  calc (X₀ : Finset (Sym2 (Fin 4 × W))).card ≤ ∑ w : W, (cov4.map (colEmb w).sym2Map).card :=
        card_biUnion_le
    _ = 2 * Fintype.card W := by simp [cov4_card, mul_comm]

section
variable (J : SimpleGraph W) [DecidableRel J.Adj]
  (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False)
include htf

theorem box_nu : packingNumber (box J) = Fintype.card W :=
  packingNumber_eq _ (packing_le J htf) P₀ (P₀_packing J) P₀_card

theorem box_tau : coverNumber (box J) = 2 * Fintype.card W :=
  coverNumber_eq _ (cover_ge J htf) X₀ (X₀_cover J htf)
    (le_antisymm X₀_card_le (cover_ge J htf X₀ (X₀_cover J htf)))

end

/-! Degree and connectivity. -/

section
variable (J : SimpleGraph W) [DecidableRel J.Adj]

theorem box_neighborFinset (i : Fin 4) (w : W) :
    (box J).neighborFinset (i, w) =
      (univ.erase i).map (colEmb w) ∪ (J.neighborFinset w).map (rowEmb i) := by
  ext ⟨a, b⟩
  rw [SimpleGraph.mem_neighborFinset, mem_union, mem_map, mem_map]
  change ((i = a ∧ J.Adj w b) ∨ (w = b ∧ i ≠ a)) ↔ _
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inr ⟨b, (J.mem_neighborFinset _ _).2 h, rfl⟩
    · exact Or.inl ⟨a, mem_erase.2 ⟨Ne.symm h, mem_univ _⟩, rfl⟩
  · rintro (⟨j, hj, hjx⟩ | ⟨y, hy, hyx⟩)
    · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hjx
      exact Or.inr ⟨h2, fun h => (mem_erase.1 hj).1 (h1.trans h.symm)⟩
    · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hyx
      refine Or.inl ⟨h1, ?_⟩
      have := (J.mem_neighborFinset _ _).1 hy
      rw [← show y = b from h2]; exact this

theorem box_regular (d : ℕ) (hJ : J.IsRegularOfDegree d) :
    (box J).IsRegularOfDegree (d + 3) := by
  rintro ⟨i, w⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, box_neighborFinset,
    card_union_of_disjoint, card_map, card_map, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin, SimpleGraph.card_neighborFinset_eq_degree, hJ w]
  · omega
  · rw [disjoint_left]
    intro x hx hx'
    obtain ⟨j, -, rfl⟩ := mem_map.1 hx
    obtain ⟨y, hy, hyx⟩ := mem_map.1 hx'
    have h2 := (Prod.ext_iff.1 hyx).2
    exact J.ne_of_adj ((J.mem_neighborFinset _ _).1 hy) h2.symm

theorem box_connected [Nonempty W] (hJ : J.Connected) : (box J).Connected := by
  have key : ∀ a b : Fin 4 × W, (box J).Reachable a b := by
    intro a b
    let f : J →g box J := ⟨fun w => (a.1, w), fun h => Or.inl ⟨rfl, h⟩⟩
    have h1 : (box J).Reachable (a.1, a.2) (a.1, b.2) := (hJ.preconnected a.2 b.2).map f
    have h2 : (box J).Reachable (a.1, b.2) b := by
      by_cases h : a.1 = b.1
      · obtain ⟨x, y⟩ := b; simp only at h; subst h; rfl
      · exact SimpleGraph.Adj.reachable (Or.inr ⟨rfl, h⟩)
    exact h1.trans h2
  exact ⟨key⟩

end

/-! The circulant `J_n = C_n(1,3)` on `ZMod n`. -/

def circ (n : ℕ) : SimpleGraph (ZMod n) where
  Adj a b := a ≠ b ∧ (b - a = 1 ∨ b - a = -1 ∨ b - a = 3 ∨ b - a = -3)
  symm := ⟨fun a b h => by
    obtain ⟨hne, h⟩ := h
    refine ⟨hne.symm, ?_⟩
    have e : a - b = -(b - a) := by ring
    rw [e]
    rcases h with h | h | h | h <;> rw [h] <;> simp⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (circ n).Adj := fun a b => by unfold circ; infer_instance

theorem natCast_ne_zero {n k : ℕ} (hk : 0 < k) (hkn : k < n) : (k : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd hk h) (by omega)

theorem circ_triangleFree {n : ℕ} (h2 : 2 ∣ n) :
    ∀ x y z, (circ n).Adj x y → (circ n).Adj y z → (circ n).Adj x z → False := by
  let φ := ZMod.castHom h2 (ZMod 2)
  have par : ∀ x y, (circ n).Adj x y → φ y - φ x = 1 := by
    intro x y h
    rw [← map_sub]
    rcases h.2 with h | h | h | h <;> rw [h] <;> simp only [map_neg, map_one, map_ofNat] <;> decide
  intro x y z hxy hyz hxz
  have h1 := par _ _ hxy
  have h2' := par _ _ hyz
  have h3 := par _ _ hxz
  generalize φ x = p at h1 h3
  generalize φ y = q at h1 h2'
  generalize φ z = r at h2' h3
  revert p q r
  decide

section
variable {n : ℕ} [NeZero n]

def S4 (n : ℕ) : Finset (ZMod n) := {1, -1, 3, -3}

theorem circ_adj_iff (hn : 8 ≤ n) (a b : ZMod n) : (circ n).Adj a b ↔ b - a ∈ S4 n := by
  simp only [S4, mem_insert, mem_singleton]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rw [sub_self] at h
    have n1 : ((1 : ℕ) : ZMod n) ≠ 0 := natCast_ne_zero (by omega) (by omega)
    have n3 : ((3 : ℕ) : ZMod n) ≠ 0 := natCast_ne_zero (by omega) (by omega)
    push_cast at n1 n3
    rcases h with h | h | h | h
    · exact n1 h.symm
    · exact n1 (neg_eq_zero.1 h.symm)
    · exact n3 h.symm
    · exact n3 (neg_eq_zero.1 h.symm)

theorem S4_card (hn : 8 ≤ n) : (S4 n).card = 4 := by
  have ne : ∀ x y : ZMod n, ∀ k : ℕ, 0 < k → k < n → x - y = (k : ZMod n) → x ≠ y := by
    intro x y k hk hkn h hxy
    rw [hxy, sub_self] at h
    exact natCast_ne_zero hk hkn h.symm
  have a1 : (1 : ZMod n) ≠ -1 := ne _ _ 2 (by omega) (by omega) (by push_cast; ring)
  have a2 : (1 : ZMod n) ≠ 3 := fun h => ne _ _ 2 (by omega) (by omega) (by push_cast; ring) h.symm
  have a3 : (1 : ZMod n) ≠ -3 := ne _ _ 4 (by omega) (by omega) (by push_cast; ring)
  have a4 : (-1 : ZMod n) ≠ 3 := fun h => ne _ _ 4 (by omega) (by omega) (by push_cast; ring) h.symm
  have a5 : (-1 : ZMod n) ≠ -3 := ne _ _ 2 (by omega) (by omega) (by push_cast; ring)
  have a6 : (3 : ZMod n) ≠ -3 := ne _ _ 6 (by omega) (by omega) (by push_cast; ring)
  rw [S4, card_insert_of_notMem, card_insert_of_notMem, card_pair a6]
  · simp only [mem_insert, mem_singleton, not_or]; exact ⟨a4, a5⟩
  · simp only [mem_insert, mem_singleton, not_or]; exact ⟨a1, a2, a3⟩

theorem circ_regular (hn : 8 ≤ n) : (circ n).IsRegularOfDegree 4 := by
  intro a
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (circ n).neighborFinset a = (S4 n).image (a + ·) := by
    ext b
    rw [SimpleGraph.mem_neighborFinset, circ_adj_iff hn, mem_image]
    constructor
    · intro h; exact ⟨b - a, h, by ring⟩
    · rintro ⟨s, hs, rfl⟩; simpa using hs
  rw [this, card_image_of_injective _ (add_right_injective a), S4_card hn]

theorem circ_connected (hn : 8 ≤ n) : (circ n).Connected := by
  have step : ∀ k : ℕ, (circ n).Reachable 0 (k : ZMod n) := by
    intro k
    induction k with
    | zero => simpa using SimpleGraph.Reachable.refl (G := circ n) (0 : ZMod n)
    | succ k ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [circ_adj_iff hn]
      simp [S4]
  have : ∀ x : ZMod n, (circ n).Reachable 0 x := by
    intro x; simpa using step x.val
  exact ⟨fun x y => (this x).symm.trans (this y)⟩

end

instance instNZ (m : ℕ) : NeZero (2 * (m + 4)) := ⟨by omega⟩

/-- **Proposition 8.3** (explicit family). For `k = m + 4 ≥ 4`, `G_k = K₄ □ C_{2k}(1,3)` is a
connected 7-regular graph on `8k` vertices with `28k` edges, `ν = 2k` and `τ = 4k = 2ν`. -/
theorem infinite_family (m : ℕ) :
    let k := m + 4
    (box (circ (2 * k))).Connected ∧ (box (circ (2 * k))).IsRegularOfDegree 7 ∧
    Fintype.card (Fin 4 × ZMod (2 * k)) = 8 * k ∧
    (box (circ (2 * k))).edgeFinset.card = 28 * k ∧
    packingNumber (box (circ (2 * k))) = 2 * k ∧
    coverNumber (box (circ (2 * k))) = 4 * k ∧
    coverNumber (box (circ (2 * k))) = 2 * packingNumber (box (circ (2 * k))) := by
  intro k
  have hn : 8 ≤ 2 * k := by omega
  have htf := circ_triangleFree (n := 2 * k) (dvd_mul_right 2 k)
  have hcard : Fintype.card (Fin 4 × ZMod (2 * k)) = 8 * k := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]; ring
  have hreg : (box (circ (2 * k))).IsRegularOfDegree 7 := box_regular _ 4 (circ_regular hn)
  have hW : Fintype.card (ZMod (2 * k)) = 2 * k := ZMod.card _
  refine ⟨box_connected _ (circ_connected hn), hreg, hcard, ?_, ?_, ?_, ?_⟩
  · have hs := (box (circ (2 * k))).sum_degrees_eq_twice_card_edges
    simp only [hreg.degree_eq, sum_const, card_univ, hcard, smul_eq_mul] at hs
    omega
  · rw [box_nu _ htf, hW]
  · rw [box_tau _ htf, hW]; ring
  · rw [box_nu _ htf, box_tau _ htf]

end Tuza.Family
