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

/-- Column and row embeddings into `Fin 4 × W`. -/
def colEmb (w : W) : Fin 4 ↪ Fin 4 × W := ⟨fun i => (i, w), fun _ _ h => (Prod.ext_iff.1 h).1⟩
def rowEmb (i : Fin 4) : W ↪ Fin 4 × W := ⟨fun w => (i, w), fun _ _ h => (Prod.ext_iff.1 h).2⟩

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

/-! `infinite_family` (Prop 8.3) is stated in `ProductExamples.lean`, where its `ν`/`τ` parts
are derived from Prop 8.1. -/

end Tuza.Family
