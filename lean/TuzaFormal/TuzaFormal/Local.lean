import TuzaFormal.Basic

/-! Local facts about `K₅` and `K₄`: `ν(K₅) ≤ 2`, `τ(K₅) ≥ 4`, `ν(K₄) ≤ 1`, `τ(K₄) ≥ 2`.
Finite checks are on triples / pairs / single edges only (no subset enumeration). -/

open Finset

namespace Tuza

lemma small3 {β : Type*} [DecidableEq β] (Y : Finset β) (hne : Y.Nonempty) (h : Y.card ≤ 3) :
    ∃ x ∈ Y, ∃ y ∈ Y, ∃ z ∈ Y, Y ⊆ {x, y, z} := by
  have hp := hne.card_pos
  have : Y.card = 1 ∨ Y.card = 2 ∨ Y.card = 3 := by omega
  rcases this with h1 | h2 | h3
  · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
    exact ⟨x, by simp, x, by simp, x, by simp, fun w hw => by simp at hw ⊢; tauto⟩
  · obtain ⟨x, y, _, rfl⟩ := card_eq_two.1 h2
    exact ⟨x, by simp, y, by simp, y, by simp, fun w hw => by simp at hw ⊢; tauto⟩
  · obtain ⟨x, y, z, _, _, _, rfl⟩ := card_eq_three.1 h3
    exact ⟨x, by simp, y, by simp, z, by simp, le_rfl⟩

theorem k5pack3 : ∀ a ∈ (univ : Finset (Fin 5)).powersetCard 3,
    ∀ b ∈ (univ : Finset (Fin 5)).powersetCard 3, ∀ c ∈ (univ : Finset (Fin 5)).powersetCard 3,
    a ≠ b → a ≠ c → b ≠ c → (triEdges a ∩ triEdges b).Nonempty ∨
      (triEdges a ∩ triEdges c).Nonempty ∨ (triEdges b ∩ triEdges c).Nonempty := by
  native_decide

theorem k4pack2 : ∀ a ∈ (univ : Finset (Fin 4)).powersetCard 3,
    ∀ b ∈ (univ : Finset (Fin 4)).powersetCard 3, a ≠ b → (triEdges a ∩ triEdges b).Nonempty := by
  native_decide

theorem k5cover3 : ∀ x ∈ triEdges (univ : Finset (Fin 5)), ∀ y ∈ triEdges (univ : Finset (Fin 5)),
    ∀ z ∈ triEdges (univ : Finset (Fin 5)), ∃ t ∈ (univ : Finset (Fin 5)).powersetCard 3,
      x ∉ triEdges t ∧ y ∉ triEdges t ∧ z ∉ triEdges t := by
  native_decide

theorem k4cover1 : ∀ x ∈ triEdges (univ : Finset (Fin 4)),
    ∃ t ∈ (univ : Finset (Fin 4)).powersetCard 3, x ∉ triEdges t := by
  native_decide

theorem k5pack : ∀ S ⊆ (univ : Finset (Fin 5)).powersetCard 3,
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) → S.card ≤ 2 := by
  intro S hS hP
  by_contra h
  rw [not_le] at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.1 h
  rcases k5pack3 a (hS ha) b (hS hb) c (hS hc) hab hac hbc with h | h | h
  · rw [hP a ha b hb hab] at h; exact not_nonempty_empty h
  · rw [hP a ha c hc hac] at h; exact not_nonempty_empty h
  · rw [hP b hb c hc hbc] at h; exact not_nonempty_empty h

theorem k4pack : ∀ S ⊆ (univ : Finset (Fin 4)).powersetCard 3,
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) → S.card ≤ 1 := by
  intro S hS hP
  by_contra h
  rw [not_le] at h
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h
  have := k4pack2 a (hS ha) b (hS hb) hab
  rw [hP a ha b hb hab] at this; exact not_nonempty_empty this

theorem k5cover : ∀ Y ⊆ triEdges (univ : Finset (Fin 5)),
    (∀ t ∈ (univ : Finset (Fin 5)).powersetCard 3, (Y ∩ triEdges t).Nonempty) → 4 ≤ Y.card := by
  intro Y hY hC
  by_contra h
  rw [not_le] at h
  have hne : Y.Nonempty := by
    obtain ⟨e, he⟩ := hC {0, 1, 2} (by decide)
    exact ⟨e, (mem_inter.1 he).1⟩
  obtain ⟨x, hx, y, hy, z, hz, hsub⟩ := small3 Y hne (by omega)
  obtain ⟨t, ht, h1, h2, h3⟩ := k5cover3 x (hY hx) y (hY hy) z (hY hz)
  obtain ⟨e, he⟩ := hC t ht
  have hm := hsub (mem_inter.1 he).1
  have he2 := (mem_inter.1 he).2
  simp only [mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact h1 he2
  · exact h2 he2
  · exact h3 he2

theorem k4cover : ∀ Y ⊆ triEdges (univ : Finset (Fin 4)),
    (∀ t ∈ (univ : Finset (Fin 4)).powersetCard 3, (Y ∩ triEdges t).Nonempty) → 2 ≤ Y.card := by
  intro Y hY hC
  by_contra h
  rw [not_le] at h
  have hne : Y.Nonempty := by
    obtain ⟨e, he⟩ := hC {0, 1, 2} (by decide)
    exact ⟨e, (mem_inter.1 he).1⟩
  obtain ⟨x, rfl⟩ := card_eq_one.1 (show Y.card = 1 by have := hne.card_pos; omega)
  obtain ⟨t, ht, h1⟩ := k4cover1 x (hY (mem_singleton_self x))
  obtain ⟨e, he⟩ := hC t ht
  have hm := (mem_inter.1 he).1
  rw [mem_singleton] at hm
  subst hm
  exact h1 (mem_inter.1 he).2

end Tuza
