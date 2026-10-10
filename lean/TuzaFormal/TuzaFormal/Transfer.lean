import TuzaFormal.Basic

/-! Transfer of local packing / cover bounds along vertex embeddings. -/

open Finset

namespace Tuza

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma triEdges_map (f : α ↪ β) (t : Finset α) :
    triEdges (t.map f) = (triEdges t).map f.sym2Map := by
  unfold triEdges
  rw [Finset.sym2_map, Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  simp [Function.Embedding.sym2Map, Sym2.isDiag_map f.injective]

lemma triEdges_mono {s t : Finset α} (h : s ⊆ t) : triEdges s ⊆ triEdges t := by
  intro e he
  simp only [triEdges, mem_filter] at he ⊢
  exact ⟨Finset.sym2_mono h he.1, he.2⟩

lemma pack_transfer (f : α ↪ β) (U : Finset α) (n : ℕ)
    (hU : ∀ S ⊆ U.powersetCard 3,
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) → S.card ≤ n)
    (S : Finset (Finset β)) (hS : S ⊆ (U.map f).powersetCard 3)
    (hP : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → triEdges s ∩ triEdges t = ∅) : S.card ≤ n := by
  rw [powersetCard_map] at hS
  set g := (mapEmbedding f).toEmbedding
  set S' := (U.powersetCard 3).filter (fun t => g t ∈ S)
  have hS' : S'.map g = S := by
    ext x
    simp only [mem_map, S', mem_filter]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩; exact ha
    · intro hx
      obtain ⟨a, ha, rfl⟩ := mem_map.1 (hS hx)
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  rw [← hS', card_map]
  apply hU S' (filter_subset _ _)
  intro s hs t ht hst
  have h1 := hP (g s) (mem_filter.1 hs).2 (g t) (mem_filter.1 ht).2 (fun h => hst (g.injective h))
  simp only [g, RelEmbedding.coe_toEmbedding, mapEmbedding_apply, triEdges_map,
    ← map_inter, map_eq_empty] at h1
  exact h1

lemma cover_transfer (f : α ↪ β) (U : Finset α) (n : ℕ)
    (hU : ∀ Y ⊆ triEdges U,
      (∀ t ∈ U.powersetCard 3, (Y ∩ triEdges t).Nonempty) → n ≤ Y.card)
    (Y : Finset (Sym2 β)) (hY : Y ⊆ triEdges (U.map f))
    (hC : ∀ t ∈ (U.map f).powersetCard 3, (Y ∩ triEdges t).Nonempty) : n ≤ Y.card := by
  rw [triEdges_map] at hY
  set h := f.sym2Map
  set Y' := (triEdges U).filter (fun e => h e ∈ Y)
  have hY' : Y'.map h = Y := by
    ext x
    simp only [mem_map, Y', mem_filter]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩; exact ha
    · intro hx
      obtain ⟨a, ha, rfl⟩ := mem_map.1 (hY hx)
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  rw [← hY', card_map]
  apply hU Y' (filter_subset _ _)
  intro t ht
  have htU : t ⊆ U := (mem_powersetCard.1 ht).1
  have ht' : t.map f ∈ (U.map f).powersetCard 3 := by
    rw [mem_powersetCard] at ht ⊢
    exact ⟨map_subset_map.2 ht.1, by rw [card_map]; exact ht.2⟩
  obtain ⟨e, he⟩ := hC _ ht'
  rw [mem_inter, triEdges_map] at he
  obtain ⟨e', he', rfl⟩ := mem_map.1 he.2
  exact ⟨e', mem_inter.2 ⟨mem_filter.2 ⟨triEdges_mono htU he', he.1⟩, he'⟩⟩

end Tuza
