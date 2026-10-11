import TuzaFormal.CodegreeFour
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Sym.Sym2.Order

/-!
# Generic reduction certificates on ten labels

A certificate for `{u, v}` in a hub configuration is described on `Fin 10`
(`0 = u, 1 = v, 2..5 = C, 6,7 = A, 8,9 = B`) by a packing `P`, a cover `X`, the non-spoke
edges it needs (`pres`) and the non-edges it needs (`abs`). The purely finite conditions
(`CertSpec.Ok`) are checked by `decide`; `reducible_of_spec` transfers them to `G` along an
injective labelling. This replaces the hand-written coverage proofs of earlier certificates.
-/

open Finset SimpleGraph

namespace Tuza.CodegreeFour

open MatchingCore

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Rim vertices of the two hubs. -/
def N10 (h : Fin 10) : Finset (Fin 10) :=
  if h = 0 then {1, 2, 3, 4, 5, 6, 7} else {0, 2, 3, 4, 5, 8, 9}

def spokes10 : Finset (Sym2 (Fin 10)) :=
  (N10 0).image (fun i => s(0, i)) ∪ (N10 1).image (fun i => s(1, i))

structure CertSpec where
  P : Finset (Finset (Fin 10))
  X : Finset (Sym2 (Fin 10))
  pres : Finset (Sym2 (Fin 10))
  abs : Finset (Sym2 (Fin 10))

/-- The finite conditions making a `CertSpec` a valid certificate. -/
def CertSpec.Ok (s : CertSpec) : Prop :=
  (∀ t ∈ s.P, t.card = 3 ∧ ∀ e ∈ triEdges t, e ∈ s.pres ∪ spokes10) ∧
  (∀ σ ∈ s.P, ∀ τ ∈ s.P, σ ≠ τ → (σ ∩ τ).card ≤ 1) ∧
  (∀ e ∈ s.X, e ∈ s.pres ∪ spokes10) ∧
  s.X.card ≤ 2 * s.P.card ∧
  (∀ t ∈ s.P, ∀ e ∈ triEdges (t \ {0, 1}), e ∈ s.X) ∧
  (∀ h ∈ ({0, 1} : Finset (Fin 10)), ∀ i ∈ N10 h, ∀ j ∈ N10 h, i ≠ j →
    s(i, j) ∉ s.abs → (s(h, i) ∈ s.X ∨ s(h, j) ∈ s.X ∨ s(i, j) ∈ s.X))

instance (s : CertSpec) : Decidable s.Ok := by
  unfold CertSpec.Ok
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_))))
  all_goals infer_instance

omit [Fintype V] in
lemma mem_triEdges_pair {α : Type*} [DecidableEq α] {t : Finset α} {a b : α} :
    s(a, b) ∈ triEdges t ↔ a ∈ t ∧ b ∈ t ∧ a ≠ b := by
  simp [triEdges, Sym2.mk_isDiag_iff, and_assoc]

omit [Fintype V] in
lemma triEdges_image {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (t : Finset α) :
    triEdges (t.image f) = (triEdges t).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · intro hmem
      obtain ⟨ha, hb, hab⟩ := mem_triEdges_pair.1 hmem
      obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
      exact mem_image.2 ⟨s(i, j), mem_triEdges_pair.2 ⟨hi, hj, fun h => hab (h ▸ rfl)⟩, rfl⟩
    · intro hmem
      obtain ⟨e0, he0, hmap⟩ := mem_image.1 hmem
      rw [mem_triEdges_pair]
      induction e0 using Sym2.ind with
      | _ i j =>
        rw [mem_triEdges_pair] at he0
        rw [Sym2.map_mk, Sym2.eq_iff] at hmap
        rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨mem_image_of_mem _ he0.1, mem_image_of_mem _ he0.2.1,
            fun h => he0.2.2 (hf h)⟩
        · exact ⟨mem_image_of_mem _ he0.2.1, mem_image_of_mem _ he0.1,
            fun h => he0.2.2 (hf h).symm⟩

/-- Labelled hub data: `f` is injective, sends `0, 1` to the hubs and `N10 h` onto `N(hub)`. -/
structure Labelling (H : HubConfig G) (f : Fin 10 → V) : Prop where
  inj : Function.Injective f
  f0 : f 0 = H.u
  f1 : f 1 = H.v
  nu : G.neighborFinset H.u = (N10 0).image f
  nv : G.neighborFinset H.v = (N10 1).image f

lemma Labelling.spoke {H : HubConfig G} {f : Fin 10 → V} (L : Labelling G H f)
    {e : Sym2 (Fin 10)} (he : e ∈ spokes10) : Sym2.map f e ∈ G.edgeFinset := by
  rw [spokes10, mem_union, mem_image, mem_image] at he
  rcases he with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have : f i ∈ G.neighborFinset H.u := by rw [L.nu]; exact mem_image_of_mem _ hi
    rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet, L.f0]
    exact (G.mem_neighborFinset _ _).1 this
  · have : f i ∈ G.neighborFinset H.v := by rw [L.nv]; exact mem_image_of_mem _ hi
    rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet, L.f1]
    exact (G.mem_neighborFinset _ _).1 this

/-- **Generic certificate transfer.** -/
theorem reducible_of_spec (H : HubConfig G) (f : Fin 10 → V) (L : Labelling G H f)
    (s : CertSpec) (hok : s.Ok)
    (hpres : ∀ e ∈ s.pres, Sym2.map f e ∈ G.edgeFinset)
    (habs : ∀ e ∈ s.abs, Sym2.map f e ∉ G.edgeFinset) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨hP, hpair, hXk, hsize, hext, hcov⟩ := hok
  have hknown : ∀ e ∈ s.pres ∪ spokes10, Sym2.map f e ∈ G.edgeFinset := by
    intro e he
    rcases mem_union.1 he with h | h
    · exact hpres e h
    · exact L.spoke G h
  have hinjT : Function.Injective (fun t : Finset (Fin 10) => t.image f) :=
    Finset.image_injective L.inj
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective L.inj
  refine ⟨Finset.insert_nonempty _ _, ⟨{
    packing := s.P.image (fun t => t.image f)
    cover := s.X.image (Sym2.map f)
    isPacking := ?_
    cover_edges := ?_
    size := ?_
    coversZ := ?_
    external := ?_ }⟩⟩
  · refine ⟨?_, ?_⟩
    · intro T hT
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hT
      obtain ⟨h3, hedges⟩ := hP t ht
      rw [mem_cliqueFinset_iff, isNClique_iff]
      refine ⟨?_, by rw [card_image_of_injective _ L.inj, h3]⟩
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
      have hij : i ≠ j := fun h => hab (h ▸ rfl)
      have := hknown _ (hedges _ (mem_triEdges_pair.2 ⟨hi, hj, hij⟩))
      rwa [Sym2.map_mk, mem_edgeFinset, mem_edgeSet] at this
    · intro S hS T hT hST
      obtain ⟨σ, hσ, rfl⟩ := mem_image.1 hS
      obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hT
      have hne : σ ≠ τ := fun h => hST (h ▸ rfl)
      rw [triEdges_image L.inj, triEdges_image L.inj]
      rw [Finset.disjoint_left]
      intro e he1 he2
      obtain ⟨e1, he1', rfl⟩ := mem_image.1 he1
      obtain ⟨e2, he2', heq⟩ := mem_image.1 he2
      have h12 := hinjE heq
      rw [h12] at he2'
      induction e1 using Sym2.ind with
      | _ i j =>
        obtain ⟨hi, hj, hij⟩ := mem_triEdges_pair.1 he1'
        obtain ⟨hi', hj', -⟩ := mem_triEdges_pair.1 he2'
        have h2 : 2 ≤ (σ ∩ τ).card := by
          have hsub : ({i, j} : Finset (Fin 10)) ⊆ σ ∩ τ := by
            intro k hk; simp only [mem_insert, mem_singleton] at hk
            rcases hk with rfl | rfl
            · exact mem_inter.2 ⟨hi, hi'⟩
            · exact mem_inter.2 ⟨hj, hj'⟩
          calc 2 = ({i, j} : Finset (Fin 10)).card := (card_pair hij).symm
            _ ≤ _ := card_le_card hsub
        have := hpair σ hσ τ hτ hne
        omega
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := mem_image.1 he
    exact hknown e0 (hXk e0 he0)
  · rw [card_image_of_injective _ hinjE, card_image_of_injective _ hinjT]; exact hsize
  · intro t ht hZ
    obtain ⟨hub, hhub, hhubt⟩ := hZ
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    obtain ⟨hidx, hhidx, hhubf, hNhub⟩ : ∃ h ∈ ({0, 1} : Finset (Fin 10)), f h = hub ∧
        G.neighborFinset hub = (N10 h).image f := by
      simp only [mem_insert, mem_singleton] at hhub
      rcases hhub with rfl | rfl
      · exact ⟨0, by simp, L.f0, L.nu⟩
      · exact ⟨1, by simp, L.f1, L.nv⟩
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hN.card_eq]
    obtain ⟨a, b, hab, hab_eq⟩ := card_eq_two.1 herase
    have ha : a ∈ t.erase hub := by rw [hab_eq]; simp
    have hb : b ∈ t.erase hub := by rw [hab_eq]; simp
    have hadj : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → G.Adj x y := fun x hx y hy hxy => hN.isClique hx hy hxy
    have haN : a ∈ G.neighborFinset hub :=
      (G.mem_neighborFinset _ _).2 (hadj _ hhubt _ (mem_erase.1 ha).2 (mem_erase.1 ha).1.symm)
    have hbN : b ∈ G.neighborFinset hub :=
      (G.mem_neighborFinset _ _).2 (hadj _ hhubt _ (mem_erase.1 hb).2 (mem_erase.1 hb).1.symm)
    rw [hNhub] at haN hbN
    obtain ⟨i, hi, rfl⟩ := mem_image.1 haN
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hbN
    have hij : i ≠ j := fun h => hab (h ▸ rfl)
    have hfij : G.Adj (f i) (f j) := hadj _ (mem_erase.1 ha).2 _ (mem_erase.1 hb).2 hab
    have hnabs : s(i, j) ∉ s.abs := by
      intro h
      apply habs _ h
      rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet]; exact hfij
    have hmem : ∀ x y : Fin 10, x ≠ y → f x ∈ t → f y ∈ t → s(x, y) ∈ s.X →
        ¬ Disjoint (s.X.image (Sym2.map f)) (triEdges t) := by
      intro x y hxy hx hy hX hdis
      refine Finset.disjoint_left.1 hdis (mem_image_of_mem _ hX) ?_
      rw [Sym2.map_mk, mem_triEdges_pair]
      exact ⟨hx, hy, fun h => hxy (L.inj h)⟩
    have hti := (mem_erase.1 ha).2
    have htj := (mem_erase.1 hb).2
    have hfh : f hidx ∈ t := hhubf ▸ hhubt
    have hhi : hidx ≠ i := fun h => (mem_erase.1 ha).1 (by rw [← hhubf, h])
    have hhj : hidx ≠ j := fun h => (mem_erase.1 hb).1 (by rw [← hhubf, h])
    rcases hcov hidx hhidx i hi j hj hij hnabs with h | h | h
    · exact hmem _ _ hhi hfh hti h
    · exact hmem _ _ hhj hfh htj h
    · exact hmem _ _ hij hti htj h
  · intro T hT e he hZ
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hT
    rw [triEdges_image L.inj] at he
    obtain ⟨e0, he0, rfl⟩ := mem_image.1 he
    refine mem_image_of_mem _ (hext t ht e0 ?_)
    have h0 : (0 : Fin 10) ∉ e0 := fun h0 =>
      hZ H.u (by simp) (by rw [← L.f0]; exact Sym2.mem_map.2 ⟨0, h0, rfl⟩)
    have h1 : (1 : Fin 10) ∉ e0 := fun h1 =>
      hZ H.v (by simp) (by rw [← L.f1]; exact Sym2.mem_map.2 ⟨1, h1, rfl⟩)
    induction e0 using Sym2.ind with
    | _ i j =>
      obtain ⟨hi, hj, hij⟩ := mem_triEdges_pair.1 he0
      have hi0 : i ≠ 0 := fun e => h0 (by rw [← e]; exact Sym2.mem_mk_left _ _)
      have hi1 : i ≠ 1 := fun e => h1 (by rw [← e]; exact Sym2.mem_mk_left _ _)
      have hj0 : j ≠ 0 := fun e => h0 (by rw [← e]; exact Sym2.mem_mk_right _ _)
      have hj1 : j ≠ 1 := fun e => h1 (by rw [← e]; exact Sym2.mem_mk_right _ _)
      exact mem_triEdges_pair.2 ⟨by simp [hi, hi0, hi1], by simp [hj, hj0, hj1], hij⟩

section Labels
variable (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
@[simp] lemma lab0 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 0 = u := rfl
@[simp] lemma lab1 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 1 = v := rfl
@[simp] lemma lab2 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 2 = c0 := rfl
@[simp] lemma lab3 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 3 = c1 := rfl
@[simp] lemma lab4 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 4 = c2 := rfl
@[simp] lemma lab5 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 5 = c3 := rfl
@[simp] lemma lab6 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 6 = a0 := rfl
@[simp] lemma lab7 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 7 = a1 := rfl
@[simp] lemma lab8 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 8 = b0 := rfl
@[simp] lemma lab9 : labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 9 = b1 := rfl
end Labels

lemma labelling_nu (H : HubConfig G) {c0 c1 c2 c3 a0 a1 b0 b1 : V}
    (hC : H.C = {c0, c1, c2, c3}) (hA : H.A = {a0, a1}) :
    G.neighborFinset H.u = (N10 0).image (labels10 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1) := by
  have hN : N10 0 = {1, 2, 3, 4, 5, 6, 7} := rfl
  rw [H.hNu, hC, hA, hN]
  simp only [image_insert, image_singleton, lab1, lab2, lab3, lab4, lab5, lab6, lab7]
  ext w; simp only [mem_insert, mem_union, mem_singleton]; tauto

lemma labelling_nv (H : HubConfig G) {c0 c1 c2 c3 a0 a1 b0 b1 : V}
    (hC : H.C = {c0, c1, c2, c3}) (hB : H.B = {b0, b1}) :
    G.neighborFinset H.v = (N10 1).image (labels10 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1) := by
  have hN : N10 1 = {0, 2, 3, 4, 5, 8, 9} := rfl
  rw [H.hNv, hC, hB, hN]
  simp only [image_insert, image_singleton, lab0, lab2, lab3, lab4, lab5, lab8, lab9]
  ext w; simp only [mem_insert, mem_union, mem_singleton]; tauto

lemma labelling_of_hub (H : HubConfig G) {c0 c1 c2 c3 a0 a1 b0 b1 : V}
    (hC : H.C = {c0, c1, c2, c3}) (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (h10 : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10) :
    Labelling G H (labels10 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1) :=
  ⟨labels10_injective _ _ _ _ _ _ _ _ _ _ h10, rfl, rfl,
    labelling_nu G H hC hA, labelling_nv G H hC hB⟩

/-- Test: certificate D1 re-derived through the generic checker. -/
def specD1 : CertSpec where
  P := {{0, 1, 5}, {0, 3, 4}, {0, 2, 6}, {1, 3, 8}, {1, 4, 2}}
  X := {s(3, 4), s(2, 6), s(3, 8), s(4, 2), s(0, 1), s(0, 5), s(0, 7), s(1, 5), s(1, 8), s(1, 9)}
  pres := {s(3, 4), s(2, 6), s(3, 8), s(2, 4)}
  abs := {s(2, 3), s(3, 6), s(4, 6)}

lemma specD1_ok : specD1.Ok := by decide +kernel

end Tuza.CodegreeFour
