import TuzaFormal.Transfer

/-!
# Proposition 8.1 (Cartesian additivity), in full generality

For arbitrary finite simple graphs `F` on `U` and `J` on `W` (Mathlib's `F □ J`):
`ν(F □ J) = |W| ν(F) + |U| ν(J)` and `τ(F □ J) = |W| τ(F) + |U| τ(J)`.

The proof follows the paper: every triangle lies in a single factor fiber, distinct fibers share
at most one vertex (hence no edge), so packings and covers decompose fiberwise.
It is organised as an abstract *fiber decomposition* theorem plus a transfer lemma for
induced embedded copies.
-/

open Finset

namespace Tuza.Product

section General
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma packings_bdd : BddAbove {n | ∃ P, IsTrianglePacking G P ∧ P.card = n} :=
  ⟨(G.cliqueFinset 3).card, by rintro _ ⟨P, hP, rfl⟩; exact card_le_card hP.1⟩

lemma le_packingNumber {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    P.card ≤ packingNumber G :=
  le_csSup (packings_bdd G) ⟨P, hP, rfl⟩

lemma exists_max_packing : ∃ P, IsTrianglePacking G P ∧ P.card = packingNumber G :=
  Nat.sSup_mem (s := {n | ∃ P, IsTrianglePacking G P ∧ P.card = n})
    ⟨0, ∅, ⟨empty_subset _, by simp⟩, rfl⟩ (packings_bdd G)

lemma triEdges_sub_edgeFinset {t : Finset V} (ht : t ∈ G.cliqueFinset 3) :
    triEdges t ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
  simp only [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
    Sym2.mk_isDiag_iff] at he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (SimpleGraph.mem_cliqueFinset_iff.1 ht).1 (mem_coe.2 he.1.1) (mem_coe.2 he.1.2) he.2

lemma triEdges_nonempty {t : Finset V} (ht : t ∈ G.cliqueFinset 3) : (triEdges t).Nonempty := by
  obtain ⟨a, b, c, hab, -, -, rfl⟩ :=
    SimpleGraph.is3Clique_iff.1 (SimpleGraph.mem_cliqueFinset_iff.1 ht)
  exact ⟨s(a, b), by simp [triEdges, G.ne_of_adj hab]⟩

lemma edgeFinset_cover : IsTriangleCover G G.edgeFinset :=
  ⟨subset_rfl, fun t ht h => by
    obtain ⟨e, he⟩ := triEdges_nonempty G ht
    exact disjoint_left.1 h (triEdges_sub_edgeFinset G ht he) he⟩

lemma coverNumber_le {X : Finset (Sym2 V)} (hX : IsTriangleCover G X) :
    coverNumber G ≤ X.card := Nat.sInf_le ⟨X, hX, rfl⟩

lemma exists_min_cover : ∃ X, IsTriangleCover G X ∧ X.card = coverNumber G :=
  Nat.sInf_mem (s := {n | ∃ X, IsTriangleCover G X ∧ X.card = n})
    ⟨_, _, edgeFinset_cover G, rfl⟩

lemma packing_mono {P Q : Finset (Finset V)} (h : Q ⊆ P) (hP : IsTrianglePacking G P) :
    IsTrianglePacking G Q :=
  ⟨h.trans hP.1, fun s hs t ht hst => hP.2 s (h hs) t (h ht) hst⟩

/-! ### Abstract fiber decomposition -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Finset V)

/-- A family of vertex sets ("fibers") such that distinct fibers share at most one vertex and
every triangle of `G` lies inside some fiber. -/
structure FiberDecomp : Prop where
  inter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1
  tri : ∀ t ∈ G.cliqueFinset 3, ∃ i, t ⊆ S i

variable {G S}

lemma edge_fiber_unique (hD : FiberDecomp G S) {e : Sym2 V} (he : ¬ e.IsDiag) {i j : ι}
    (hi : e ∈ (S i).sym2) (hj : e ∈ (S j).sym2) : i = j := by
  by_contra hij
  have h1 := hD.inter i j hij
  induction e using Sym2.ind with
  | _ x y =>
  rw [Sym2.mk_isDiag_iff] at he
  rw [mem_sym2_iff] at hi hj
  have hsub : ({x, y} : Finset V) ⊆ S i ∩ S j := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_inter.2 ⟨hi _ (Sym2.mem_mk_left _ _), hj _ (Sym2.mem_mk_left _ _)⟩
    · exact mem_inter.2 ⟨hi _ (Sym2.mem_mk_right _ _), hj _ (Sym2.mem_mk_right _ _)⟩
  have := card_le_card hsub
  rw [card_pair he] at this
  omega

lemma tri_fiber_unique (hD : FiberDecomp G S) {t : Finset V} (ht : t.card = 3) {i j : ι}
    (hi : t ⊆ S i) (hj : t ⊆ S j) : i = j := by
  by_contra hij
  have := card_le_card (subset_inter hi hj)
  have := hD.inter i j hij
  omega

lemma triEdges_sub_sym2 {t A : Finset V} (h : t ⊆ A) : triEdges t ⊆ A.sym2 :=
  fun _ he => Finset.sym2_mono h (mem_filter.1 he).1

/-- **Fiber decomposition for `ν`.** -/
theorem nu_of_decomp (hD : FiberDecomp G S) (n : ι → ℕ)
    (hup : ∀ i Q, IsTrianglePacking G Q → (∀ s ∈ Q, s ⊆ S i) → Q.card ≤ n i)
    (hex : ∀ i, ∃ Q, IsTrianglePacking G Q ∧ (∀ s ∈ Q, s ⊆ S i) ∧ Q.card = n i) :
    packingNumber G = ∑ i, n i := by
  choose Q hQp hQs hQc using hex
  apply packingNumber_eq G (P₀ := univ.biUnion Q)
  · intro P hP
    have hsub : P ⊆ univ.biUnion (fun i => P.filter (· ⊆ S i)) := by
      intro s hs
      obtain ⟨i, hi⟩ := hD.tri s (hP.1 hs)
      exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨hs, hi⟩⟩
    calc P.card ≤ _ := card_le_card hsub
      _ ≤ ∑ i, (P.filter (· ⊆ S i)).card := card_biUnion_le
      _ ≤ ∑ i, n i := sum_le_sum fun i _ =>
          hup i _ (packing_mono G (filter_subset _ _) hP) (fun s hs => (mem_filter.1 hs).2)
  · refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
    · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hs
      exact (hQp i).1 hi
    · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hs
      obtain ⟨j, -, hj⟩ := mem_biUnion.1 ht
      by_cases hij : i = j
      · subst hij; exact (hQp i).2 s hi t hj hst
      · rw [disjoint_left]
        intro e h1 h2
        exact hij (edge_fiber_unique hD (mem_filter.1 h1).2
          (triEdges_sub_sym2 (hQs i s hi) h1) (triEdges_sub_sym2 (hQs j t hj) h2))
  · rw [card_biUnion]
    · exact sum_congr rfl fun i _ => hQc i
    · intro i _ j _ hij
      rw [Function.onFun, disjoint_left]
      intro s hi hj
      have hc := (SimpleGraph.mem_cliqueFinset_iff.1 ((hQp i).1 hi)).card_eq
      exact hij (tri_fiber_unique hD hc (hQs i s hi) (hQs j s hj))

/-- **Fiber decomposition for `τ`.** -/
theorem tau_of_decomp (hD : FiberDecomp G S) (m : ι → ℕ)
    (hlow : ∀ i X, X ⊆ G.edgeFinset →
      (∀ t ∈ G.cliqueFinset 3, t ⊆ S i → ¬ Disjoint X (triEdges t)) →
      m i ≤ (X.filter (· ∈ (S i).sym2)).card)
    (hex : ∀ i, ∃ Y, Y ⊆ G.edgeFinset ∧
      (∀ t ∈ G.cliqueFinset 3, t ⊆ S i → ¬ Disjoint Y (triEdges t)) ∧ Y.card ≤ m i) :
    coverNumber G = ∑ i, m i := by
  choose Y hYe hYc hYm using hex
  apply le_antisymm
  · calc coverNumber G ≤ (univ.biUnion Y).card := by
          refine coverNumber_le G ⟨biUnion_subset.2 fun i _ => hYe i, fun t ht h => ?_⟩
          obtain ⟨i, hi⟩ := hD.tri t ht
          exact hYc i t ht hi (disjoint_of_subset_left (subset_biUnion_of_mem Y (mem_univ i)) h)
      _ ≤ ∑ i, (Y i).card := card_biUnion_le
      _ ≤ ∑ i, m i := sum_le_sum fun i _ => hYm i
  · obtain ⟨X, hX, hXc⟩ := exists_min_cover G
    rw [← hXc]
    calc ∑ i, m i ≤ ∑ i, (X.filter (· ∈ (S i).sym2)).card :=
          sum_le_sum fun i _ => hlow i X hX.1 fun t ht _ => hX.2 t ht
      _ = (univ.biUnion fun i => X.filter (· ∈ (S i).sym2)).card := by
          rw [card_biUnion]
          intro i _ j _ hij
          rw [Function.onFun, disjoint_left]
          intro e h1 h2
          have hne : ¬ e.IsDiag :=
            SimpleGraph.not_isDiag_of_mem_edgeSet G
              (SimpleGraph.mem_edgeFinset.1 (hX.1 (mem_filter.1 h1).1))
          exact hij (edge_fiber_unique hD hne (mem_filter.1 h1).2 (mem_filter.1 h2).2)
      _ ≤ X.card := card_le_card (biUnion_subset.2 fun i _ => filter_subset _ _)

end General

/-! ### Induced embedded copies -/

section Embed
set_option linter.unusedSectionVars false
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {H : SimpleGraph α} [DecidableRel H.Adj] {G : SimpleGraph β} [DecidableRel G.Adj]
  (f : α ↪ β) (hf : ∀ x y, G.Adj (f x) (f y) ↔ H.Adj x y)
lemma sym2Map_mem_sym2 (e : Sym2 α) : f.sym2Map e ∈ (univ.map f).sym2 := by
  rw [mem_sym2_iff]
  intro a ha
  simp only [Function.Embedding.sym2Map_apply, Sym2.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  exact mem_map_of_mem f (mem_univ b)

include hf

lemma clique_map_iff (t : Finset α) :
    t.map f ∈ G.cliqueFinset 3 ↔ t ∈ H.cliqueFinset 3 := by
  simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, card_map,
    SimpleGraph.isClique_iff, Set.Pairwise, coe_map, Set.mem_image, mem_coe]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨fun x hx y hy hxy => (hf x y).1 (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (f.injective.ne hxy)), hc⟩
  · rintro ⟨h, hc⟩
    refine ⟨?_, hc⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact (hf x y).2 (h hx hy (fun e => hxy (e ▸ rfl)))

lemma embed_pack_le (Q : Finset (Finset β)) (hQ : IsTrianglePacking G Q)
    (hS : ∀ s ∈ Q, s ⊆ univ.map f) : Q.card ≤ packingNumber H := by
  set g := (mapEmbedding f).toEmbedding
  set P := (univ : Finset (Finset α)).filter (fun t => g t ∈ Q)
  have hsub : Q ⊆ P.map g := by
    intro s hs
    obtain ⟨u, -, rfl⟩ := subset_map_iff.1 (hS s hs)
    exact mem_map.2 ⟨u, mem_filter.2 ⟨mem_univ _, hs⟩, rfl⟩
  refine (card_le_card hsub).trans ?_
  rw [card_map]
  apply le_packingNumber
  refine ⟨fun t ht => ?_, fun s hs t ht hst => ?_⟩
  · have := hQ.1 (mem_filter.1 ht).2
    simp only [g, RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at this
    exact (clique_map_iff f hf t).1 this
  · have h1 := hQ.2 (g s) (mem_filter.1 hs).2 (g t) (mem_filter.1 ht).2
      (fun h => hst (g.injective h))
    simp only [g, RelEmbedding.coe_toEmbedding, mapEmbedding_apply, triEdges_map,
      disjoint_map] at h1
    exact h1

lemma embed_pack_ex : ∃ Q, IsTrianglePacking G Q ∧ (∀ s ∈ Q, s ⊆ univ.map f) ∧
    Q.card = packingNumber H := by
  obtain ⟨P, hP, hc⟩ := exists_max_packing H
  set g := (mapEmbedding f).toEmbedding
  refine ⟨P.map g, ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩, fun s hs => ?_, by rw [card_map, hc]⟩
  · obtain ⟨u, hu, rfl⟩ := mem_map.1 hs
    exact (clique_map_iff f hf u).2 (hP.1 hu)
  · obtain ⟨u, hu, rfl⟩ := mem_map.1 hs
    obtain ⟨v, hv, rfl⟩ := mem_map.1 ht
    have := hP.2 u hu v hv (fun h => hst (h ▸ rfl))
    simp only [g, RelEmbedding.coe_toEmbedding, mapEmbedding_apply, triEdges_map,
      disjoint_map]
    exact this
  · obtain ⟨u, -, rfl⟩ := mem_map.1 hs
    exact map_subset_map.2 (subset_univ u)

lemma embed_cover_le (X : Finset (Sym2 β)) (hX : X ⊆ G.edgeFinset)
    (hC : ∀ t ∈ G.cliqueFinset 3, t ⊆ univ.map f → ¬ Disjoint X (triEdges t)) :
    coverNumber H ≤ (X.filter (· ∈ (univ.map f).sym2)).card := by
  set Y := H.edgeFinset.filter (fun e => f.sym2Map e ∈ X)
  have hY : IsTriangleCover H Y := by
    refine ⟨filter_subset _ _, fun t ht hd => ?_⟩
    have := hC (t.map f) ((clique_map_iff f hf t).2 ht) (map_subset_map.2 (subset_univ t))
    obtain ⟨e, heX, het⟩ := not_disjoint_iff.1 this
    rw [triEdges_map] at het
    obtain ⟨e', he', rfl⟩ := mem_map.1 het
    exact disjoint_left.1 hd
      (mem_filter.2 ⟨triEdges_sub_edgeFinset H ht he', heX⟩) he'
  refine (coverNumber_le H hY).trans ?_
  rw [← card_map f.sym2Map]
  apply card_le_card
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.1 he
  exact mem_filter.2 ⟨(mem_filter.1 he').2, sym2Map_mem_sym2 f e'⟩

lemma embed_cover_ex : ∃ Y, Y ⊆ G.edgeFinset ∧
    (∀ t ∈ G.cliqueFinset 3, t ⊆ univ.map f → ¬ Disjoint Y (triEdges t)) ∧
    Y.card ≤ coverNumber H := by
  obtain ⟨X, hX, hc⟩ := exists_min_cover H
  refine ⟨X.map f.sym2Map, fun e he => ?_, fun t ht hts hd => ?_, by rw [card_map, hc]⟩
  · obtain ⟨e', he', rfl⟩ := mem_map.1 he
    have := hX.1 he'
    induction e' using Sym2.ind with
    | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Function.Embedding.sym2Map_apply, Sym2.map_mk] at this ⊢
    exact (hf a b).2 this
  · obtain ⟨u, -, rfl⟩ := subset_map_iff.1 hts
    have hu := (clique_map_iff f hf u).1 ht
    obtain ⟨e, heX, heu⟩ := not_disjoint_iff.1 (hX.2 u hu)
    rw [triEdges_map] at hd
    exact disjoint_left.1 hd (mem_map_of_mem _ heX) (mem_map_of_mem _ heu)

end Embed

/-! ### The Cartesian product -/

section Box
set_option linter.unusedSectionVars false
variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
  (F : SimpleGraph U) (J : SimpleGraph W) [DecidableRel F.Adj] [DecidableRel J.Adj]

/-- `u ↦ (u, w)`: the `F`-fiber over `w`. -/
def rowE (w : W) : U ↪ U × W := ⟨fun u => (u, w), fun _ _ h => (Prod.ext_iff.1 h).1⟩
/-- `w ↦ (u, w)`: the `J`-fiber over `u`. -/
def colE (u : U) : W ↪ U × W := ⟨fun w => (u, w), fun _ _ h => (Prod.ext_iff.1 h).2⟩

@[simp] lemma rowE_apply (w : W) (u : U) : rowE w u = (u, w) := rfl
@[simp] lemma colE_apply (u : U) (w : W) : colE u w = (u, w) := rfl

instance boxDec : DecidableRel (F □ J).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.boxProd_adj.symm

/-- Fibers of `F □ J`, indexed by `W ⊕ U`. -/
def fib : W ⊕ U → Finset (U × W)
  | .inl w => univ.map (rowE w)
  | .inr u => univ.map (colE u)

lemma mem_fib_inl {w : W} {x : U × W} : x ∈ fib (.inl w) ↔ x.2 = w := by
  simp only [fib, mem_map, mem_univ, true_and, rowE, Function.Embedding.coeFn_mk]
  exact ⟨by rintro ⟨u, rfl⟩; rfl, fun h => ⟨x.1, by subst h; rfl⟩⟩

lemma mem_fib_inr {u : U} {x : U × W} : x ∈ fib (.inr u) ↔ x.1 = u := by
  simp only [fib, mem_map, mem_univ, true_and, colE, Function.Embedding.coeFn_mk]
  exact ⟨by rintro ⟨w, rfl⟩; rfl, fun h => ⟨x.2, by subst h; rfl⟩⟩

theorem box_decomp : FiberDecomp (F □ J) (fib (U := U) (W := W)) := by
  constructor
  · intro i j hij
    apply card_le_one.2
    intro a ha b hb
    rw [mem_inter] at ha hb
    rcases i with w | u <;> rcases j with w' | u' <;>
      simp only [mem_fib_inl, mem_fib_inr] at ha hb
    · exact absurd (ha.1.symm.trans ha.2) (fun h => hij (by rw [h]))
    · exact Prod.ext (ha.2.trans hb.2.symm) (ha.1.trans hb.1.symm)
    · exact Prod.ext (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm)
    · exact absurd (ha.1.symm.trans ha.2) (fun h => hij (by rw [h]))
  · intro t ht
    have hc := (SimpleGraph.mem_cliqueFinset_iff).1 ht
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hc
    simp only [SimpleGraph.boxProd_adj] at hab hac hbc
    rcases hab with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases hac with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · subst h3
      refine ⟨.inl a2, ?_⟩
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact mem_fib_inl.2 rfl
    · subst h3
      rcases hbc with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> subst h5 <;> simp_all
    · subst h3
      rcases hbc with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> subst h5 <;> simp_all
    · subst h3
      refine ⟨.inr a1, ?_⟩
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact mem_fib_inr.2 rfl

lemma rowE_adj (w : W) (x y : U) : (F □ J).Adj (rowE w x) (rowE w y) ↔ F.Adj x y := by
  simp [SimpleGraph.boxProd_adj]

lemma colE_adj (u : U) (x y : W) : (F □ J).Adj (colE u x) (colE u y) ↔ J.Adj x y := by
  simp [SimpleGraph.boxProd_adj]

/-- **Proposition 8.1, packing part.** -/
theorem nu_boxProd :
    packingNumber (F □ J) = Fintype.card W * packingNumber F + Fintype.card U * packingNumber J := by
  rw [nu_of_decomp (box_decomp F J) (fun i => Sum.elim (fun _ => packingNumber F)
      (fun _ => packingNumber J) i)]
  · simp [Fintype.sum_sum_type]
  · rintro (w | u) Q hQ hS
    · exact embed_pack_le (rowE w) (rowE_adj F J w) Q hQ hS
    · exact embed_pack_le (colE u) (colE_adj F J u) Q hQ hS
  · rintro (w | u)
    · exact embed_pack_ex (rowE w) (rowE_adj F J w)
    · exact embed_pack_ex (colE u) (colE_adj F J u)

/-- **Proposition 8.1, cover part.** -/
theorem tau_boxProd :
    coverNumber (F □ J) = Fintype.card W * coverNumber F + Fintype.card U * coverNumber J := by
  rw [tau_of_decomp (box_decomp F J) (fun i => Sum.elim (fun _ => coverNumber F)
      (fun _ => coverNumber J) i)]
  · simp [Fintype.sum_sum_type]
  · rintro (w | u) X hX hC
    · exact embed_cover_le (rowE w) (rowE_adj F J w) X hX hC
    · exact embed_cover_le (colE u) (colE_adj F J u) X hX hC
  · rintro (w | u)
    · exact embed_cover_ex (rowE w) (rowE_adj F J w)
    · exact embed_cover_ex (colE u) (colE_adj F J u)

/-- **Proposition 8.1** (Cartesian additivity). -/
theorem prop_8_1 :
    packingNumber (F □ J) = Fintype.card W * packingNumber F + Fintype.card U * packingNumber J ∧
    coverNumber (F □ J) = Fintype.card W * coverNumber F + Fintype.card U * coverNumber J :=
  ⟨nu_boxProd F J, tau_boxProd F J⟩

end Box

end Tuza.Product
