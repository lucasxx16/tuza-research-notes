import TuzaFormal.CodegreeFour

/-!
# Sanity check: the (A1) connectivity hypotheses are satisfiable

Guard against the earlier bug where `A1` used `(linkGraph G u).Connected` on all of `V`,
which is unsatisfiable for any hub configuration (the hub is isolated in its own link).
Here we build a concrete `HubConfig` on `Fin 10` and prove that both hub links are
`LinkConnected`. (The non-WKE conjuncts of (A1) are not checked here.)
-/

open Finset SimpleGraph

namespace Tuza.CodegreeFour.Sanity

/-- u = 0, v = 1, C = {2,3,4,5}, A = {6,7}, B = {8,9}; extra edges 6–2, 7–2, 8–2, 9–2. -/
def E (a b : Fin 10) : Bool :=
  (a = 0 ∧ b ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset (Fin 10))) ∨
  (a = 1 ∧ b ∈ ({2, 3, 4, 5, 8, 9} : Finset (Fin 10))) ∨
  (a = 2 ∧ b ∈ ({6, 7, 8, 9} : Finset (Fin 10)))

def G0 : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun a b => E a b = true

instance : DecidableRel G0.Adj := fun a b => by unfold G0; infer_instance

def H0 : HubConfig G0 where
  u := 0
  v := 1
  huv := by decide
  C := {2, 3, 4, 5}
  A := {6, 7}
  B := {8, 9}
  hC := by decide
  hCcard := by decide
  hNu := by decide
  hNv := by decide
  hA := by decide
  hB := by decide
  hAdisj := by decide
  hBdisj := by decide
  hABdisj := by decide
  hvA := by decide
  huB := by decide
  hdu := by decide
  hdv := by decide

private lemma reach_two (z : Fin 10) (a : Fin 10)
    (h : ∀ a ∈ G0.neighborFinset z, (linkGraph G0 z).Adj a 2 ∨ a = 2 ∨
      ∃ m, (linkGraph G0 z).Adj a m ∧ (linkGraph G0 z).Adj m 2)
    (ha : a ∈ G0.neighborFinset z) : (linkGraph G0 z).Reachable a 2 := by
  rcases h a ha with h | rfl | ⟨m, h1, h2⟩
  · exact h.reachable
  · rfl
  · exact h1.reachable.trans h2.reachable

private lemma linkConnected_of (z : Fin 10)
    (h : ∀ a ∈ G0.neighborFinset z, (linkGraph G0 z).Adj a 2 ∨ a = 2 ∨
      ∃ m, (linkGraph G0 z).Adj a m ∧ (linkGraph G0 z).Adj m 2) :
    LinkConnected G0 z := fun a ha b hb =>
  (reach_two z a h ha).trans (reach_two z b h hb).symm

theorem H0_u_linkConnected : LinkConnected G0 H0.u :=
  linkConnected_of 0 (by decide)

theorem H0_v_linkConnected : LinkConnected G0 H0.v :=
  linkConnected_of 1 (by decide)

/-- The hypotheses no longer force `|V| = 7`: here `|V| = 10`. -/
example : Fintype.card (Fin 10) = 10 ∧ LinkConnected G0 H0.u ∧ LinkConnected G0 H0.v :=
  ⟨rfl, H0_u_linkConnected, H0_v_linkConnected⟩

end Tuza.CodegreeFour.Sanity

/-! ## Full (A1) and (A2) are satisfiable

Concrete configuration (`u = 0`, `v = 1`, `C = {2,3,4,5}`, `A = {6,7}`, `B = {8,9}`):
core edges `23, 24`; A-side `26, 36, 37, 47, 56, 67`; B-side `28, 38, 39, 49, 58, 89`.
Both links are connected and **not WKE**, and the budget (A2) holds, so the hypotheses
of `structural_codegree_four` are non-vacuous. Non-WKE is reduced (`wke_small`) to a finite
search over matchings of size ≤ 3 and `Q ⊆ N(z)`, then checked by `decide +kernel`. -/

namespace Tuza.CodegreeFour.Sanity

/-- A WKE witness for a link on `≤ 7` vertices can be taken with `|M| ≤ 3`, `Q ⊆ N(z)`. -/
lemma wke_small {W : Type*} [Fintype W] [DecidableEq W] (F : SimpleGraph W)
    [DecidableRel F.Adj] (z : W) (h7 : (F.neighborFinset z).card ≤ 7)
    (h : IsWKE (linkGraph F z)) :
    ∃ M ∈ (Finset.range 4).biUnion (fun k => (linkGraph F z).edgeFinset.powersetCard k),
    ∃ Q ∈ (F.neighborFinset z).powerset, Q.card ≤ M.card ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset) ∧
      ∀ e ∈ (linkGraph F z).edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M := by
  classical
  obtain ⟨M, Q, ⟨hMsub, hMdisj⟩, hQ, hcov⟩ := h
  have hsub2 : ∀ e ∈ M, e.toFinset ⊆ F.neighborFinset z ∧ e.toFinset.card = 2 := by
    intro e he
    have := hMsub he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : (linkGraph F z).Adj a b := (mem_edgeFinset).1 this
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hab.1
        · exact hab.2.1
      · rw [Sym2.toFinset_mk_eq]; exact card_pair (F.ne_of_adj hab.2.2)
  have hcardM : M.card ≤ 3 := by
    have hU : (M.biUnion Sym2.toFinset).card = M.card * 2 := by
      rw [card_biUnion (fun e he f hf hne => hMdisj e he f hf hne)]
      rw [sum_congr rfl (fun e he => (hsub2 e he).2), sum_const, smul_eq_mul]
    have hle : (M.biUnion Sym2.toFinset).card ≤ 7 :=
      (card_le_card (biUnion_subset.2 fun e he => (hsub2 e he).1)).trans h7
    omega
  refine ⟨M, mem_biUnion.2 ⟨M.card, mem_range.2 (by omega), mem_powersetCard.2 ⟨hMsub, rfl⟩⟩,
    Q ∩ F.neighborFinset z, mem_powerset.2 inter_subset_right,
    (card_le_card inter_subset_left).trans hQ, hMdisj, ?_⟩
  intro e he hx
  refine hcov e he (fun x hxe hxQ => ?_)
  have hxN : x ∈ F.neighborFinset z := by
    induction e using Sym2.ind with
    | _ a b =>
      have hab : (linkGraph F z).Adj a b := (mem_edgeFinset).1 he
      rw [Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · exact hab.1
      · exact hab.2.1
  exact hx x hxe (mem_inter.2 ⟨hxQ, hxN⟩)

def E1 (a b : Fin 10) : Bool :=
  (a = 0 ∧ b ∈ ({1, 2, 3, 4, 5, 6, 7} : Finset (Fin 10))) ∨
  (a = 1 ∧ b ∈ ({2, 3, 4, 5, 8, 9} : Finset (Fin 10))) ∨
  (a = 2 ∧ b ∈ ({3, 4, 6, 8} : Finset (Fin 10))) ∨
  (a = 3 ∧ b ∈ ({6, 7, 8, 9} : Finset (Fin 10))) ∨
  (a = 4 ∧ b ∈ ({7, 9} : Finset (Fin 10))) ∨
  (a = 5 ∧ b ∈ ({6, 8} : Finset (Fin 10))) ∨
  (a = 6 ∧ b = 7) ∨ (a = 8 ∧ b = 9)

def G1 : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun a b => E1 a b = true

instance : DecidableRel G1.Adj := fun a b => by unfold G1; infer_instance

def H1 : HubConfig G1 where
  u := 0
  v := 1
  huv := by decide
  C := {2, 3, 4, 5}
  A := {6, 7}
  B := {8, 9}
  hC := by decide
  hCcard := by decide
  hNu := by decide
  hNv := by decide
  hA := by decide
  hB := by decide
  hAdisj := by decide
  hBdisj := by decide
  hABdisj := by decide
  hvA := by decide
  huB := by decide
  hdu := by decide
  hdv := by decide

theorem H1_A2 : H1.A2 := by
  unfold HubConfig.A2 HubConfig.coreDeg; decide

private lemma lc1 (z : Fin 10)
    (h : ∀ a ∈ G1.neighborFinset z, (linkGraph G1 z).Adj a 2 ∨ a = 2 ∨
      ∃ m, (linkGraph G1 z).Adj a m ∧ (linkGraph G1 z).Adj m 2) :
    LinkConnected G1 z := by
  have r : ∀ a ∈ G1.neighborFinset z, (linkGraph G1 z).Reachable a 2 := by
    intro a ha
    rcases h a ha with h | rfl | ⟨m, h1, h2⟩
    · exact h.reachable
    · rfl
    · exact h1.reachable.trans h2.reachable
  exact fun a ha b hb => (r a ha).trans (r b hb).symm

def IsMat1 (M : Finset (Sym2 (Fin 10))) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset
instance (M : Finset (Sym2 (Fin 10))) : Decidable (IsMat1 M) := by
  unfold IsMat1; infer_instance
def Cov1 (z : Fin 10) (M : Finset (Sym2 (Fin 10))) (Q : Finset (Fin 10)) : Prop :=
  ∀ e ∈ (linkGraph G1 z).edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M
instance (z M Q) : Decidable (Cov1 z M Q) := by unfold Cov1; infer_instance
def Good1 (z : Fin 10) (M : Finset (Sym2 (Fin 10))) (Q : Finset (Fin 10)) : Prop :=
  Q.card ≤ M.card ∧ IsMat1 M ∧ Cov1 z M Q
instance (z M Q) : Decidable (Good1 z M Q) := by
  unfold Good1; exact instDecidableAnd
def SmallWKE1 (z : Fin 10) : Prop :=
  ∃ M ∈ (Finset.range 4).biUnion (fun k => (linkGraph G1 z).edgeFinset.powersetCard k),
    ∃ Q ∈ (G1.neighborFinset z).powerset, Good1 z M Q
instance (z) : Decidable (SmallWKE1 z) := by unfold SmallWKE1; infer_instance

private lemma notWKE1 (z : Fin 10) (h7 : (G1.neighborFinset z).card ≤ 7)
    (hdec : ¬ SmallWKE1 z) : ¬ IsWKE (linkGraph G1 z) := fun h => by
  obtain ⟨M, hM, Q, hQ, h1, h2, h3⟩ := wke_small G1 z h7 h
  exact hdec ⟨M, hM, Q, hQ, h1, h2, h3⟩

set_option maxHeartbeats 4000000 in
lemma lcu : LinkConnected G1 0 := lc1 0 (by decide)
set_option maxHeartbeats 4000000 in
lemma lcv : LinkConnected G1 1 := lc1 1 (by decide)
lemma c7u : (G1.neighborFinset 0).card ≤ 7 := by decide
lemma c7v : (G1.neighborFinset 1).card ≤ 7 := by decide
set_option maxHeartbeats 4000000 in
lemma nwu : ¬ SmallWKE1 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
lemma nwv : ¬ SmallWKE1 1 := by decide +kernel

theorem H1_A1 : H1.A1 :=
  ⟨lcu, notWKE1 0 c7u nwu, lcv, notWKE1 1 c7v nwv⟩

/-- The full hypotheses of Theorem 1.3 are satisfiable. -/
example : ∃ (G : SimpleGraph (Fin 10)) (_ : DecidableRel G.Adj) (H : HubConfig G),
    H.A1 ∧ H.A2 := ⟨G1, inferInstance, H1, H1_A1, H1_A2⟩

end Tuza.CodegreeFour.Sanity
