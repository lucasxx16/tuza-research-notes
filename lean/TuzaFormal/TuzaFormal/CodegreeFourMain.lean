import TuzaFormal.GenericCert

/-!
# Theorem 1.3: remaining denser cores (C₄, paw, K₃+K₁) and the structural theorem
-/

open Finset SimpleGraph

set_option maxHeartbeats 800000

namespace Tuza.CodegreeFour

open MatchingCore

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Proposition 6.3**: C₄ core is reducible under (A1)–(A2). -/
theorem c4_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hpy : G.Adj p y) (hyq : G.Adj y q) (hqx : G.Adj q x)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(x, p) ∨ s(a, b) = s(p, y) ∨ s(a, b) = s(y, q) ∨ s(a, b) = s(q, x)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  sorry

/-- **Proposition 6.4**: paw core is reducible under (A1)–(A2). -/
theorem paw_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {p q r s : V} (hC : H.C = {p, q, r, s})
    (hpq : G.Adj p q) (hpr : G.Adj p r) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(p, q) ∨ s(a, b) = s(p, r) ∨ s(a, b) = s(q, r) ∨ s(a, b) = s(r, s)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  sorry

/-- **Proposition 6.7**: K₃+K₁ core is reducible under (A1)–(A2). -/
theorem k3k1_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {p q r s : V} (hC : H.C = {p, q, r, s})
    (hpq : G.Adj p q) (hpr : G.Adj p r) (hqr : G.Adj q r)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(p, q) ∨ s(a, b) = s(p, r) ∨ s(a, b) = s(q, r)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  sorry

/-- If every core edge is `e0e1`, there is at most one core edge. -/
lemma numCoreEdges_le_one (H : HubConfig G) (e0 e1 : V)
    (h : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y → s(x, y) = s(e0, e1)) :
    H.numCoreEdges ≤ 1 := by
  classical
  unfold HubConfig.numCoreEdges
  calc _ ≤ ({({e0, e1} : Finset V)} : Finset (Finset V)).card := by
        apply card_le_card
        intro e he
        rw [mem_filter, mem_powersetCard] at he
        obtain ⟨⟨hsub, hcard⟩, x, hx, y, hy, hxy, hadj⟩ := he
        have hs := h x (hsub hx) y (hsub hy) hadj
        have hexy : ({x, y} : Finset V) = e :=
          eq_of_subset_of_card_le
            (by intro t ht; simp only [mem_insert, mem_singleton] at ht
                rcases ht with rfl | rfl <;> assumption)
            (by rw [hcard, card_pair hxy])
        rw [mem_singleton, ← hexy]
        rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact pair_comm _ _
    _ = 1 := card_singleton _

theorem structural_codegree_four (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  have hge : 2 ≤ H.numCoreEdges := by
    by_contra hlt
    have : H.numCoreEdges ≤ 1 := by omega
    exact prop31 G H hA1 this
  by_cases h2K2 : ∃ p0 p1 q0 q1 : V,
      H.C = {p0, p1, q0, q1} ∧ G.Adj p0 p1 ∧ G.Adj q0 q1 ∧
      (∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1))
  · obtain ⟨p0, p1, q0, q1, hC, hp, hq, honly⟩ := h2K2
    exact MatchingCore.matching_core_reducible G H hA1 p0 p1 q0 q1 hC ⟨hp, hq⟩ honly
  by_cases hstar : ∃ p q r s : V,
      H.C = {p, q, r, s} ∧ G.Adj p q ∧ G.Adj p r ∧ G.Adj p s ∧
      (∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
  · obtain ⟨p, q, r, s, hC, hpq, hpr, hps, honly⟩ := hstar
    exact star_core_reducible G H hA1.2.1 hA1.2.2.2 p q r s hC ⟨hpq, hpr, hps⟩ honly
  by_cases hpath : ∃ p q r s : V,
      H.C = {p, q, r, s} ∧ G.Adj p q ∧ G.Adj p r ∧
      (∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
  · obtain ⟨p, q, r, s, hC, hpq, hpr, honly⟩ := hpath
    have hpC : p ∈ H.C := by rw [hC]; simp
    exact path_core_reducible G H hA1 p q r s hC ⟨hpq, hpr⟩ honly (hA2 p hpC)
  by_cases hP4 : ∃ p q r s : V,
      H.C = {p, q, r, s} ∧ G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧
      (∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, q) ∨ s(x, y) = s(q, r) ∨ s(x, y) = s(r, s))
  · obtain ⟨p, q, r, s, hC, hpq, hqr, hrs, honly⟩ := hP4
    exact p4_core_reducible G H hA1 hC hpq hqr hrs honly
  by_cases hK4c : ∃ x y z w : V,
      H.C = {x, y, z, w} ∧
      G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w
  · obtain ⟨x, y, z, w, hC, hK4⟩ := hK4c
    exact k4_core_reducible G H hA1 hA2 hC hK4
  by_cases hDiam : ∃ x y p q : V,
      H.C = {x, y, p, q} ∧ G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q ∧
      ¬ G.Adj x y ∧
      (∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
        s(a, b) = s(x, p) ∨ s(a, b) = s(x, q) ∨ s(a, b) = s(y, p) ∨
        s(a, b) = s(y, q) ∨ s(a, b) = s(p, q))
  · obtain ⟨x, y, p, q, hC, hxp, hxq, hyp, hyq, hpq, hnxy, honly⟩ := hDiam
    exact diamond_core_reducible G H hA1 hA2 hC hxp hxq hyp hyq hpq hnxy honly
  by_cases hC4 : ∃ x y p q : V,
      H.C = {x, y, p, q} ∧ G.Adj x p ∧ G.Adj p y ∧ G.Adj y q ∧ G.Adj q x ∧
      (∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
        s(a, b) = s(x, p) ∨ s(a, b) = s(p, y) ∨ s(a, b) = s(y, q) ∨ s(a, b) = s(q, x))
  · obtain ⟨x, y, p, q, hC, hxp, hpy, hyq, hqx, honly⟩ := hC4
    exact c4_core_reducible G H hA1 hA2 hC hxp hpy hyq hqx honly
  by_cases hPaw : ∃ p q r s : V,
      H.C = {p, q, r, s} ∧ G.Adj p q ∧ G.Adj p r ∧ G.Adj q r ∧ G.Adj r s ∧
      (∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
        s(a, b) = s(p, q) ∨ s(a, b) = s(p, r) ∨ s(a, b) = s(q, r) ∨ s(a, b) = s(r, s))
  · obtain ⟨p, q, r, s, hC, hpq, hpr, hqr, hrs, honly⟩ := hPaw
    exact paw_core_reducible G H hA1 hA2 hC hpq hpr hqr hrs honly
  by_cases hK3 : ∃ p q r s : V,
      H.C = {p, q, r, s} ∧ G.Adj p q ∧ G.Adj p r ∧ G.Adj q r ∧
      (∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
        s(a, b) = s(p, q) ∨ s(a, b) = s(p, r) ∨ s(a, b) = s(q, r))
  · obtain ⟨p, q, r, s, hC, hpq, hpr, hqr, honly⟩ := hK3
    exact k3k1_core_reducible G H hA1 hA2 hC hpq hpr hqr honly
  -- Lemma 2.2: every graph on the 4-set `C` is one of the cases above or has ≤ 1 edge.
  exfalso
  obtain ⟨a, b, c, d, -, -, -, -, -, -, hC⟩ := card_eq_four.1 H.hCcard
  rcases core4_classify G a b c d with
    ⟨e0, e1, h⟩ | ⟨p0, p1, q0, q1, he, h1, h2, h⟩ | ⟨p, q, r, s, he, h1, h2, h3, h⟩ |
    ⟨p, q, r, s, he, h1, h2, h⟩ | ⟨p, q, r, s, he, h1, h2, h3, h⟩ |
    ⟨x, y, z, w, he, h1, h2, h3, h4, h5, h6⟩ |
    ⟨x, y, p, q, he, h1, h2, h3, h4, h5, h6, h⟩ | ⟨x, y, p, q, he, h1, h2, h3, h4, h⟩ |
    ⟨p, q, r, s, he, h1, h2, h3, h4, h⟩ | ⟨p, q, r, s, he, h1, h2, h3, h⟩
  · have := numCoreEdges_le_one G H e0 e1 (by rw [hC]; exact h); omega
  · exact h2K2 ⟨p0, p1, q0, q1, hC.trans he, h1, h2, by rw [hC]; exact h⟩
  · exact hstar ⟨p, q, r, s, hC.trans he, h1, h2, h3, by rw [hC]; exact h⟩
  · exact hpath ⟨p, q, r, s, hC.trans he, h1, h2, by rw [hC]; exact h⟩
  · exact hP4 ⟨p, q, r, s, hC.trans he, h1, h2, h3, by rw [hC]; exact h⟩
  · exact hK4c ⟨x, y, z, w, hC.trans he, h1, h2, h3, h4, h5, h6⟩
  · exact hDiam ⟨x, y, p, q, hC.trans he, h1, h2, h3, h4, h5, h6, by rw [hC]; exact h⟩
  · exact hC4 ⟨x, y, p, q, hC.trans he, h1, h2, h3, h4, by rw [hC]; exact h⟩
  · exact hPaw ⟨p, q, r, s, hC.trans he, h1, h2, h3, h4, by rw [hC]; exact h⟩
  · exact hK3 ⟨p, q, r, s, hC.trans he, h1, h2, h3, by rw [hC]; exact h⟩


end Tuza.CodegreeFour
