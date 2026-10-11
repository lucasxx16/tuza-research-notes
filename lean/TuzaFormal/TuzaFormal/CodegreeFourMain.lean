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

omit [Fintype V] in
lemma set4_eq_of {x y p q x' y' p' q' : V}
    (h1 : x' ∈ ({x, y, p, q} : Finset V)) (h2 : y' ∈ ({x, y, p, q} : Finset V))
    (h3 : p' ∈ ({x, y, p, q} : Finset V)) (h4 : q' ∈ ({x, y, p, q} : Finset V))
    (h5 : x ∈ ({x', y', p', q'} : Finset V)) (h6 : y ∈ ({x', y', p', q'} : Finset V))
    (h7 : p ∈ ({x', y', p', q'} : Finset V)) (h8 : q ∈ ({x', y', p', q'} : Finset V)) :
    ({x, y, p, q} : Finset V) = {x', y', p', q'} := by
  ext w; constructor
  · intro hw; simp only [mem_insert, mem_singleton] at hw
    rcases hw with e | e | e | e <;> rw [e] <;> assumption
  · intro hw; simp only [mem_insert, mem_singleton] at hw
    rcases hw with e | e | e | e <;> rw [e] <;> assumption

/-! ### Four-cycle core (Proposition 6.3) -/

/-- C1: private edge `cd`; core = 4-cycle `x p y q`. -/
def specC1 : CertSpec where
  P := {{0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}, {1, 8, 9}}
  X := {s(2, 4), s(4, 3), s(3, 5), s(5, 2), s(8, 9), s(0, 1), s(0, 6), s(0, 7), s(1, 8), s(1, 9)}
  pres := {s(2, 4), s(4, 3), s(3, 5), s(5, 2), s(8, 9)}
  abs := {s(2, 3), s(4, 5)}

lemma specC1_ok : specC1.Ok := by decide +kernel

/-- C3 / D2 (crossed attachment matchings), private edge `ab` present. -/
def specC3ab : CertSpec where
  P := {{0, 2, 6}, {0, 4, 7}, {0, 3, 5}, {1, 2, 4}, {1, 3, 8}, {1, 5, 9}}
  X := {s(2, 6), s(4, 7), s(3, 5), s(2, 4), s(3, 8), s(5, 9), s(6, 7),
    s(0, 3), s(0, 5), s(1, 2), s(1, 4), s(1, 9)}
  pres := {s(2, 6), s(4, 7), s(3, 5), s(2, 4), s(3, 8), s(5, 9), s(6, 7)}
  abs := {s(4, 6), s(2, 7), s(5, 8)}

lemma specC3ab_ok : specC3ab.Ok := by decide +kernel

/-- C3 / D2, private edge `ab` absent. -/
def specC3nab : CertSpec where
  P := {{0, 2, 6}, {0, 4, 7}, {0, 3, 5}, {1, 2, 4}, {1, 3, 8}, {1, 5, 9}}
  X := {s(2, 6), s(4, 7), s(3, 5), s(2, 4), s(3, 8), s(5, 9),
    s(0, 3), s(0, 5), s(1, 2), s(1, 4), s(1, 9)}
  pres := {s(2, 6), s(4, 7), s(3, 5), s(2, 4), s(3, 8), s(5, 9)}
  abs := {s(4, 6), s(2, 7), s(5, 8), s(6, 7)}

lemma specC3nab_ok : specC3nab.Ok := by decide +kernel

/-- C4: exact opposite pair `N_C(a) = {p,q}` and outside triangle `ypd`. -/
def specC4 : CertSpec where
  P := {{0, 2, 7}, {0, 3, 5}, {0, 4, 6}, {1, 2, 4}, {1, 3, 8}, {1, 5, 9}, {3, 4, 9}}
  X := {s(2, 4), s(2, 7), s(4, 3), s(3, 5), s(3, 8), s(3, 9), s(4, 6), s(4, 9), s(5, 9),
    s(0, 1), s(0, 5), s(0, 7), s(1, 2), s(1, 8)}
  pres := {s(2, 4), s(2, 7), s(4, 3), s(3, 5), s(3, 8), s(3, 9), s(4, 6), s(4, 9), s(5, 9)}
  abs := {s(2, 3), s(2, 6), s(3, 6), s(4, 5)}

lemma specC4_ok : specC4.Ok := by decide +kernel

/-- The non-WKE obstruction (6): with `Q = {z, t, t'}` and `M = {rb, sa, zt}`. -/
lemma c4_wke6 (H : HubConfig G) {r s t t' a b : V}
    (hC : H.C = {r, s, t, t'}) (hA : H.A = {a, b})
    (hrs : ¬ G.Adj r s) (hab : ¬ G.Adj a b) (hra : ¬ G.Adj r a) (hsb : ¬ G.Adj s b)
    (hrb : G.Adj r b) (hsa : G.Adj s a) : IsWKE (linkGraph G H.u) := by
  obtain ⟨d_rs, d_rt, d_rt', d_st, d_st', d_tt'⟩ := core4_distinct G H hC
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have htC : t ∈ H.C := by rw [hC]; simp
  have haA : a ∈ H.A := by rw [hA]; simp
  have hbA : b ∈ H.A := by rw [hA]; simp
  have d_ab : a ≠ b := ne_of_pair_card hA H.hA
  have d_ra := ne_core_priv G H hrC haA
  have d_rb := ne_core_priv G H hrC hbA
  have d_sa := ne_core_priv G H hsC haA
  have d_sb := ne_core_priv G H hsC hbA
  have d_ta := ne_core_priv G H htC haA
  have d_tb := ne_core_priv G H htC hbA
  have d_vr : H.v ≠ r := fun e => H.hvA.2 (e ▸ hrC)
  have d_vs : H.v ≠ s := fun e => H.hvA.2 (e ▸ hsC)
  have d_vt : H.v ≠ t := fun e => H.hvA.2 (e ▸ htC)
  have d_va : H.v ≠ a := fun e => H.hvA.1 (e ▸ haA)
  have d_vb : H.v ≠ b := fun e => H.hvA.1 (e ▸ hbA)
  have NC {w : V} (hw : w ∈ H.C) : w ∈ G.neighborFinset H.u := core_mem_Nu G H hw
  have NA {w : V} (hw : w ∈ H.A) : w ∈ G.neighborFinset H.u := by
    rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hw)
  have hvt : G.Adj H.v t := hub_adj_CB G H (mem_union_left _ htC)
  refine wke3 (linkGraph G H.u) (a := r) (b := b) (c := s) (d := a) (e := H.v) (f := t)
    (q1 := H.v) (q2 := t) (q3 := t')
    ⟨NC hrC, NA hbA, hrb⟩ ⟨NC hsC, NA haA, hsa⟩ ⟨opposite_hub_mem G H, NC htC, hvt⟩
    (by simp [List.nodup_cons, d_rb, d_rs, d_ra, d_vr.symm, d_rt, d_sb.symm, d_ab.symm,
      d_vb.symm, d_tb.symm, d_sa, d_vs.symm, d_st, d_va.symm, d_ta.symm, d_vt]) ?_
  intro g hg hO
  revert hg hO
  refine Sym2.inductionOn g fun m n hg hO => ?_
  have hmn : (linkGraph G H.u).Adj m n := (mem_edgeFinset (G := linkGraph G H.u)).1 hg
  have hG : G.Adj m n := hmn.2.2
  have cls (w : V) (hw : w ∈ G.neighborFinset H.u) (hwO : w ∉ ({H.v, t, t'} : Finset V)) :
      w = r ∨ w = s ∨ w = a ∨ w = b := by
    rw [H.hNu] at hw
    simp only [mem_insert, mem_union, mem_singleton, not_or] at hw hwO
    rcases hw with h | h | h
    · exact absurd h hwO.1
    · rw [hC] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd h hwO.2.1
      · exact absurd h hwO.2.2
    · rw [hA] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  rcases cls m hmn.1 (hO m (by simp)) with rfl | rfl | rfl | rfl <;>
  rcases cls n hmn.2.1 (hO n (by simp)) with rfl | rfl | rfl | rfl <;>
  first
  | exact (G.irrefl hG).elim
  | exact Or.inl rfl
  | exact Or.inl Sym2.eq_swap
  | exact Or.inr (Or.inl rfl)
  | exact Or.inr (Or.inl Sym2.eq_swap)
  | exact (hrs hG).elim
  | exact (hrs hG.symm).elim
  | exact (hab hG).elim
  | exact (hab hG.symm).elim
  | exact (hra hG).elim
  | exact (hra hG.symm).elim
  | exact (hsb hG).elim
  | exact (hsb hG.symm).elim

set_option maxHeartbeats 0 in
/-- **Proposition 6.3**: C₄ core is reducible under (A1)–(A2).
The case tree over the 18 private attachment bits was generated mechanically
(`gen/c4gen.py`); every leaf is closed by a certificate C1–C4 (checked via
`reducible_of_spec`), or by full support, the budget (2), link connectivity,
or the non-WKE obstruction (6). -/
theorem c4_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hpy : G.Adj p y) (hyq : G.Adj y q) (hqx : G.Adj q x)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(x, p) ∨ s(a, b) = s(p, y) ∨ s(a, b) = s(y, q) ∨ s(a, b) = s(q, x)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨d_xy, d_xp, d_xq, d_yp, d_yq, d_pq⟩ := core4_distinct G H hC
  have hxC : x ∈ H.C := by rw [hC]; simp
  have hyC : y ∈ H.C := by rw [hC]; simp
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hnxy : ¬ G.Adj x y := by
    intro h
    rcases honly x hxC y hyC h with e | e | e | e <;>
      simp [Sym2.eq_iff, d_xy, d_xp, d_xq, d_yp, d_yq, d_pq, d_xy.symm, d_xp.symm,
        d_xq.symm, d_yp.symm, d_yq.symm, d_pq.symm] at e
  have hnpq : ¬ G.Adj p q := by
    intro h
    rcases honly p hpC q hqC h with e | e | e | e <;>
      simp [Sym2.eq_iff, d_xy, d_xp, d_xq, d_yp, d_yq, d_pq, d_xy.symm, d_xp.symm,
        d_xq.symm, d_yp.symm, d_yq.symm, d_pq.symm] at e
  obtain ⟨sA, sB⟩ := diamond_full_support G H hA1 hC hxp hyq
  obtain ⟨a, b, hne_ab, hA⟩ := card_eq_two.1 H.hA
  obtain ⟨c, d, hne_cd, hB⟩ := card_eq_two.1 H.hB
  have bud_x := leaf_budget G H hA2 hxC hpC hqC hxp hqx.symm d_pq a b c d hA hB
  have bud_y := leaf_budget G H hA2 hyC hpC hqC hpy.symm hyq d_pq a b c d hA hB
  have bud_p := leaf_budget G H hA2 hpC hxC hyC hxp.symm hpy d_xy a b c d hA hB
  have bud_q := leaf_budget G H hA2 hqC hxC hyC hqx hyq.symm d_xy a b c d hA hB
  by_cases h_ab : G.Adj a b
  ·
    have hC' := (show H.swap.C = {x, y, p, q} from hC)
    have hA' := (show H.swap.A = {c, d} from hB)
    have hB' := (show H.swap.B = {a, b} from hA)
    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC1 specC1_ok (by simp only [specC1]; spec_present) (by simp only [specC1]; spec_absent))
  ·
    by_cases h_cd : G.Adj c d
    ·
      have hC' := (show H.C = {x, y, p, q} from hC)
      have hA' := (show H.A = {a, b} from hA)
      have hB' := (show H.B = {c, d} from hB)
      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC1 specC1_ok (by simp only [specC1]; spec_present) (by simp only [specC1]; spec_absent)
    ·
      by_cases h_xa : G.Adj x a
      ·
        by_cases h_yc : G.Adj y c
        ·
          by_cases h_xb : G.Adj x b
          ·
            by_cases h_xc : G.Adj x c
            ·
              by_cases h_pd : G.Adj p d
              ·
                by_cases h_qa : G.Adj q a
                ·
                  by_cases h_qb : G.Adj q b
                  ·
                    by_cases h_qd : G.Adj q d
                    ·
                      by_cases h_ya : G.Adj y a
                      ·
                        by_cases h_pb : G.Adj p b
                        ·
                          by_cases h_qc : G.Adj q c
                          ·
                            exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            by_cases h_pa : G.Adj p a
                            ·
                              by_cases h_pc : G.Adj p c
                              ·
                                exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                            ·
                              by_cases h_xd : G.Adj x d
                              ·
                                exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.swap.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {a, b} from hA)
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                        ·
                          by_cases h_yb : G.Adj y b
                          ·
                            by_cases h_qc : G.Adj q c
                            ·
                              exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              by_cases h_pa : G.Adj p a
                              ·
                                by_cases h_xd : G.Adj x d
                                ·
                                  exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                                ·
                                  have hC' := (show H.swap.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.swap.A = {c, d} from hB)
                                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                              ·
                                exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                          ·
                            have hC' := (show H.C = {x, y, p, q} from hC)
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                      ·
                        by_cases h_pa : G.Adj p a
                        ·
                          by_cases h_yb : G.Adj y b
                          ·
                            by_cases h_xd : G.Adj x d
                            ·
                              exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              by_cases h_qc : G.Adj q c
                              ·
                                exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.swap.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {a, b} from hA)
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                          ·
                            exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                        ·
                          have hC' := (show H.C = {x, y, p, q} from hC)
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_xd : G.Adj x d
                      ·
                        exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        have hC' := (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_yb : G.Adj y b
                    ·
                      by_cases h_xd : G.Adj x d
                      ·
                        exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        by_cases h_ya : G.Adj y a
                        ·
                          by_cases h_yd : G.Adj y d
                          ·
                            exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            by_cases h_pa : G.Adj p a
                            ·
                              have hC' := (show H.swap.C = {x, y, p, q} from hC)
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                            ·
                              by_cases h_pc : G.Adj p c
                              ·
                                by_cases h_pb : G.Adj p b
                                ·
                                  exact (hA1.2.1 (c4_wke6 G H (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {a, b} from hA) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                                ·
                                  have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                              ·
                                have hC' := (show H.swap.C = {x, y, p, q} from hC)
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                        ·
                          have hC' := (show H.C = {y, p, q, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                    ·
                      have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_qb : G.Adj q b
                  ·
                    by_cases h_ya : G.Adj y a
                    ·
                      by_cases h_xd : G.Adj x d
                      ·
                        exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        by_cases h_yb : G.Adj y b
                        ·
                          by_cases h_yd : G.Adj y d
                          ·
                            exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            by_cases h_pb : G.Adj p b
                            ·
                              have hC' := (show H.swap.C = {x, y, p, q} from hC)
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                            ·
                              by_cases h_pc : G.Adj p c
                              ·
                                by_cases h_pa : G.Adj p a
                                ·
                                  exact (hA1.2.1 (c4_wke6 G H (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                                ·
                                  have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {a, b} from hA)
                                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                              ·
                                have hC' := (show H.swap.C = {x, y, p, q} from hC)
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {a, b} from hA)
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                        ·
                          have hC' := (show H.C = {y, p, q, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                    ·
                      have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {a, b} from hA)
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_qd : G.Adj q d
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    by_cases h_xd : G.Adj x d
                    ·
                      exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                    ·
                      have hC' := (show H.swap.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_pb : G.Adj p b
                    ·
                      by_cases h_ya : G.Adj y a
                      ·
                        by_cases h_xd : G.Adj x d
                        ·
                          exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.swap.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        have hC' := (show H.C = {x, y, p, q} from hC)
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  by_cases h_xd : G.Adj x d
                  ·
                    exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                  ·
                    by_cases h_yd : G.Adj y d
                    ·
                      have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {c, d} from hB) (core_iso G (show H.swap.C = {x, y, p, q} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
            ·
              by_cases h_xd : G.Adj x d
              ·
                by_cases h_pc : G.Adj p c
                ·
                  by_cases h_ya : G.Adj y a
                  ·
                    by_cases h_qc : G.Adj q c
                    ·
                      by_cases h_yb : G.Adj y b
                      ·
                        by_cases h_yd : G.Adj y d
                        ·
                          exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {x, y, p, q} from hC) (show H.swap.A = {c, d} from hB) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                      ·
                        by_cases h_pb : G.Adj p b
                        ·
                          by_cases h_qb : G.Adj q b
                          ·
                            by_cases h_pd : G.Adj p d
                            ·
                              by_cases h_qd : G.Adj q d
                              ·
                                by_cases h_pa : G.Adj p a
                                ·
                                  exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                                ·
                                  have hC' := (show H.C = {y, q, p, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {a, b} from hA)
                                  have hB' := (show H.B = {c, d} from hB)
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                              ·
                                have hC' := (show H.swap.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                            ·
                              have hC' := (show H.swap.C = {x, q, p, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                          ·
                            have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                        ·
                          have hC' := (show H.C = {x, y, p, q} from hC)
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      have hC' := (show H.swap.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_qa : G.Adj q a
                    ·
                      by_cases h_yb : G.Adj y b
                      ·
                        by_cases h_pd : G.Adj p d
                        ·
                          by_cases h_pa : G.Adj p a
                          ·
                            by_cases h_qc : G.Adj q c
                            ·
                              by_cases h_qd : G.Adj q d
                              ·
                                by_cases h_pb : G.Adj p b
                                ·
                                  exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                                ·
                                  have hC' := (show H.C = {y, q, p, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                                  have hB' := (show H.B = {c, d} from hB)
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                              ·
                                have hC' := (show H.swap.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                                have hB' := (show H.swap.B = {a, b} from hA)
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                            ·
                              have hC' := (show H.swap.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                          ·
                            have hC' := (show H.C = {x, y, p, q} from hC)
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                        ·
                          have hC' := (show H.swap.C = {x, q, p, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {a, b} from hA)
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {c, d} from hB)
                  have hB' := (show H.swap.B = {a, b} from hA)
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
              ·
                exact absurd (sB x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_pb : G.Adj p b
            ·
              by_cases h_qd : G.Adj q d
              ·
                by_cases h_qc : G.Adj q c
                ·
                  by_cases h_qb : G.Adj q b
                  ·
                    by_cases h_yd : G.Adj y d
                    ·
                      by_cases h_ya : G.Adj y a
                      ·
                        by_cases h_pc : G.Adj p c
                        ·
                          by_cases h_yb : G.Adj y b
                          ·
                            exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            have hC' := (show H.C = {x, y, p, q} from hC)
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          by_cases h_pd : G.Adj p d
                          ·
                            by_cases h_xc : G.Adj x c
                            ·
                              by_cases h_qa : G.Adj q a
                              ·
                                exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.A = {a, b} from hA)
                                have hB' := (show H.B = {c, d} from hB)
                                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                            ·
                              have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                          ·
                            exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        by_cases h_qa : G.Adj q a
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_pd : G.Adj p d
                      ·
                        by_cases h_qa : G.Adj q a
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                      ·
                        have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    by_cases h_pd : G.Adj p d
                    ·
                      by_cases h_qb : G.Adj q b
                      ·
                        by_cases h_yd : G.Adj y d
                        ·
                          by_cases h_ya : G.Adj y a
                          ·
                            by_cases h_pc : G.Adj p c
                            ·
                              exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                          ·
                            by_cases h_yb : G.Adj y b
                            ·
                              exact (hA1.2.1 (c4_wke6 G H (show H.C = {x, y, p, q} from hC) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.C = {x, y, p, q} from hC)
                              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                              have hB' := (show H.B = {c, d} from hB)
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          have hC' := (show H.swap.C = {y, p, q, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_yd : G.Adj y d
                      ·
                        by_cases h_pc : G.Adj p c
                        ·
                          exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                        ·
                          exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    have hC' := (show H.C = {x, y, p, q} from hC)
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
              ·
                by_cases h_ya : G.Adj y a
                ·
                  by_cases h_xd : G.Adj x d
                  ·
                    by_cases h_qc : G.Adj q c
                    ·
                      by_cases h_yd : G.Adj y d
                      ·
                        by_cases h_pa : G.Adj p a
                        ·
                          by_cases h_pc : G.Adj p c
                          ·
                            by_cases h_yb : G.Adj y b
                            ·
                              exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.C = {x, y, p, q} from hC)
                              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                          ·
                            by_cases h_pd : G.Adj p d
                            ·
                              exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {c, d} from hB) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.swap.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                        ·
                          have hC' := (show H.C = {x, y, p, q} from hC)
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                      ·
                        have hC' := (show H.swap.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    by_cases h_pd : G.Adj p d
                    ·
                      by_cases h_qb : G.Adj q b
                      ·
                        have hC' := (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_qc : G.Adj q c
                        ·
                          have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                        ·
                          exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      by_cases h_yd : G.Adj y d
                      ·
                        have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {c, d} from hB) (core_iso G (show H.swap.C = {x, y, p, q} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                ·
                  by_cases h_qa : G.Adj q a
                  ·
                    by_cases h_yb : G.Adj y b
                    ·
                      exact (hA1.2.1 (c4_wke6 G H (show H.C = {x, y, p, q} from hC) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                    ·
                      exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_qb : G.Adj q b
              ·
                by_cases h_pd : G.Adj p d
                ·
                  have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_yb : G.Adj y b
                ·
                  by_cases h_xd : G.Adj x d
                  ·
                    have hC' := (show H.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    by_cases h_xc : G.Adj x c
                    ·
                      have hC' := (show H.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      exact absurd (sB x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  exact absurd (priv_isolated_edge G H hA1 (show H.A = {a, b} from hA) (core_iso G hC (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
        ·
          by_cases h_yd : G.Adj y d
          ·
            by_cases h_pc : G.Adj p c
            ·
              by_cases h_qb : G.Adj q b
              ·
                by_cases h_qa : G.Adj q a
                ·
                  by_cases h_qc : G.Adj q c
                  ·
                    by_cases h_xb : G.Adj x b
                    ·
                      by_cases h_xd : G.Adj x d
                      ·
                        by_cases h_pa : G.Adj p a
                        ·
                          by_cases h_xc : G.Adj x c
                          ·
                            exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                        ·
                          by_cases h_pb : G.Adj p b
                          ·
                            by_cases h_ya : G.Adj y a
                            ·
                              by_cases h_xc : G.Adj x c
                              ·
                                exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                have hA' := (show H.swap.A = {c, d} from hB)
                                have hB' := (show H.swap.B = {a, b} from hA)
                                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                            ·
                              have hC' := (show H.C = {x, y, p, q} from hC)
                              have hA' := (show H.A = {a, b} from hA)
                              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                          ·
                            exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        by_cases h_qd : G.Adj q d
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.swap.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        by_cases h_qd : G.Adj q d
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.swap.C = {y, p, q, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    have hC' := (show H.swap.C = {p, q, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                ·
                  by_cases h_xb : G.Adj x b
                  ·
                    by_cases h_xd : G.Adj x d
                    ·
                      by_cases h_ya : G.Adj y a
                      ·
                        by_cases h_pd : G.Adj p d
                        ·
                          by_cases h_pb : G.Adj p b
                          ·
                            by_cases h_xc : G.Adj x c
                            ·
                              exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                          ·
                            by_cases h_pa : G.Adj p a
                            ·
                              exact (hA1.2.1 (c4_wke6 G H (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.A = {a, b} from hA)
                              have hB' := (show H.B = {c, d} from hB)
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {x, y, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_pd : G.Adj p d
                      ·
                        by_cases h_xc : G.Adj x c
                        ·
                          exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {x, y, p, q} from hC) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                        ·
                          exact absurd (sB x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    have hC' := (show H.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
              ·
                by_cases h_xd : G.Adj x d
                ·
                  by_cases h_yb : G.Adj y b
                  ·
                    by_cases h_qa : G.Adj q a
                    ·
                      by_cases h_xb : G.Adj x b
                      ·
                        by_cases h_pd : G.Adj p d
                        ·
                          by_cases h_pa : G.Adj p a
                          ·
                            by_cases h_xc : G.Adj x c
                            ·
                              exact (bud_x ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                          ·
                            by_cases h_pb : G.Adj p b
                            ·
                              exact (hA1.2.1 (c4_wke6 G H (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {a, b} from hA) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                              have hB' := (show H.B = {c, d} from hB)
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    by_cases h_pb : G.Adj p b
                    ·
                      by_cases h_qc : G.Adj q c
                      ·
                        have hC' := (show H.C = {p, q, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                      ·
                        by_cases h_qa : G.Adj q a
                        ·
                          have hC' := (show H.swap.C = {p, q, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                        ·
                          exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      by_cases h_xb : G.Adj x b
                      ·
                        have hC' := (show H.C = {x, y, p, q} from hC)
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                      ·
                        exact absurd (priv_isolated_edge G H hA1 (show H.A = {a, b} from hA) (core_iso G hC (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                ·
                  by_cases h_qd : G.Adj q d
                  ·
                    by_cases h_xc : G.Adj x c
                    ·
                      exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {x, y, p, q} from hC) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                    ·
                      exact absurd (sB x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    have hC' := (show H.swap.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
            ·
              by_cases h_qc : G.Adj q c
              ·
                by_cases h_pb : G.Adj p b
                ·
                  have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {c, d} from hB)
                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_xc : G.Adj x c
                ·
                  by_cases h_yb : G.Adj y b
                  ·
                    have hC' := (show H.swap.C = {x, y, p, q} from hC)
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_ya : G.Adj y a
                    ·
                      have hC' := (show H.swap.C = {x, y, p, q} from hC)
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (core_iso G (show H.swap.C = {x, y, p, q} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
          ·
            exact absurd (sB y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
      ·
        by_cases h_pa : G.Adj p a
        ·
          by_cases h_qc : G.Adj q c
          ·
            by_cases h_xb : G.Adj x b
            ·
              by_cases h_yd : G.Adj y d
              ·
                by_cases h_yc : G.Adj y c
                ·
                  by_cases h_yb : G.Adj y b
                  ·
                    by_cases h_qd : G.Adj q d
                    ·
                      by_cases h_qa : G.Adj q a
                      ·
                        by_cases h_pc : G.Adj p c
                        ·
                          by_cases h_ya : G.Adj y a
                          ·
                            exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            have hC' := (show H.C = {x, y, p, q} from hC)
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          by_cases h_pd : G.Adj p d
                          ·
                            by_cases h_xc : G.Adj x c
                            ·
                              by_cases h_ya : G.Adj y a
                              ·
                                exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                              ·
                                have hC' := (show H.C = {x, y, p, q} from hC)
                                have hA' := (show H.A = {a, b} from hA)
                                have hB' := (show H.B = {c, d} from hB)
                                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                            ·
                              have hC' := (show H.swap.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                          ·
                            exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_xd : G.Adj x d
                      ·
                        by_cases h_pb : G.Adj p b
                        ·
                          by_cases h_pc : G.Adj p c
                          ·
                            by_cases h_ya : G.Adj y a
                            ·
                              exact (bud_y ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.C = {x, y, p, q} from hC)
                              have hA' := (show H.A = {a, b} from hA)
                              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                          ·
                            by_cases h_pd : G.Adj p d
                            ·
                              exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {c, d} from hB) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.swap.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                        ·
                          have hC' := (show H.C = {x, y, p, q} from hC)
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                      ·
                        have hC' := (show H.swap.C = {y, x, q, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_ya : G.Adj y a
                    ·
                      exact (hA1.2.1 (c4_wke6 G H (show H.C = {x, y, p, q} from hC) (show H.A = {a, b} from hA) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                    ·
                      exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  by_cases h_pb : G.Adj p b
                  ·
                    by_cases h_pc : G.Adj p c
                    ·
                      by_cases h_qa : G.Adj q a
                      ·
                        by_cases h_pd : G.Adj p d
                        ·
                          exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.swap.C = {y, q, p, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    have hC' := (show H.C = {x, q, p, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
              ·
                by_cases h_qa : G.Adj q a
                ·
                  by_cases h_pd : G.Adj p d
                  ·
                    by_cases h_yc : G.Adj y c
                    ·
                      by_cases h_pc : G.Adj p c
                      ·
                        by_cases h_qb : G.Adj q b
                        ·
                          by_cases h_qd : G.Adj q d
                          ·
                            exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                          ·
                            have hC' := (show H.swap.C = {p, q, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                            have hB' := (show H.swap.B = {a, b} from hA)
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                        ·
                          have hC' := (show H.C = {x, p, q, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                      ·
                        have hC' := (show H.swap.C = {y, q, p, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                    ·
                      exact absurd (sB y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    by_cases h_xd : G.Adj x d
                    ·
                      by_cases h_yb : G.Adj y b
                      ·
                        have hC' := (show H.swap.C = {x, y, p, q} from hC)
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_ya : G.Adj y a
                        ·
                          have hC' := (show H.swap.C = {x, y, p, q} from hC)
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                        ·
                          exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      by_cases h_qd : G.Adj q d
                      ·
                        have hC' := (show H.swap.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {c, d} from hB) (core_iso G (show H.swap.C = {x, y, p, q} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                ·
                  have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {a, b} from hA)
                  have hB' := (show H.B = {c, d} from hB)
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              exact absurd (sA x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_qd : G.Adj q d
            ·
              by_cases h_xb : G.Adj x b
              ·
                by_cases h_yc : G.Adj y c
                ·
                  by_cases h_pb : G.Adj p b
                  ·
                    by_cases h_pd : G.Adj p d
                    ·
                      by_cases h_qa : G.Adj q a
                      ·
                        by_cases h_yd : G.Adj y d
                        ·
                          by_cases h_yb : G.Adj y b
                          ·
                            by_cases h_pc : G.Adj p c
                            ·
                              exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {c, d} from hB)
                              have hB' := (show H.swap.B = {a, b} from hA)
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent))
                          ·
                            by_cases h_ya : G.Adj y a
                            ·
                              exact (hA1.2.1 (c4_wke6 G H (show H.C = {x, y, p, q} from hC) (show H.A = {a, b} from hA) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                            ·
                              have hC' := (show H.C = {x, y, p, q} from hC)
                              have hA' := (show H.A = {a, b} from hA)
                              have hB' := (show H.B = {c, d} from hB)
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC4 specC4_ok (by simp only [specC4]; spec_present) (by simp only [specC4]; spec_absent)
                        ·
                          have hC' := (show H.swap.C = {y, p, q, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent))
                      ·
                        have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_yd : G.Adj y d
                      ·
                        by_cases h_pc : G.Adj p c
                        ·
                          exact (hA1.2.2.2 (c4_wke6 G H.swap (show H.swap.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)))).elim
                        ·
                          exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        have hC' := (show H.swap.C = {q, p, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    have hC' := (show H.C = {x, y, p, q} from hC)
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specC3nab specC3nab_ok (by simp only [specC3nab]; spec_present) (by simp only [specC3nab]; spec_absent)
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    by_cases h_qa : G.Adj q a
                    ·
                      have hC' := (show H.swap.C = {p, q, y, x} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      have hC' := (show H.C = {p, q, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {a, b} from hA)
                      have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    by_cases h_xc : G.Adj x c
                    ·
                      by_cases h_yb : G.Adj y b
                      ·
                        have hC' := (show H.swap.C = {x, y, p, q} from hC)
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_ya : G.Adj y a
                        ·
                          have hC' := (show H.swap.C = {x, y, p, q} from hC)
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                        ·
                          exact absurd (sA y (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (core_iso G (show H.swap.C = {x, y, p, q} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
              ·
                exact absurd (sA x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
        ·
          by_cases h_ya : G.Adj y a
          ·
            by_cases h_xc : G.Adj x c
            ·
              have hC' := (show H.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {a, b} from hA)
              have hB' := (show H.B = {c, d} from hB)
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_xd : G.Adj x d
              ·
                have hC' := (show H.C = {y, x, p, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {a, b} from hA)
                have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                exact absurd (sB x (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_qa : G.Adj q a
            ·
              by_cases h_pc : G.Adj p c
              ·
                have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {a, b} from hA)
                have hB' := (show H.B = {c, d} from hB)
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                by_cases h_pd : G.Adj p d
                ·
                  have hC' := (show H.C = {q, p, x, y} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {a, b} from hA)
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              exact absurd (priv_isolated_edge G H hA1 (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (core_iso G hC (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))

/-! ### Paw core (Proposition 6.4) -/

/-- D3 / P2: two unused private vertices. -/
def specD3 : CertSpec where
  P := {{0, 1, 5}, {0, 2, 4}, {0, 3, 6}, {1, 2, 8}, {1, 3, 4}}
  X := {s(2, 4), s(3, 6), s(2, 8), s(3, 4), s(0, 1), s(0, 5), s(0, 6), s(1, 5), s(1, 8)}
  pres := {s(2, 4), s(3, 6), s(2, 8), s(3, 4)}
  abs := {s(2, 7), s(3, 7), s(4, 7), s(2, 9), s(3, 9), s(4, 9), s(2, 3)}

lemma specD3_ok : specD3.Ok := by decide +kernel

/-- D4 / P3: a private edge and an outside triangle. -/
def specD4 : CertSpec where
  P := {{0, 1, 2}, {0, 3, 5}, {0, 6, 7}, {1, 3, 8}, {1, 5, 9}, {2, 4, 6}}
  X := {s(2, 4), s(2, 6), s(4, 6), s(3, 5), s(3, 8), s(5, 9), s(6, 7),
    s(0, 3), s(0, 5), s(1, 2), s(1, 4), s(1, 9)}
  pres := {s(2, 4), s(2, 6), s(4, 6), s(3, 5), s(3, 8), s(5, 9), s(6, 7)}
  abs := {s(2, 7), s(4, 7), s(5, 8)}

lemma specD4_ok : specD4.Ok := by decide +kernel

/-- P4: dominant asymmetry against a matched edge (labels `t w p h`). -/
def specP4 : CertSpec where
  P := {{0, 1, 3}, {0, 4, 5}, {0, 2, 6}, {1, 5, 9}, {1, 4, 8}}
  X := {s(4, 5), s(2, 6), s(5, 9), s(4, 8), s(0, 4), s(0, 5), s(0, 7), s(1, 2), s(1, 3), s(1, 8)}
  pres := {s(4, 5), s(2, 6), s(5, 9), s(4, 8)}
  abs := {s(3, 6), s(4, 9), s(2, 3)}

lemma specP4_ok : specP4.Ok := by decide +kernel

/-- Budget at a core vertex with three core neighbours. -/
lemma bud3_card (H : HubConfig G) (hA2 : H.A2) {t n1 n2 n3 : V} (htC : t ∈ H.C)
    (h1C : n1 ∈ H.C) (h2C : n2 ∈ H.C) (h3C : n3 ∈ H.C)
    (h1 : G.Adj t n1) (h2 : G.Adj t n2) (h3 : G.Adj t n3)
    (d12 : n1 ≠ n2) (d13 : n1 ≠ n3) (d23 : n2 ≠ n3) :
    (G.neighborFinset t ∩ H.A).card + (G.neighborFinset t ∩ H.B).card ≤ 2 := by
  have h := hA2 t htC
  have hd : 3 ≤ H.coreDeg t := by
    unfold HubConfig.coreDeg
    have hsub : ({n1, n2, n3} : Finset V) ⊆ (H.C.erase t).filter (G.Adj t) := by
      intro w hw; simp only [mem_insert, mem_singleton] at hw
      rcases hw with e | e | e <;> rw [e] <;> simp only [mem_filter, mem_erase]
      · exact ⟨⟨fun e => by subst e; exact G.irrefl h1, h1C⟩, h1⟩
      · exact ⟨⟨fun e => by subst e; exact G.irrefl h2, h2C⟩, h2⟩
      · exact ⟨⟨fun e => by subst e; exact G.irrefl h3, h3C⟩, h3⟩
    have hc : ({n1, n2, n3} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [d12, d13]), card_pair d23]
    calc 3 = _ := hc.symm
      _ ≤ _ := card_le_card hsub
  omega

lemma card_nbr_pair (S : Finset V) {t a b : V} (hS : S = {a, b}) (h2 : S.card = 2)
    (ha : G.Adj t a) (hb : G.Adj t b) : 2 ≤ (G.neighborFinset t ∩ S).card := by
  have hab := ne_of_pair_card hS h2
  have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset t ∩ S := by
    intro w hw
    refine mem_inter.2 ⟨?_, by rw [hS]; exact hw⟩
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with e | e <;> rw [e] <;> simpa
  calc 2 = ({a, b} : Finset V).card := (card_pair hab).symm
    _ ≤ _ := card_le_card hsub

lemma card_nbr_one (S : Finset V) {t e : V} (he : e ∈ S) (h : G.Adj t e) :
    1 ≤ (G.neighborFinset t ∩ S).card :=
  card_pos.2 ⟨e, mem_inter.2 ⟨by simpa, he⟩⟩

/-- Paw non-WKE obstruction: `N_C(a) = {p}`; `Q = {z, p, b}`, `M = {qr, pa, zs}`. -/
lemma paw_wke (H : HubConfig G) {p q r s a b : V}
    (hC : H.C = {p, q, r, s}) (hA : H.A = {a, b})
    (hqr : G.Adj q r) (hqs : ¬ G.Adj q s) (hrs : ¬ G.Adj r s) (hpa : G.Adj p a)
    (hqa : ¬ G.Adj q a) (hra : ¬ G.Adj r a) (hsa : ¬ G.Adj s a) :
    IsWKE (linkGraph G H.u) := by
  obtain ⟨d_pq, d_pr, d_ps, d_qr, d_qs, d_rs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have haA : a ∈ H.A := by rw [hA]; simp
  have d_qa := ne_core_priv G H hqC haA
  have d_ra := ne_core_priv G H hrC haA
  have d_pa := ne_core_priv G H hpC haA
  have d_sa := ne_core_priv G H hsC haA
  have d_vq : H.v ≠ q := fun e => H.hvA.2 (e ▸ hqC)
  have d_vr : H.v ≠ r := fun e => H.hvA.2 (e ▸ hrC)
  have d_vp : H.v ≠ p := fun e => H.hvA.2 (e ▸ hpC)
  have d_vs : H.v ≠ s := fun e => H.hvA.2 (e ▸ hsC)
  have d_va : H.v ≠ a := fun e => H.hvA.1 (e ▸ haA)
  have NC {w : V} (hw : w ∈ H.C) : w ∈ G.neighborFinset H.u := core_mem_Nu G H hw
  have NA {w : V} (hw : w ∈ H.A) : w ∈ G.neighborFinset H.u := by
    rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hw)
  have hvs : G.Adj H.v s := hub_adj_CB G H (mem_union_left _ hsC)
  refine wke3 (linkGraph G H.u) (a := q) (b := r) (c := p) (d := a) (e := H.v) (f := s)
    (q1 := H.v) (q2 := p) (q3 := b)
    ⟨NC hqC, NC hrC, hqr⟩ ⟨NC hpC, NA haA, hpa⟩ ⟨opposite_hub_mem G H, NC hsC, hvs⟩
    (by simp [List.nodup_cons, d_qr, d_pq.symm, d_qa, d_vq.symm, d_qs, d_pr.symm, d_ra,
      d_vr.symm, d_rs, d_pa, d_vp.symm, d_ps, d_va.symm, d_sa.symm, d_vs]) ?_
  intro g hg hO
  revert hg hO
  refine Sym2.inductionOn g fun m n hg hO => ?_
  have hmn : (linkGraph G H.u).Adj m n := (mem_edgeFinset (G := linkGraph G H.u)).1 hg
  have hG : G.Adj m n := hmn.2.2
  have cls (w : V) (hw : w ∈ G.neighborFinset H.u) (hwO : w ∉ ({H.v, p, b} : Finset V)) :
      w = q ∨ w = r ∨ w = s ∨ w = a := by
    rw [H.hNu] at hw
    simp only [mem_insert, mem_union, mem_singleton, not_or] at hw hwO
    rcases hw with h | h | h
    · exact absurd h hwO.1
    · rw [hC] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h | h | h
      · exact absurd h hwO.2.1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rw [hA] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd h hwO.2.2
  rcases cls m hmn.1 (hO m (by simp)) with rfl | rfl | rfl | rfl <;>
  rcases cls n hmn.2.1 (hO n (by simp)) with rfl | rfl | rfl | rfl <;>
  first
  | exact (G.irrefl hG).elim
  | exact Or.inl rfl
  | exact Or.inl Sym2.eq_swap
  | exact (hqs hG).elim
  | exact (hqs hG.symm).elim
  | exact (hrs hG).elim
  | exact (hrs hG.symm).elim
  | exact (hqa hG).elim
  | exact (hqa hG.symm).elim
  | exact (hra hG).elim
  | exact (hra hG.symm).elim
  | exact (hsa hG).elim
  | exact (hsa hG.symm).elim

set_option maxHeartbeats 0 in
/-- **Proposition 6.4**: paw core (triangle `pqr`, pendant `s` at `r`) is reducible under
(A1)–(A2). Generated case tree over the private attachment bits (`gen/pawgen.py`); leaves are
closed by certificates P1 = D1, P2 = D3, P3 = D4, P4, or by support, the budget (2) (including
the degree-three budget at `r`), link connectivity, or the non-WKE witness `paw_wke`. -/
theorem paw_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {p q r s : V} (hC : H.C = {p, q, r, s})
    (hpq : G.Adj p q) (hpr : G.Adj p r) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(p, q) ∨ s(a, b) = s(p, r) ∨ s(a, b) = s(q, r) ∨ s(a, b) = s(r, s)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨d_pq, d_pr, d_ps, d_qr, d_qs, d_rs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hnps : ¬ G.Adj p s := by
    intro h
    rcases honly p hpC s hsC h with e | e | e | e <;>
      simp [Sym2.eq_iff, d_pq, d_pr, d_ps, d_qr, d_qs, d_rs, d_pq.symm, d_pr.symm,
        d_ps.symm, d_qr.symm, d_qs.symm, d_rs.symm] at e
  have hnqs : ¬ G.Adj q s := by
    intro h
    rcases honly q hqC s hsC h with e | e | e | e <;>
      simp [Sym2.eq_iff, d_pq, d_pr, d_ps, d_qr, d_qs, d_rs, d_pq.symm, d_pr.symm,
        d_ps.symm, d_qr.symm, d_qs.symm, d_rs.symm] at e
  have hC' : H.C = {s, p, r, q} := hC.trans
    (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  obtain ⟨sA, sB⟩ := diamond_full_support G H hA1 hC' hrs.symm hpq
  obtain ⟨a, b, hne_ab, hA⟩ := card_eq_two.1 H.hA
  obtain ⟨c, d, hne_cd, hB⟩ := card_eq_two.1 H.hB
  have bud_p := leaf_budget G H hA2 hpC hqC hrC hpq hpr d_qr a b c d hA hB
  have bud_q := leaf_budget G H hA2 hqC hpC hrC hpq.symm hqr d_pr a b c d hA hB
  have bud_r := leaf_budget G H hA2 hrC hpC hqC hpr.symm hqr.symm d_pq a b c d hA hB
  have b3 := bud3_card G H hA2 hrC hpC hqC hsC hpr.symm hqr.symm hrs d_pq d_ps d_qs
  have bud3A_r : ∀ e ∈ H.B, ¬ (G.Adj r a ∧ G.Adj r b ∧ G.Adj r e) := by
    rintro e he ⟨h1, h2, h3⟩
    have := card_nbr_pair G H.A hA H.hA h1 h2
    have := card_nbr_one G H.B he h3
    omega
  have bud3B_r : ∀ e ∈ H.A, ¬ (G.Adj r c ∧ G.Adj r d ∧ G.Adj r e) := by
    rintro e he ⟨h1, h2, h3⟩
    have := card_nbr_pair G H.B hB H.hB h1 h2
    have := card_nbr_one G H.A he h3
    omega
  by_cases h_ra : G.Adj r a
  ·
    by_cases h_rc : G.Adj r c
    ·
      by_cases h_rb : G.Adj r b
      ·
        exact (bud3A_r c (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
      ·
        by_cases h_sb : G.Adj s b
        ·
          by_cases h_pd : G.Adj p d
          ·
            by_cases h_pb : G.Adj p b
            ·
              by_cases h_qb : G.Adj q b
              ·
                by_cases h_sd : G.Adj s d
                ·
                  by_cases h_qd : G.Adj q d
                  ·
                    by_cases h_pc : G.Adj p c
                    ·
                      by_cases h_pa : G.Adj p a
                      ·
                        exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        by_cases h_sc : G.Adj s c
                        ·
                          by_cases h_qc : G.Adj q c
                          ·
                            by_cases h_qa : G.Adj q a
                            ·
                              exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              by_cases h_sa : G.Adj s a
                              ·
                                by_cases h_rd : G.Adj r d
                                ·
                                  exact (bud3B_r a (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                                ·
                                  have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {a, b} from hA)
                                  have hB' := (show H.B = {c, d} from hB)
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                              ·
                                exact (hA1.2.1 (paw_wke G H (show H.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {a, b} from hA) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                          ·
                            have hC' := (show H.swap.C = {s, q, p, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                        ·
                          have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                    ·
                      by_cases h_qc : G.Adj q c
                      ·
                        by_cases h_qa : G.Adj q a
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          by_cases h_sc : G.Adj s c
                          ·
                            have hC' := (show H.swap.C = {s, p, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                          ·
                            have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {a, b} from hA)
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                      ·
                        by_cases h_sc : G.Adj s c
                        ·
                          have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                        ·
                          exact (hA1.2.2.2 (paw_wke G H.swap (show H.swap.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {c, d} from hB) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                  ·
                    have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {a, b} from hA)
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
              ·
                by_cases h_qd : G.Adj q d
                ·
                  have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_qc : G.Adj q c
                  ·
                    have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
          ·
            by_cases h_qd : G.Adj q d
            ·
              by_cases h_qb : G.Adj q b
              ·
                by_cases h_sd : G.Adj s d
                ·
                  have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {a, b} from hA)
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  by_cases h_pb : G.Adj p b
                  ·
                    have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                  ·
                    by_cases h_rd : G.Adj r d
                    ·
                      exact (bud3B_r a (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                    ·
                      have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                      have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
              ·
                have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_sd : G.Adj s d
              ·
                by_cases h_pb : G.Adj p b
                ·
                  have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {a, b} from hA)
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_rd : G.Adj r d
                ·
                  exact (bud3B_r a (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    by_cases h_qc : G.Adj q c
                    ·
                      by_cases h_cd : G.Adj c d
                      ·
                        have hC' := (show H.swap.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent))
                      ·
                        exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {c, d} from hB) (core_iso G (show H.swap.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                    ·
                      exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
        ·
          by_cases h_sd : G.Adj s d
          ·
            by_cases h_pb : G.Adj p b
            ·
              have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_qb : G.Adj q b
              ·
                have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                by_cases h_sa : G.Adj s a
                ·
                  by_cases h_ab : G.Adj a b
                  ·
                    by_cases h_pa : G.Adj p a
                    ·
                      by_cases h_qa : G.Adj q a
                      ·
                        by_cases h_rd : G.Adj r d
                        ·
                          exact (bud3B_r a (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent)
                      ·
                        exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (priv_isolated_edge G H hA1 (show H.A = {a, b} from hA) (core_iso G (show H.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                ·
                  exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_sc : G.Adj s c
            ·
              by_cases h_rd : G.Adj r d
              ·
                exact (bud3B_r a (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
              ·
                by_cases h_pb : G.Adj p b
                ·
                  have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {c, d} from hB)
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_qb : G.Adj q b
                  ·
                    have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    by_cases h_sa : G.Adj s a
                    ·
                      by_cases h_pd : G.Adj p d
                      ·
                        have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_qd : G.Adj q d
                        ·
                          have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {a, b} from hA)
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                        ·
                          by_cases h_pa : G.Adj p a
                          ·
                            have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD3 specD3_ok (by simp only [specD3]; spec_present) (by simp only [specD3]; spec_absent)
                          ·
                            exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              exact absurd (sB s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
    ·
      by_cases h_rd : G.Adj r d
      ·
        by_cases h_sc : G.Adj s c
        ·
          by_cases h_pb : G.Adj p b
          ·
            by_cases h_pc : G.Adj p c
            ·
              by_cases h_qc : G.Adj q c
              ·
                by_cases h_sb : G.Adj s b
                ·
                  by_cases h_qb : G.Adj q b
                  ·
                    by_cases h_pa : G.Adj p a
                    ·
                      by_cases h_pd : G.Adj p d
                      ·
                        exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        by_cases h_sa : G.Adj s a
                        ·
                          by_cases h_qa : G.Adj q a
                          ·
                            by_cases h_qd : G.Adj q d
                            ·
                              exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              by_cases h_rb : G.Adj r b
                              ·
                                exact (bud3A_r d (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                              ·
                                by_cases h_sd : G.Adj s d
                                ·
                                  have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                                  have hB' := (show H.swap.B = {a, b} from hA)
                                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                                ·
                                  exact (hA1.2.2.2 (paw_wke G H.swap (show H.swap.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                          ·
                            have hC' := (show H.C = {s, q, p, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                        ·
                          have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                    ·
                      by_cases h_qa : G.Adj q a
                      ·
                        by_cases h_qd : G.Adj q d
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          by_cases h_sa : G.Adj s a
                          ·
                            have hC' := (show H.C = {s, p, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {c, d} from hB)
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                          ·
                            have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                      ·
                        by_cases h_sa : G.Adj s a
                        ·
                          have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {a, b} from hA)
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                        ·
                          exact (hA1.2.1 (paw_wke G H (show H.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {a, b} from hA) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                  ·
                    have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                ·
                  have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
              ·
                by_cases h_qb : G.Adj q b
                ·
                  have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {c, d} from hB)
                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                ·
                  by_cases h_qa : G.Adj q a
                  ·
                    have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.swap.A = {c, d} from hB)
              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
          ·
            by_cases h_qb : G.Adj q b
            ·
              by_cases h_qc : G.Adj q c
              ·
                by_cases h_sb : G.Adj s b
                ·
                  have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                    have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                  ·
                    by_cases h_rb : G.Adj r b
                    ·
                      exact (bud3A_r d (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                    ·
                      have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.swap.A = {c, d} from hB)
                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
            ·
              by_cases h_sb : G.Adj s b
              ·
                by_cases h_pc : G.Adj p c
                ·
                  have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_rb : G.Adj r b
                ·
                  exact (bud3A_r d (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    by_cases h_qa : G.Adj q a
                    ·
                      by_cases h_ab : G.Adj a b
                      ·
                        have hC' := (show H.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {a, b} from hA)
                        have hB' := (show H.B = {c, d} from hB)
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent)
                      ·
                        exact absurd (priv_isolated_edge G H hA1 (show H.A = {a, b} from hA) (core_iso G (show H.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                    ·
                      exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
        ·
          by_cases h_sb : G.Adj s b
          ·
            by_cases h_pc : G.Adj p c
            ·
              have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.swap.A = {c, d} from hB)
              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
            ·
              by_cases h_qc : G.Adj q c
              ·
                have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.swap.A = {c, d} from hB)
                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
              ·
                by_cases h_sd : G.Adj s d
                ·
                  by_cases h_rb : G.Adj r b
                  ·
                    exact (bud3A_r d (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                  ·
                    by_cases h_pd : G.Adj p d
                    ·
                      by_cases h_qd : G.Adj q d
                      ·
                        by_cases h_cd : G.Adj c d
                        ·
                          have hC' := (show H.swap.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent))
                        ·
                          exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (core_iso G (show H.swap.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                      ·
                        exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  exact absurd (sB s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_sa : G.Adj s a
            ·
              by_cases h_rb : G.Adj r b
              ·
                exact (bud3A_r d (by rw [hB]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
              ·
                by_cases h_pc : G.Adj p c
                ·
                  have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {c, d} from hB)
                  have hB' := (show H.swap.B = {a, b} from hA)
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                ·
                  by_cases h_qc : G.Adj q c
                  ·
                    have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_sd : G.Adj s d
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                        have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                        exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                      ·
                        by_cases h_qb : G.Adj q b
                        ·
                          have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                        ·
                          by_cases h_pa : G.Adj p a
                          ·
                            have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {a, b} from hA)
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD3 specD3_ok (by simp only [specD3]; spec_present) (by simp only [specD3]; spec_absent)
                          ·
                            exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sB s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
      ·
        exact absurd (sB r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
  ·
    by_cases h_sa : G.Adj s a
    ·
      by_cases h_rb : G.Adj r b
      ·
        by_cases h_rc : G.Adj r c
        ·
          by_cases h_pd : G.Adj p d
          ·
            by_cases h_pa : G.Adj p a
            ·
              by_cases h_qa : G.Adj q a
              ·
                by_cases h_sd : G.Adj s d
                ·
                  by_cases h_qd : G.Adj q d
                  ·
                    by_cases h_pc : G.Adj p c
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                      ·
                        by_cases h_sc : G.Adj s c
                        ·
                          by_cases h_qc : G.Adj q c
                          ·
                            by_cases h_qb : G.Adj q b
                            ·
                              exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              by_cases h_sb : G.Adj s b
                              ·
                                by_cases h_rd : G.Adj r d
                                ·
                                  exact (bud3B_r b (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                                ·
                                  have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                                  have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                                  have hB' := (show H.B = {c, d} from hB)
                                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                              ·
                                exact (hA1.2.1 (paw_wke G H (show H.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                          ·
                            have hC' := (show H.swap.C = {s, q, p, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {a, b} from hA)
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                        ·
                          have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                    ·
                      by_cases h_qc : G.Adj q c
                      ·
                        by_cases h_qb : G.Adj q b
                        ·
                          exact (bud_q ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                        ·
                          by_cases h_sc : G.Adj s c
                          ·
                            have hC' := (show H.swap.C = {s, p, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {a, b} from hA)
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                          ·
                            have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {c, d} from hB)
                            have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                      ·
                        by_cases h_sc : G.Adj s c
                        ·
                          have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {c, d} from hB)
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                        ·
                          exact (hA1.2.2.2 (paw_wke G H.swap (show H.swap.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {c, d} from hB) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                  ·
                    have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                    have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
              ·
                by_cases h_qd : G.Adj q d
                ·
                  have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {a, b} from hA)
                  have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                ·
                  by_cases h_qc : G.Adj q c
                  ·
                    have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
            ·
              have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {a, b} from hA)
              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
          ·
            by_cases h_qd : G.Adj q d
            ·
              by_cases h_qa : G.Adj q a
              ·
                by_cases h_sd : G.Adj s d
                ·
                  have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  by_cases h_pa : G.Adj p a
                  ·
                    have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                    have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                  ·
                    by_cases h_rd : G.Adj r d
                    ·
                      exact (bud3B_r b (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                    ·
                      have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
              ·
                have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {a, b} from hA)
                have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_sd : G.Adj s d
              ·
                by_cases h_pa : G.Adj p a
                ·
                  have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                  have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                  exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_rd : G.Adj r d
                ·
                  exact (bud3B_r b (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    by_cases h_qc : G.Adj q c
                    ·
                      by_cases h_cd : G.Adj c d
                      ·
                        have hC' := (show H.swap.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent))
                      ·
                        exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {c, d} from hB) (core_iso G (show H.swap.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                    ·
                      exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
        ·
          by_cases h_sc : G.Adj s c
          ·
            by_cases h_pa : G.Adj p a
            ·
              by_cases h_qc : G.Adj q c
              ·
                by_cases h_qa : G.Adj q a
                ·
                  by_cases h_sd : G.Adj s d
                  ·
                    by_cases h_pc : G.Adj p c
                    ·
                      by_cases h_rd : G.Adj r d
                      ·
                        by_cases h_sb : G.Adj s b
                        ·
                          by_cases h_pb : G.Adj p b
                          ·
                            by_cases h_pd : G.Adj p d
                            ·
                              exact (bud_p ⟨by assumption, by assumption, by assumption, by assumption⟩).elim
                            ·
                              have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                              have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                          ·
                            have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                        ·
                          by_cases h_pb : G.Adj p b
                          ·
                            have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                          ·
                            by_cases h_qb : G.Adj q b
                            ·
                              have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                              have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                            ·
                              exact (hA1.2.1 (paw_wke G H (show H.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                      ·
                        exact absurd (sB r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {a, b} from hA)
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                  ·
                    by_cases h_rd : G.Adj r d
                    ·
                      by_cases h_pc : G.Adj p c
                      ·
                        by_cases h_pd : G.Adj p d
                        ·
                          have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                          have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                          exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                        ·
                          by_cases h_qd : G.Adj q d
                          ·
                            have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                            have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                            exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
                          ·
                            exact (hA1.2.2.2 (paw_wke G H.swap (show H.swap.C = {r, p, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)))) (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact SimpleGraph.adj_symm _ (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption)))).elim
                      ·
                        have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      exact absurd (sB r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                  have hA' := (show H.A = {a, b} from hA)
                  have hB' := (show H.B = {c, d} from hB)
                  exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.swap.A = {c, d} from hB)
                have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent))
            ·
              by_cases h_rd : G.Adj r d
              ·
                by_cases h_qa : G.Adj q a
                ·
                  by_cases h_qc : G.Adj q c
                  ·
                    have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specP4 specP4_ok (by simp only [specP4]; spec_present) (by simp only [specP4]; spec_absent)
                  ·
                    have hC' := (show H.swap.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.swap.A = {c, d} from hB)
                    have hB' := (show H.swap.B = {a, b} from hA)
                    exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                ·
                  by_cases h_pc : G.Adj p c
                  ·
                    have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                    have hA' := (show H.A = {a, b} from hA)
                    have hB' := (show H.B = {c, d} from hB)
                    exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                  ·
                    by_cases h_qc : G.Adj q c
                    ·
                      have hC' := (show H.C = {s, q, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.A = {a, b} from hA)
                      have hB' := (show H.B = {c, d} from hB)
                      exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        have hC' := (show H.swap.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                exact absurd (sB r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            by_cases h_pc : G.Adj p c
            ·
              have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.swap.A = {c, d} from hB)
              have hB' := (show H.swap.B = {a, b} from hA)
              exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
            ·
              by_cases h_qc : G.Adj q c
              ·
                have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.swap.A = {c, d} from hB)
                have hB' := (show H.swap.B = {a, b} from hA)
                exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
              ·
                by_cases h_sd : G.Adj s d
                ·
                  by_cases h_pd : G.Adj p d
                  ·
                    by_cases h_qd : G.Adj q d
                    ·
                      by_cases h_cd : G.Adj c d
                      ·
                        have hC' := (show H.swap.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {a, b} from hA)
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent))
                      ·
                        exact absurd (priv_isolated_edge G H.swap hA1.swap (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _))) (core_iso G (show H.swap.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                    ·
                      exact absurd (sB q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (sB p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  exact absurd (sB s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
      ·
        exact absurd (sA r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
    ·
      by_cases h_rb : G.Adj r b
      ·
        by_cases h_sc : G.Adj s c
        ·
          by_cases h_pa : G.Adj p a
          ·
            have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
            have hA' := (show H.A = {a, b} from hA)
            have hB' := (show H.B = {c, d} from hB)
            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
          ·
            by_cases h_qa : G.Adj q a
            ·
              have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {a, b} from hA)
              have hB' := (show H.B = {c, d} from hB)
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_rd : G.Adj r d
              ·
                by_cases h_sb : G.Adj s b
                ·
                  by_cases h_ab : G.Adj a b
                  ·
                    by_cases h_pb : G.Adj p b
                    ·
                      by_cases h_qb : G.Adj q b
                      ·
                        by_cases h_rc : G.Adj r c
                        ·
                          exact (bud3B_r b (by rw [hA]; simp) ⟨by assumption, by assumption, by assumption⟩).elim
                        ·
                          have hC' := (show H.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent)
                      ·
                        exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (priv_isolated_edge G H hA1 (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (core_iso G (show H.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                ·
                  exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
              ·
                by_cases h_sb : G.Adj s b
                ·
                  by_cases h_sd : G.Adj s d
                  ·
                    by_cases h_rc : G.Adj r c
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        by_cases h_qb : G.Adj q b
                        ·
                          by_cases h_ab : G.Adj a b
                          ·
                            have hC' := (show H.C = {p, s, q, r} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                            have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                            have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                            exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent)
                          ·
                            exact absurd (priv_isolated_edge G H hA1 (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (core_iso G (show H.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                        ·
                          exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (sB r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    by_cases h_pd : G.Adj p d
                    ·
                      have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                      have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      by_cases h_qd : G.Adj q d
                      ·
                        have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {d, c} from (hB.trans (pair_comm _ _)))
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_pb : G.Adj p b
                        ·
                          have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD3 specD3_ok (by simp only [specD3]; spec_present) (by simp only [specD3]; spec_absent)
                        ·
                          exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
        ·
          by_cases h_sd : G.Adj s d
          ·
            by_cases h_pa : G.Adj p a
            ·
              have hC' := (show H.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
              have hA' := (show H.A = {a, b} from hA)
              have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
              exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
            ·
              by_cases h_qa : G.Adj q a
              ·
                have hC' := (show H.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                have hA' := (show H.A = {a, b} from hA)
                have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent)
              ·
                by_cases h_rc : G.Adj r c
                ·
                  by_cases h_sb : G.Adj s b
                  ·
                    by_cases h_ab : G.Adj a b
                    ·
                      by_cases h_pb : G.Adj p b
                      ·
                        by_cases h_qb : G.Adj q b
                        ·
                          have hC' := (show H.C = {p, r, q, s} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {c, d} from hB)
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD4 specD4_ok (by simp only [specD4]; spec_present) (by simp only [specD4]; spec_absent)
                        ·
                          exact absurd (sA q (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                      ·
                        exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                    ·
                      exact absurd (priv_isolated_edge G H hA1 (show H.A = {b, a} from (hA.trans (pair_comm _ _))) (core_iso G (show H.C = {p, q, r, s} from hC) (by assumption) (by assumption) (by assumption) (by assumption))) (by first | assumption | exact fun h => absurd (SimpleGraph.adj_symm _ h) (by assumption))
                  ·
                    exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                ·
                  by_cases h_sb : G.Adj s b
                  ·
                    by_cases h_pc : G.Adj p c
                    ·
                      have hC' := (show H.swap.C = {p, s, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                      have hA' := (show H.swap.A = {c, d} from hB)
                      have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                      exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                    ·
                      by_cases h_qc : G.Adj q c
                      ·
                        have hC' := (show H.swap.C = {q, s, r, p} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                        have hA' := (show H.swap.A = {c, d} from hB)
                        have hB' := (show H.swap.B = {b, a} from (hA.trans (pair_comm _ _)))
                        exact reducible_of_swap G H (reducible_of_spec G H.swap _ (labelling_of_hub G H.swap hC' hA' hB' (diamond_h10 G H.swap hC' hA' hB')) specD1 specD1_ok (by simp only [specD1]; spec_present) (by simp only [specD1]; spec_absent))
                      ·
                        by_cases h_pb : G.Adj p b
                        ·
                          have hC' := (show H.C = {s, p, r, q} from (hC.trans (set4_eq_of (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))))
                          have hA' := (show H.A = {b, a} from (hA.trans (pair_comm _ _)))
                          have hB' := (show H.B = {d, c} from (hB.trans (pair_comm _ _)))
                          exact reducible_of_spec G H _ (labelling_of_hub G H hC' hA' hB' (diamond_h10 G H hC' hA' hB')) specD3 specD3_ok (by simp only [specD3]; spec_present) (by simp only [specD3]; spec_absent)
                        ·
                          exact absurd (sA p (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
                  ·
                    exact absurd (sA s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
          ·
            exact absurd (sB s (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hB] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)
      ·
        exact absurd (sA r (by rw [hC]; simp)) (by rintro ⟨w, hw, hadj⟩; rw [hA] at hw; simp only [mem_insert, mem_singleton] at hw; rcases hw with e | e <;> rw [e] at hadj <;> contradiction)

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
