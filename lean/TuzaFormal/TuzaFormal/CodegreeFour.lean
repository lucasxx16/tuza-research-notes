import TuzaFormal.Reducibility

/-!
# Codegree-four structural reduction (Theorem 1.3)

Setup: adjacent hubs `u, v` of degree 7 with codegree 4, core `C = N(u) ∩ N(v)`,
private sides `A, B`. Under (A1)–(A2), `{u, v}` is reducible.
-/

open Finset SimpleGraph

set_option maxHeartbeats 800000

namespace Tuza.CodegreeFour

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local data for the codegree-four configuration of Theorem 1.3. -/
structure HubConfig where
  u : V
  v : V
  huv : G.Adj u v
  C : Finset V
  A : Finset V
  B : Finset V
  hC : C = G.neighborFinset u ∩ G.neighborFinset v
  hCcard : C.card = 4
  hNu : G.neighborFinset u = insert v (C ∪ A)
  hNv : G.neighborFinset v = insert u (C ∪ B)
  hA : A.card = 2
  hB : B.card = 2
  hAdisj : Disjoint A C
  hBdisj : Disjoint B C
  hABdisj : Disjoint A B
  hvA : v ∉ A ∧ v ∉ C
  huB : u ∉ B ∧ u ∉ C
  hdu : G.degree u = 7
  hdv : G.degree v = 7

/-- Ambient link graph on `N(z)`. -/
def linkGraph (z : V) : SimpleGraph V where
  Adj a b := a ∈ G.neighborFinset z ∧ b ∈ G.neighborFinset z ∧ G.Adj a b
  symm := ⟨fun _a _b h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun a h => G.irrefl h.2.2⟩

instance linkGraph.decidable (z : V) : DecidableRel (linkGraph G z).Adj :=
  fun _ _ => by unfold linkGraph; infer_instance

namespace HubConfig

variable {G : SimpleGraph V} [DecidableRel G.Adj] (H : HubConfig G)

/-- Attachment support toward a private pair `D`. -/
def attachSupport (D : Finset V) : Finset V :=
  H.C.filter (fun c => (G.neighborFinset c ∩ D).Nonempty)

/-- Degree of `c` inside the core. -/
def coreDeg (c : V) : ℕ := ((H.C.erase c).filter (G.Adj c)).card

/-- Number of core edges. -/
def numCoreEdges : ℕ :=
  (H.C.powersetCard 2).filter (fun e => ∃ a ∈ e, ∃ b ∈ e, a ≠ b ∧ G.Adj a b) |>.card

/-- (A1) both hub links are connected and not WKE. -/
def A1 : Prop :=
  (linkGraph G H.u).Connected ∧ ¬ IsWKE (linkGraph G H.u) ∧
  (linkGraph G H.v).Connected ∧ ¬ IsWKE (linkGraph G H.v)

/-- (A2) common-neighbour degree budget. -/
def A2 : Prop :=
  ∀ x ∈ H.C,
    H.coreDeg x + (G.neighborFinset x ∩ H.A).card + (G.neighborFinset x ∩ H.B).card ≤ 5

/-- Lemma 2.2 (edge-count half): a 4-vertex core has at most 6 edges. -/
theorem core_edge_bound : H.numCoreEdges ≤ 6 := by
  have hle : H.numCoreEdges ≤ (H.C.powersetCard 2).card := card_le_card (filter_subset _ _)
  have : (H.C.powersetCard 2).card = 6 := by
    rw [card_powersetCard, H.hCcard]; decide
  omega

end HubConfig

/-- Puleo's consequence used by the exclusions ([1, Cor 4.12]): a connected graph on
`n ≥ 6` vertices with an independent set of size `n − 3` is WKE.
Taken as an axiom pending a formalization of Puleo's paper. -/
axiom puleo_large_indep {α : Type*} [Fintype α] [DecidableEq α]
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (hn : 6 ≤ Fintype.card α) (hconn : F.Connected)
    (I : Finset α) (hI : I.card = Fintype.card α - 3)
    (hind : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ F.Adj a b) :
    IsWKE F


/-! ## Constructive WKE witnesses for Proposition 3.1 -/

namespace Prop31

lemma link_edge (hub a b : V)
    (ha : a ∈ G.neighborFinset hub) (hb : b ∈ G.neighborFinset hub) (hab : G.Adj a b) :
    s(a, b) ∈ (linkGraph G hub).edgeFinset := by
  rw [mem_edgeFinset]; exact ⟨ha, hb, hab⟩

private lemma tf {a b : V} : s(a, b).toFinset = {a, b} := Sym2.toFinset_mk_eq

private lemma disj4 {a b c d : V}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint s(a, b).toFinset s(c, d).toFinset := by
  simp [tf, Finset.disjoint_iff_ne, hac, had, hbc, hbd]

structure SixDistinct (z p q r d0 d1 : V) : Prop where
  zp : z ≠ p
  zq : z ≠ q
  zr : z ≠ r
  zd0 : z ≠ d0
  zd1 : z ≠ d1
  pq : p ≠ q
  pr : p ≠ r
  pd0 : p ≠ d0
  pd1 : p ≠ d1
  qr : q ≠ r
  qd0 : q ≠ d0
  qd1 : q ≠ d1
  rd0 : r ≠ d0
  rd1 : r ≠ d1
  d01 : d0 ≠ d1

private lemma sym2_ne_of_disj {a b c d : V}
    (h : Disjoint s(a, b).toFinset s(c, d).toFinset) : s(a, b) ≠ s(c, d) := by
  intro heq
  have ha : a ∈ s(a, b).toFinset := by simp [tf]
  exact Finset.disjoint_left.1 h ha (by simpa [congrArg Sym2.toFinset heq] using ha)

private lemma card3_vertices {z d0 d1 : V} (zd0 : z ≠ d0) (zd1 : z ≠ d1) (d01 : d0 ≠ d1) :
    ({z, d0, d1} : Finset V).card = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton] <;> simp [zd0, zd1, d01]

private lemma card3_edges {e f g : Sym2 V} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ({e, f, g} : Finset (Sym2 V)).card = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton] <;> simp [hef, heg, hfg]

/-- Case: unique core edge `pq`, private edge present. -/
theorem wke_private_edge (hub z p q r d0 d1 : V)
    (D : SixDistinct z p q r d0 d1)
    (hpq : G.Adj p q) (hd01 : G.Adj d0 d1) (hzr : G.Adj z r)
    (hN : ({z, p, q, r, d0, d1} : Finset V) ⊆ G.neighborFinset hub)
    (honly : ∀ e ∈ (linkGraph G hub).edgeFinset,
      (∀ x ∈ e, x ∉ ({z, d0, d1} : Finset V)) → e = s(p, q)) :
    IsWKEWitness (linkGraph G hub)
      ({s(p, q), s(d0, d1), s(z, r)} : Finset (Sym2 V))
      ({z, d0, d1} : Finset V) := by
  have hz : z ∈ G.neighborFinset hub := hN (by simp)
  have hp : p ∈ G.neighborFinset hub := hN (by simp)
  have hq : q ∈ G.neighborFinset hub := hN (by simp)
  have hr : r ∈ G.neighborFinset hub := hN (by simp)
  have h0 : d0 ∈ G.neighborFinset hub := hN (by simp)
  have h1 : d1 ∈ G.neighborFinset hub := hN (by simp)
  have d1j := disj4 (a := p) (b := q) (c := d0) (d := d1) D.pd0 D.pd1 D.qd0 D.qd1
  have d2j := disj4 (a := p) (b := q) (c := z) (d := r) D.zp.symm D.pr D.zq.symm D.qr
  have d3j := disj4 (a := d0) (b := d1) (c := z) (d := r)
    D.zd0.symm D.rd0.symm D.zd1.symm D.rd1.symm
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro e he; simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact link_edge G hub p q hp hq hpq
    · exact link_edge G hub d0 d1 h0 h1 hd01
    · exact link_edge G hub z r hz hr hzr
  · intro e he f hf hne
    simp only [mem_insert, mem_singleton] at he hf
    rcases he with he | he | he <;> rcases hf with hf | hf | hf
    · subst he; subst hf; exact absurd rfl hne
    · subst he; subst hf; exact d1j
    · subst he; subst hf; exact d2j
    · subst he; subst hf; exact d1j.symm
    · subst he; subst hf; exact absurd rfl hne
    · subst he; subst hf; exact d3j
    · subst he; subst hf; exact d2j.symm
    · subst he; subst hf; exact d3j.symm
    · subst he; subst hf; exact absurd rfl hne
  · exact Nat.le_of_eq (by
      rw [card3_vertices D.zd0 D.zd1 D.d01,
        card3_edges (sym2_ne_of_disj d1j) (sym2_ne_of_disj d2j) (sym2_ne_of_disj d3j)])
  · intro e he hQ; simp [honly e he hQ]

/-- Case: attachment `r–d₀`, no private edge. -/
theorem wke_private_attach (hub z p q r s d0 d1 : V)
    (D : SixDistinct z p q r d0 d1)
    (hsN : s ∈ G.neighborFinset hub)
    (sz : s ≠ z) (sp : s ≠ p) (sq : s ≠ q) (sr : s ≠ r) (sd0 : s ≠ d0) (_sd1 : s ≠ d1)
    (hpq : G.Adj p q) (hrd0 : G.Adj r d0) (hzs : G.Adj z s)
    (hN : ({z, p, q, r, d0, d1} : Finset V) ⊆ G.neighborFinset hub)
    (honly : ∀ e ∈ (linkGraph G hub).edgeFinset,
      (∀ x ∈ e, x ∉ ({z, d0, d1} : Finset V)) → e = s(p, q) ∨ e = s(r, d0)) :
    IsWKEWitness (linkGraph G hub)
      ({s(p, q), s(r, d0), s(z, s)} : Finset (Sym2 V))
      ({z, d0, d1} : Finset V) := by
  have hz : z ∈ G.neighborFinset hub := hN (by simp)
  have hp : p ∈ G.neighborFinset hub := hN (by simp)
  have hq : q ∈ G.neighborFinset hub := hN (by simp)
  have hr : r ∈ G.neighborFinset hub := hN (by simp)
  have h0 : d0 ∈ G.neighborFinset hub := hN (by simp)
  have d1j := disj4 (a := p) (b := q) (c := r) (d := d0) D.pr D.pd0 D.qr D.qd0
  have d2j := disj4 (a := p) (b := q) (c := z) (d := s) D.zp.symm sp.symm D.zq.symm sq.symm
  have d3j := disj4 (a := r) (b := d0) (c := z) (d := s) D.zr.symm sr.symm D.zd0.symm sd0.symm
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro e he; simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact link_edge G hub p q hp hq hpq
    · exact link_edge G hub r d0 hr h0 hrd0
    · exact link_edge G hub z s hz hsN hzs
  · intro e he f hf hne
    simp only [mem_insert, mem_singleton] at he hf
    rcases he with he | he | he <;> rcases hf with hf | hf | hf
    · subst he; subst hf; exact absurd rfl hne
    · subst he; subst hf; exact d1j
    · subst he; subst hf; exact d2j
    · subst he; subst hf; exact d1j.symm
    · subst he; subst hf; exact absurd rfl hne
    · subst he; subst hf; exact d3j
    · subst he; subst hf; exact d2j.symm
    · subst he; subst hf; exact d3j.symm
    · subst he; subst hf; exact absurd rfl hne
  · exact Nat.le_of_eq (by
      rw [card3_vertices D.zd0 D.zd1 D.d01,
        card3_edges (sym2_ne_of_disj d1j) (sym2_ne_of_disj d2j) (sym2_ne_of_disj d3j)])
  · intro e he hQ; rcases honly e he hQ with h | h <;> simp [h]

/-- Unique core edge when `numCoreEdges = 1`. -/
lemma exists_unique_core_edge (H : HubConfig G) (h1 : H.numCoreEdges = 1) :
    ∃ p q, p ∈ H.C ∧ q ∈ H.C ∧ p ≠ q ∧ G.Adj p q ∧
      (∀ x ∈ H.C, ∀ y ∈ H.C, x ≠ y → G.Adj x y → s(x, y) = s(p, q)) := by
  classical
  unfold HubConfig.numCoreEdges at h1
  obtain ⟨e, heq⟩ := (card_eq_one.1 h1)
  have he : e ∈ (H.C.powersetCard 2).filter
      (fun t => ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧ G.Adj a b) := by simp [heq]
  obtain ⟨hep, ⟨a, ha, b, hb, hab, hAdj⟩⟩ := mem_filter.1 he
  have hsub := (mem_powersetCard.1 hep).1
  refine ⟨a, b, hsub ha, hsub hb, hab, hAdj, ?_⟩
  intro x hx y hy hxy hxyAdj
  have hedge : ({x, y} : Finset V) ∈
      (H.C.powersetCard 2).filter (fun t => ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧ G.Adj u v) := by
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨by
      intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption,
      by simp [card_insert_of_notMem, hxy]⟩,
      ⟨x, by simp, y, by simp, hxy, hxyAdj⟩⟩
  have hxe : ({x, y} : Finset V) = e := by simpa [heq] using hedge
  have hab_e : ({a, b} : Finset V) = e := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [(mem_powersetCard.1 hep).2]; simp [card_insert_of_notMem, hab]
  have hpair : ({x, y} : Finset V) = ({a, b} : Finset V) := hxe.trans hab_e.symm
  have hxab : x = a ∨ x = b := by
    have : x ∈ ({a, b} : Finset V) := by simp [← hpair]
    simpa using this
  have hyab : y = a ∨ y = b := by
    have : y ∈ ({a, b} : Finset V) := by simp [← hpair]
    simpa using this
  rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl
  · exact absurd rfl hxy
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hxy

/-- From HubConfig + connectedness of the u-link: `|V| = 7`. -/
lemma card_of_link_connected (H : HubConfig G)
    (hconn : (linkGraph G H.u).Connected) : Fintype.card V = 7 := by
  have hNcard : (G.neighborFinset H.u).card = 7 := by
    simpa [← SimpleGraph.card_neighborFinset_eq_degree] using H.hdu
  have hNu_univ : G.neighborFinset H.u = univ := by
    ext w; simp only [mem_univ, iff_true]
    by_contra hw
    have hdeg0 : (linkGraph G H.u).degree w = 0 := by
      simp only [← card_neighborFinset_eq_degree]
      refine card_eq_zero.2 (eq_empty_iff_forall_notMem.2 ?_)
      intro x hx
      exact hw ((mem_neighborFinset _ _ _).1 hx).1
    obtain ⟨x, hx⟩ : (G.neighborFinset H.u).Nonempty := by
      rw [← card_pos, hNcard]; omega
    have hxne : w ≠ x := fun heq => hw (heq ▸ hx)
    exact (not_reachable_of_left_degree_zero hxne hdeg0) (hconn.preconnected w x)
  calc Fintype.card V = (univ : Finset V).card := by simp [card_univ]
    _ = (G.neighborFinset H.u).card := by rw [hNu_univ]
    _ = 7 := hNcard

private lemma mem_C_of_N_not_QA (H : HubConfig G) {d0 d1 a : V}
    (hAeq : H.A = {d0, d1})
    (haN : a ∈ G.neighborFinset H.u)
    (haQ : a ∉ ({H.v, d0, d1} : Finset V)) : a ∈ H.C := by
  rw [H.hNu] at haN
  simp only [mem_insert, mem_union] at haN
  rcases haN with rfl | hC | hA
  · exact absurd (by simp) haQ
  · exact hC
  · have : a = d0 ∨ a = d1 := by rw [hAeq] at hA; simpa using hA
    exact absurd (by rcases this with rfl | rfl <;> simp) haQ

/-- Edges of the u-link with both ends outside `Q = {v} ∪ A` are exactly the unique core edge. -/
lemma only_core_edge_outside_Q (H : HubConfig G)
    {p q d0 d1 : V}
    (hAeq : H.A = {d0, d1})
    (hunique : ∀ x ∈ H.C, ∀ y ∈ H.C, x ≠ y → G.Adj x y → s(x, y) = s(p, q)) :
    ∀ e ∈ (linkGraph G H.u).edgeFinset,
      (∀ x ∈ e, x ∉ ({H.v, d0, d1} : Finset V)) → e = s(p, q) := by
  intro e he hQ
  revert he hQ
  refine Sym2.inductionOn e fun a b he hQ => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hGAdj : G.Adj a b := hab.2.2
  have hne : a ≠ b := fun h => G.irrefl (h ▸ hGAdj)
  have haC := mem_C_of_N_not_QA G H hAeq hab.1 (hQ a (by simp))
  have hbC := mem_C_of_N_not_QA G H hAeq hab.2.1 (hQ b (by simp))
  exact hunique a haC b hbC hne hGAdj

/-- Independence of `{r,s,d0,d1}` in the one-edge/no-attach case. -/
lemma indep_rest_core_priv (H : HubConfig G)
    {p q r s d0 d1 : V}
    (hpC : p ∈ H.C) (hqC : q ∈ H.C) (hrC : r ∈ H.C) (hsC : s ∈ H.C)
    (hAeq : H.A = {d0, d1})
    (hunique : ∀ x ∈ H.C, ∀ y ∈ H.C, x ≠ y → G.Adj x y → s(x, y) = s(p, q))
    (hrne : r ∉ ({p, q} : Finset V)) (hsne : s ∉ ({p, q} : Finset V))
    (hpriv : ¬ G.Adj d0 d1)
    (hr_no : ¬ G.Adj r d0 ∧ ¬ G.Adj r d1)
    (hs_no : ¬ G.Adj s d0 ∧ ¬ G.Adj s d1) :
    ∀ a ∈ ({r, s, d0, d1} : Finset V), ∀ b ∈ ({r, s, d0, d1} : Finset V),
      a ≠ b → ¬ (linkGraph G H.u).Adj a b := by
  intro a ha b hb hab hAdj
  have hG : G.Adj a b := hAdj.2.2
  have ha' : a = r ∨ a = s ∨ a = d0 ∨ a = d1 := by
    simpa [mem_insert, mem_singleton] using ha
  have hb' : b = r ∨ b = s ∨ b = d0 ∨ b = d1 := by
    simpa [mem_insert, mem_singleton] using hb
  rcases ha' with (har | has | had0 | had1) <;> rcases hb' with (hbr | hbs | hbd0 | hbd1)
  · exact absurd (har.trans hbr.symm) hab
  · -- a=r, b=s
    have hem := hunique a (har ▸ hrC) b (hbs ▸ hsC) hab hG
    have : a = p ∨ a = q := by
      have : a ∈ s(p, q) := by
        simpa [hem] using (Sym2.mem_mk_left a b : a ∈ s(a, b))
      simpa [Sym2.mem_iff] using this
    exact hrne (by simpa [mem_insert, mem_singleton, ← har] using this)
  · -- a=r, b=d0
    have : G.Adj r d0 := by rw [← har, ← hbd0]; exact hG
    exact hr_no.1 this
  · have : G.Adj r d1 := by rw [← har, ← hbd1]; exact hG
    exact hr_no.2 this
  · -- a=s, b=r
    have hem := hunique a (has ▸ hsC) b (hbr ▸ hrC) hab hG
    have : a = p ∨ a = q := by
      have : a ∈ s(p, q) := by
        simpa [hem] using (Sym2.mem_mk_left a b : a ∈ s(a, b))
      simpa [Sym2.mem_iff] using this
    exact hsne (by simpa [mem_insert, mem_singleton, ← has] using this)
  · exact absurd (has.trans hbs.symm) hab
  · have : G.Adj s d0 := by rw [← has, ← hbd0]; exact hG
    exact hs_no.1 this
  · have : G.Adj s d1 := by rw [← has, ← hbd1]; exact hG
    exact hs_no.2 this
  · have : G.Adj r d0 := by rw [← hbr, ← had0]; exact hG.symm
    exact hr_no.1 this
  · have : G.Adj s d0 := by rw [← hbs, ← had0]; exact hG.symm
    exact hs_no.1 this
  · exact absurd (had0.trans hbd0.symm) hab
  · have : G.Adj d0 d1 := by rw [← had0, ← hbd1]; exact hG
    exact hpriv this
  · have : G.Adj r d1 := by rw [← hbr, ← had1]; exact hG.symm
    exact hr_no.2 this
  · have : G.Adj s d1 := by rw [← hbs, ← had1]; exact hG.symm
    exact hs_no.2 this
  · have : G.Adj d0 d1 := by rw [← hbd0, ← had1]; exact hG.symm
    exact hpriv this
  · exact absurd (had1.trans hbd1.symm) hab

/-- **Prop 3.1, one-edge case:** unique core edge ⇒ the u-link is WKE. -/
theorem one_edge_is_wke (H : HubConfig G)
    (hconn : (linkGraph G H.u).Connected) (h1 : H.numCoreEdges = 1) :
    IsWKE (linkGraph G H.u) := by
  classical
  obtain ⟨p, q, hpC, hqC, hpq, hpqAdj, hunique⟩ := exists_unique_core_edge G H h1
  obtain ⟨d0, d1, hd01, hAeq⟩ := (card_eq_two (s := H.A)).1 H.hA
  have hV := card_of_link_connected G H hconn
  set z := H.v with hzdef
  have hpqC : ({p, q} : Finset V) ⊆ H.C := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have hrest_card : (H.C \ {p, q}).card = 2 := by
    have hinter : {p, q} ∩ H.C = {p, q} := by
      rw [inter_comm]; exact inter_eq_right.2 hpqC
    rw [card_sdiff, hinter, H.hCcard]
    simp [card_insert_of_notMem, hpq]
  obtain ⟨r, s, hrs, hRest⟩ := (card_eq_two (s := H.C \ {p, q})).1 hrest_card
  have hrC : r ∈ H.C := (mem_sdiff.1 (by rw [hRest]; exact mem_insert_self _ _)).1
  have hsC : s ∈ H.C := (mem_sdiff.1 (by rw [hRest]; simp)).1
  have hrne : r ∉ ({p, q} : Finset V) :=
    (mem_sdiff.1 (by rw [hRest]; exact mem_insert_self _ _)).2
  have hsne : s ∉ ({p, q} : Finset V) :=
    (mem_sdiff.1 (by rw [hRest]; simp)).2
  have hzC : z ∉ H.C := H.hvA.2
  have hzA : z ∉ H.A := H.hvA.1
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have D : SixDistinct z p q r d0 d1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hpq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hd01⟩
    · intro h; subst h; exact hzC hpC
    · intro h; subst h; exact hzC hqC
    · intro h; subst h; exact hzC hrC
    · intro h; subst h; exact hzA hd0A
    · intro h; subst h; exact hzA hd1A
    · intro h; subst h; exact hrne (by simp)
    · intro h; subst h; exact absurd hpC (Finset.disjoint_left.1 H.hAdisj hd0A)
    · intro h; subst h; exact absurd hpC (Finset.disjoint_left.1 H.hAdisj hd1A)
    · intro h; subst h; exact hrne (by simp)
    · intro h; subst h; exact absurd hqC (Finset.disjoint_left.1 H.hAdisj hd0A)
    · intro h; subst h; exact absurd hqC (Finset.disjoint_left.1 H.hAdisj hd1A)
    · intro h; subst h; exact absurd hrC (Finset.disjoint_left.1 H.hAdisj hd0A)
    · intro h; subst h; exact absurd hrC (Finset.disjoint_left.1 H.hAdisj hd1A)
  have hs_ne_z : s ≠ z := by intro h; subst h; exact hzC hsC
  have hs_ne_p : s ≠ p := by intro h; subst h; exact hsne (by simp)
  have hs_ne_q : s ≠ q := by intro h; subst h; exact hsne (by simp)
  have hs_ne_r : s ≠ r := hrs.symm
  have hs_ne_d0 : s ≠ d0 := by intro h; subst h; exact absurd hsC (Finset.disjoint_left.1 H.hAdisj hd0A)
  have hs_ne_d1 : s ≠ d1 := by intro h; subst h; exact absurd hsC (Finset.disjoint_left.1 H.hAdisj hd1A)
  have hCN : ∀ c ∈ H.C, c ∈ G.neighborFinset H.u := fun c hc => by
    rw [H.hNu]; exact mem_insert_of_mem (mem_union_left _ hc)
  have hzN : z ∈ G.neighborFinset H.u := by rw [H.hNu]; exact mem_insert_self _ _
  have hd0N : d0 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hd1N : d1 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hN6 : ({z, p, q, r, d0, d1} : Finset V) ⊆ G.neighborFinset H.u := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h | h | h | h
    · rw [h]; exact hzN
    · rw [h]; exact hCN p hpC
    · rw [h]; exact hCN q hqC
    · rw [h]; exact hCN r hrC
    · rw [h]; exact hd0N
    · rw [h]; exact hd1N
  have hz_adj (c : V) (hc : c ∈ H.C) : G.Adj z c := by
    have : c ∈ G.neighborFinset z := (mem_inter.1 (H.hC ▸ hc)).2
    exact (G.mem_neighborFinset _ _).1 this
  have honly := only_core_edge_outside_Q G H hAeq hunique
  by_cases hpriv : G.Adj d0 d1
  · exact isWKE_of_witness _
      (wke_private_edge G H.u z p q r d0 d1 D hpqAdj hpriv (hz_adj r hrC) hN6 honly)
  by_cases hr0 : G.Adj r d0
  · have honly' : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d0, d1} : Finset V)) →
          e = s(p, q) ∨ e = s(r, d0) := fun e he hQ => Or.inl (honly e he hQ)
    exact isWKE_of_witness _
      (wke_private_attach G H.u z p q r s d0 d1 D (hCN s hsC)
        hs_ne_z hs_ne_p hs_ne_q hs_ne_r hs_ne_d0 hs_ne_d1
        hpqAdj hr0 (hz_adj s hsC) hN6 honly')
  by_cases hr1 : G.Adj r d1
  · have D' : SixDistinct z p q r d1 d0 :=
      ⟨D.zp, D.zq, D.zr, D.zd1, D.zd0, D.pq, D.pr, D.pd1, D.pd0, D.qr,
        D.qd1, D.qd0, D.rd1, D.rd0, D.d01.symm⟩
    have hN6' : ({z, p, q, r, d1, d0} : Finset V) ⊆ G.neighborFinset H.u := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with h | h | h | h | h | h
      · rw [h]; exact hzN
      · rw [h]; exact hCN p hpC
      · rw [h]; exact hCN q hqC
      · rw [h]; exact hCN r hrC
      · rw [h]; exact hd1N
      · rw [h]; exact hd0N
    have honly1 : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d1, d0} : Finset V)) → e = s(p, q) := by
      intro e he hQ
      exact honly e he (fun x hx hxQ =>
        hQ x hx (by simpa [or_left_comm, or_assoc, or_comm] using hxQ))
    have honly' : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d1, d0} : Finset V)) →
          e = s(p, q) ∨ e = s(r, d1) := fun e he hQ => Or.inl (honly1 e he hQ)
    exact isWKE_of_witness _
      (wke_private_attach G H.u z p q r s d1 d0 D' (hCN s hsC)
        hs_ne_z hs_ne_p hs_ne_q hs_ne_r hs_ne_d1 hs_ne_d0
        hpqAdj hr1 (hz_adj s hsC) hN6' honly')
  by_cases hs0 : G.Adj s d0
  · have Ds : SixDistinct z p q s d0 d1 :=
      ⟨D.zp, D.zq, hs_ne_z.symm, D.zd0, D.zd1, D.pq, hs_ne_p.symm, D.pd0, D.pd1, hs_ne_q.symm,
        D.qd0, D.qd1, hs_ne_d0, hs_ne_d1, D.d01⟩
    have hN6s : ({z, p, q, s, d0, d1} : Finset V) ⊆ G.neighborFinset H.u := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with h | h | h | h | h | h
      · rw [h]; exact hzN
      · rw [h]; exact hCN p hpC
      · rw [h]; exact hCN q hqC
      · rw [h]; exact hCN s hsC
      · rw [h]; exact hd0N
      · rw [h]; exact hd1N
    have honly' : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d0, d1} : Finset V)) →
          e = s(p, q) ∨ e = s(s, d0) := fun e he hQ => Or.inl (honly e he hQ)
    exact isWKE_of_witness _
      (wke_private_attach G H.u z p q s r d0 d1 Ds (hCN r hrC)
        D.zr.symm (fun h => hrne (by simp [← h])) (fun h => hrne (by simp [h]))
        hrs D.rd0 D.rd1 hpqAdj hs0 (hz_adj r hrC) hN6s honly')
  by_cases hs1 : G.Adj s d1
  · have Ds' : SixDistinct z p q s d1 d0 :=
      ⟨D.zp, D.zq, hs_ne_z.symm, D.zd1, D.zd0, D.pq, hs_ne_p.symm, D.pd1, D.pd0, hs_ne_q.symm,
        D.qd1, D.qd0, hs_ne_d1, hs_ne_d0, D.d01.symm⟩
    have hN6s : ({z, p, q, s, d1, d0} : Finset V) ⊆ G.neighborFinset H.u := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with h | h | h | h | h | h
      · rw [h]; exact hzN
      · rw [h]; exact hCN p hpC
      · rw [h]; exact hCN q hqC
      · rw [h]; exact hCN s hsC
      · rw [h]; exact hd1N
      · rw [h]; exact hd0N
    have honly1 : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d1, d0} : Finset V)) → e = s(p, q) := by
      intro e he hQ
      exact honly e he (fun x hx hxQ =>
        hQ x hx (by simpa [or_left_comm, or_assoc, or_comm] using hxQ))
    have honly' : ∀ e ∈ (linkGraph G H.u).edgeFinset,
        (∀ x ∈ e, x ∉ ({z, d1, d0} : Finset V)) →
          e = s(p, q) ∨ e = s(s, d1) := fun e he hQ => Or.inl (honly1 e he hQ)
    exact isWKE_of_witness _
      (wke_private_attach G H.u z p q s r d1 d0 Ds' (hCN r hrC)
        D.zr.symm (fun h => hrne (by simp [← h])) (fun h => hrne (by simp [h]))
        hrs D.rd1 D.rd0 hpqAdj hs1 (hz_adj r hrC) hN6s honly')
  · -- No private edge, no attachments at r or s
    have hind := indep_rest_core_priv G H hpC hqC hrC hsC hAeq hunique hrne hsne
      hpriv ⟨hr0, hr1⟩ ⟨hs0, hs1⟩
    refine puleo_large_indep (linkGraph G H.u) (by omega) hconn
      ({r, s, d0, d1} : Finset V) ?_ hind
    have hcard : ({r, s, d0, d1} : Finset V).card = 4 := by
      simp [card_insert_of_notMem, hrs, hs_ne_d0, hs_ne_d1, D.rd0, D.rd1, D.d01]
    simp [hV, hcard]


end Prop31

/-- **Proposition 3.1.** If a hub link satisfies (A1) connectivity/non-WKE and the core has
at most one edge, contradiction. Edgeless cores use `puleo_large_indep`; one-edge cores use
`Prop31.one_edge_is_wke` (private-edge / attach / Puleo trichotomy). -/
theorem prop31 (H : HubConfig G) (hA1 : H.A1) (hle : H.numCoreEdges ≤ 1) : False := by
  have hNcard : (G.neighborFinset H.u).card = 7 := by
    simpa [← SimpleGraph.card_neighborFinset_eq_degree] using H.hdu
  obtain h0 | h1 : H.numCoreEdges = 0 ∨ H.numCoreEdges = 1 := by omega
  · -- Edgeless core ⇒ C is an independent 4-set in the link
    have hind : ∀ a ∈ H.C, ∀ b ∈ H.C, a ≠ b → ¬ (linkGraph G H.u).Adj a b := by
      intro a ha b hb hab hAdj
      have : H.numCoreEdges = 0 := h0
      have hedge : ({a, b} : Finset V) ∈
          (H.C.powersetCard 2).filter (fun e => ∃ x ∈ e, ∃ y ∈ e, x ≠ y ∧ G.Adj x y) := by
        refine mem_filter.2 ⟨?_, ⟨a, by simp, b, by simp, hab, hAdj.2.2⟩⟩
        exact mem_powersetCard.2 ⟨by
          intro z hz; simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption,
          by simp [card_insert_of_notMem, hab]⟩
      have hpos : 0 < H.numCoreEdges := by
        unfold HubConfig.numCoreEdges
        exact Finset.card_pos.2 ⟨_, hedge⟩
      omega
    have hV : Fintype.card V = 7 := by
      -- Link connectivity + deg(u)=7 ⇒ V = N(u) (no isolated vertices outside N(u))
      have hNu_univ : G.neighborFinset H.u = univ := by
        ext w; simp only [mem_univ, iff_true]
        by_contra hw
        have hdeg0 : (linkGraph G H.u).degree w = 0 := by
          simp only [← card_neighborFinset_eq_degree]
          refine card_eq_zero.2 (eq_empty_iff_forall_notMem.2 ?_)
          intro x hx
          have hAdj : (linkGraph G H.u).Adj w x := (mem_neighborFinset _ _ _).1 hx
          exact hw hAdj.1
        obtain ⟨x, hx⟩ : (G.neighborFinset H.u).Nonempty := by
          rw [← card_pos, hNcard]; omega
        have hxne : w ≠ x := fun h => hw (h ▸ hx)
        have hreach : (linkGraph G H.u).Reachable w x := hA1.1.preconnected w x
        exact (not_reachable_of_left_degree_zero hxne hdeg0) hreach
      calc Fintype.card V = (univ : Finset V).card := by simp [card_univ]
        _ = (G.neighborFinset H.u).card := by rw [hNu_univ]
        _ = 7 := hNcard
    have hWKE : IsWKE (linkGraph G H.u) :=
      puleo_large_indep (linkGraph G H.u) (by omega) hA1.1 H.C
        (by simp [hV, H.hCcard]) hind
    exact hA1.2.1 hWKE
  · have : IsWKE (linkGraph G H.u) := Prop31.one_edge_is_wke G H hA1.1 h1
    exact hA1.2.1 this


/-! ## Matching core `2K₂` (Proposition 4.2) -/

namespace MatchingCore

def packing42 (u v c0 c1 c2 c3 a0 a1 b1 : V) : Finset (Finset V) :=
  {{u, c0, c3}, {u, c1, a1}, {u, c2, a0}, {v, c0, b1}, {v, c1, c2}}

def cover42 (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, a0), s(u, a1), s(v, b0), s(v, b1),
   s(c0, c3), s(c1, c2), s(c1, a1), s(c2, a0), s(c0, b1)}

/-- The ten labelled vertices as a function on `Fin 10`. -/
def labels10 (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) : Fin 10 → V
  | ⟨0, _⟩ => u
  | ⟨1, _⟩ => v
  | ⟨2, _⟩ => c0
  | ⟨3, _⟩ => c1
  | ⟨4, _⟩ => c2
  | ⟨5, _⟩ => c3
  | ⟨6, _⟩ => a0
  | ⟨7, _⟩ => a1
  | ⟨8, _⟩ => b0
  | ⟨9, _⟩ => b1

lemma labels10_image (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) :
    (univ.image (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) =
      ({u, v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V) := by
  ext x; simp only [mem_image, mem_univ, true_and, labels10]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩

lemma labels10_injective (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (h10 : ({u, v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10) :
    Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1) := by
  classical
  have himg := labels10_image u v c0 c1 c2 c3 a0 a1 b0 b1
  -- `#image = 10 = #Fin 10` ⇒ injective
  have hcard : ((univ : Finset (Fin 10)).image
      (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)).card =
      (univ : Finset (Fin 10)).card := by
    rw [himg, h10]; rfl
  exact fun i j h =>
    (Finset.injOn_of_card_image_eq hcard) (mem_univ i) (mem_univ j) h

lemma hub_adj_CA (H : HubConfig G) {x : V} (hx : x ∈ H.C ∪ H.A) : G.Adj H.u x := by
  have : x ∈ G.neighborFinset H.u := by
    rw [H.hNu]; exact mem_insert_of_mem (by simpa using hx)
  exact (G.mem_neighborFinset _ _).1 this

lemma hub_adj_CB (H : HubConfig G) {x : V} (hx : x ∈ H.C ∪ H.B) : G.Adj H.v x := by
  have : x ∈ G.neighborFinset H.v := by
    rw [H.hNv]; exact mem_insert_of_mem (by simpa using hx)
  exact (G.mem_neighborFinset _ _).1 this

private lemma is3clique_of_adj {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hcard : ({a, b, c} : Finset V).card = 3) :
    ({a, b, c} : Finset V) ∈ G.cliqueFinset 3 := by
  rw [mem_cliqueFinset_iff, isNClique_iff]
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  simp only [mem_coe, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | assumption | exact Adj.symm ‹_›

private lemma card3_of_inj {a b c : V} {f : Fin 10 → V} (hinj : Function.Injective f)
    {i j k : Fin 10} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ha : f i = a) (hb : f j = b) (hc : f k = c) :
    ({a, b, c} : Finset V).card = 3 := by
  have ab : a ≠ b := by rw [← ha, ← hb]; exact hinj.ne hij
  have ac : a ≠ c := by rw [← ha, ← hc]; exact hinj.ne hik
  have bc : b ≠ c := by rw [← hb, ← hc]; exact hinj.ne hjk
  simp [card_insert_of_notMem, ab, ac, bc]

/-- Rim edges of the Prop 4.2 packing (the set `R` in the paper). -/
def R42 (c0 c1 c2 c3 a0 a1 b1 : V) : Finset (Sym2 V) :=
  {s(c0, c3), s(c1, c2), s(c1, a1), s(c2, a0), s(c0, b1)}

private lemma ne_of_mem_notMem {s t : Finset V} {x : V}
    (hx : x ∈ s) (hn : x ∉ t) : s ≠ t := fun h => hn (h ▸ hx)

private lemma pairwise_ne_of_card3 {α : Type*} [DecidableEq α] {a b c : α}
    (h : ({a, b, c} : Finset α).card = 3) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩
  · intro eq; subst eq
    have h' : ({a, c} : Finset α).card = 3 := by
      convert h using 2; simp [insert_eq_of_mem]
    cases' eq_or_ne a c with hac hac <;> simp [hac, card_insert_of_notMem] at h'
  · intro eq; subst eq
    have h' : ({a, b} : Finset α).card = 3 := by
      convert h using 2
      -- {a, b, a} = {a, b}
      ext x; simp [or_comm, or_assoc, or_left_comm]
    cases' eq_or_ne a b with hab hab <;> simp [hab, card_insert_of_notMem] at h'
  · intro eq; subst eq
    have h' : ({a, b} : Finset α).card = 3 := by
      convert h using 2; simp [insert_eq_of_mem]
    cases' eq_or_ne a b with hab hab <;> simp [hab, card_insert_of_notMem] at h'

/-- The three undirected edges of a 3-set. -/
lemma triEdges_eq_of_card3 {α : Type*} [DecidableEq α] {a b c : α}
    (hcard : ({a, b, c} : Finset α).card = 3) :
    triEdges ({a, b, c} : Finset α) = {s(a, b), s(a, c), s(b, c)} := by
  obtain ⟨hab, hac, hbc⟩ := pairwise_ne_of_card3 hcard
  ext e; constructor
  · intro he'
    obtain ⟨hem, hndiag⟩ := mem_filter.1 he'
    revert hem hndiag
    refine Sym2.inductionOn e fun x y hem hndiag => ?_
    have hx := Finset.mem_sym2_iff.1 hem x (Sym2.mem_mk_left x y)
    have hy := Finset.mem_sym2_iff.1 hem y (Sym2.mem_mk_right x y)
    have hxy : x ≠ y := fun h => hndiag (by simpa [Sym2.mk_isDiag_iff] using h)
    simp only [mem_insert, mem_singleton] at hx hy ⊢
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact (hxy rfl).elim | simp [Sym2.eq_swap]
  · intro he'
    simp only [mem_insert, mem_singleton] at he'
    rcases he' with rfl | rfl | rfl
    · exact mem_filter.2 ⟨by simp [hab], by simp [Sym2.mk_isDiag_iff, hab]⟩
    · exact mem_filter.2 ⟨by simp [hac], by simp [Sym2.mk_isDiag_iff, hac]⟩
    · exact mem_filter.2 ⟨by simp [hbc], by simp [Sym2.mk_isDiag_iff, hbc]⟩

/-- Edge of a triangle opposite a missing vertex. -/
lemma triEdges_omit_vertex {α : Type*} [DecidableEq α] {a b c : α} {e : Sym2 α}
    (hcard : ({a, b, c} : Finset α).card = 3)
    (he : e ∈ triEdges ({a, b, c} : Finset α)) (ha : a ∉ e) :
    e = s(b, c) := by
  rw [triEdges_eq_of_card3 hcard] at he
  simp only [mem_insert, mem_singleton] at he
  rcases he with he | he | he
  · exact absurd (by simp [he] : a ∈ e) ha
  · exact absurd (by simp [he] : a ∈ e) ha
  · exact he

/-! ### Fin-10 model of the Prop 4.2 packing/cover (decidable) -/

def packing10 : Finset (Finset (Fin 10)) :=
  {{0, 2, 5}, {0, 3, 7}, {0, 4, 6}, {1, 2, 9}, {1, 3, 4}}

def cover10 : Finset (Sym2 (Fin 10)) :=
  {s(0, 1), s(0, 6), s(0, 7), s(1, 8), s(1, 9),
   s(2, 5), s(3, 4), s(3, 7), s(4, 6), s(2, 9)}

lemma packing10_card : packing10.card = 5 := by native_decide

lemma cover10_card : cover10.card = 10 := by native_decide

lemma packing10_pairwise_inter_le_one :
    ∀ s ∈ packing10, ∀ t ∈ packing10, s ≠ t → (s ∩ t).card ≤ 1 := by
  native_decide

private def mapTri (f : Fin 10 → V) (t : Finset (Fin 10)) : Finset V := t.image f

private lemma map_lab (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) :
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 0 = u ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 1 = v ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 2 = c0 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 3 = c1 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 4 = c2 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 5 = c3 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 6 = a0 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 7 = a1 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 8 = b0 ∧
    labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 9 = b1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma packing_image_eq (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) :
    packing10.image (mapTri (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) =
      packing42 u v c0 c1 c2 c3 a0 a1 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, _, f9⟩ := map_lab u v c0 c1 c2 c3 a0 a1 b0 b1
  set f := labels10 u v c0 c1 c2 c3 a0 a1 b0 b1 with hf
  have e1 : mapTri f {0, 2, 5} = ({u, c0, c3} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f5]
  have e2 : mapTri f {0, 3, 7} = ({u, c1, a1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f7]
  have e3 : mapTri f {0, 4, 6} = ({u, c2, a0} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f6]
  have e4 : mapTri f {1, 2, 9} = ({v, c0, b1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f9]
  have e5 : mapTri f {1, 3, 4} = ({v, c1, c2} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f4]
  simp only [packing10, packing42, image_insert, image_singleton, e1, e2, e3, e4, e5]

private lemma cover_image_eq (u v c0 c1 c2 c3 a0 a1 b0 b1 : V) :
    cover10.image (Sym2.map (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) =
      cover42 u v c0 c1 c2 c3 a0 a1 b0 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := map_lab u v c0 c1 c2 c3 a0 a1 b0 b1
  set f := labels10 u v c0 c1 c2 c3 a0 a1 b0 b1
  have mk (i j : Fin 10) {x y : V} (hi : f i = x) (hj : f j = y) :
      Sym2.map f s(i, j) = s(x, y) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10, cover42, image_insert, image_singleton,
    mk 0 1 f0 f1, mk 0 6 f0 f6, mk 0 7 f0 f7, mk 1 8 f1 f8, mk 1 9 f1 f9,
    mk 2 5 f2 f5, mk 3 4 f3 f4, mk 3 7 f3 f7, mk 4 6 f4 f6, mk 2 9 f2 f9]

lemma packing42_card' (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    (packing42 u v c0 c1 c2 c3 a0 a1 b1).card = 5 := by
  let f := labels10 u v c0 c1 c2 c3 a0 a1 b0 b1
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packing_image_eq u v c0 c1 c2 c3 a0 a1 b0 b1,
    card_image_of_injective _ hinjT, packing10_card]

lemma packing42_disjoint (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    ∀ s ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1,
      ∀ t ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1,
        s ≠ t → Disjoint (triEdges s) (triEdges t) := by
  let f := labels10 u v c0 c1 c2 c3 a0 a1 b0 b1
  intro s hs t ht hst
  rw [← packing_image_eq u v c0 c1 c2 c3 a0 a1 b0 b1] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  have hs0t0 : s0 ≠ t0 := fun h => by subst h; exact hst rfl
  have hinter := packing10_pairwise_inter_le_one s0 hs0 t0 ht0 hs0t0
  have hinter' : (mapTri f s0 ∩ mapTri f t0).card ≤ 1 := by
    have : mapTri f s0 ∩ mapTri f t0 = (s0 ∩ t0).image f := by
      simp only [mapTri]; exact (Finset.image_inter s0 t0 hinj).symm
    rw [this]
    exact le_trans card_image_le hinter
  rw [Finset.disjoint_left]
  intro e heA heB
  have hA := mem_filter.1 heA
  have hB := mem_filter.1 heB
  revert hA hB
  refine Sym2.inductionOn e fun x y hA hB => ?_
  have hxA : x ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 x (Sym2.mem_mk_left x y)
  have hyA : y ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 y (Sym2.mem_mk_right x y)
  have hxB : x ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 x (Sym2.mem_mk_left x y)
  have hyB : y ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 y (Sym2.mem_mk_right x y)
  have hxy : x ≠ y := fun eq => hA.2 (by simpa [Sym2.mk_isDiag_iff] using eq)
  have hsub : ({x, y} : Finset V) ⊆ mapTri f s0 ∩ mapTri f t0 := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [hxA, hyA, hxB, hyB]
  have : 2 ≤ (mapTri f s0 ∩ mapTri f t0).card :=
    (card_le_card hsub).trans' (by simp [card_insert_of_notMem, hxy])
  omega

lemma cover42_card (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    (cover42 u v c0 c1 c2 c3 a0 a1 b0 b1).card = 10 := by
  let f := labels10 u v c0 c1 c2 c3 a0 a1 b0 b1
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← cover_image_eq u v c0 c1 c2 c3 a0 a1 b0 b1,
    card_image_of_injective _ hinjE, cover10_card]

lemma external42 (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1)
    {e : Sym2 V} (he : e ∈ triEdges t)
    (hZ : ∀ z ∈ ({u, v} : Finset V), z ∉ e) :
    e ∈ cover42 u v c0 c1 c2 c3 a0 a1 b0 b1 := by
  have hu : u ∉ e := hZ u (by simp)
  have hv : v ∉ e := hZ v (by simp)
  have t1 : ({u, c0, c3} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 2) (k := 5)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 : ({u, c1, a1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 3) (k := 7)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 : ({u, c2, a0} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 4) (k := 6)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 : ({v, c0, b1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 2) (k := 9)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 : ({v, c1, c2} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 3) (k := 4)
      (by decide) (by decide) (by decide) rfl rfl rfl
  simp only [packing42, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · have h := triEdges_omit_vertex t1 he hu; rw [h]; simp [cover42]
  · have h := triEdges_omit_vertex t2 he hu; rw [h]; simp [cover42]
  · have h := triEdges_omit_vertex t3 he hu; rw [h]; simp [cover42]
  · have h := triEdges_omit_vertex t4 he hv; rw [h]; simp [cover42]
  · have h := triEdges_omit_vertex t5 he hv; rw [h]; simp [cover42]

lemma coversZ42 (H : HubConfig G)
    (c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hC : H.C = {c0, c1, c2, c3})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hcore_only : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2))
    (_hinj : Function.Injective (labels10 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ G.cliqueFinset 3)
    (hZmeet : ∃ z ∈ ({H.u, H.v} : Finset V), z ∈ t) :
    ¬ Disjoint (cover42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1) (triEdges t) := by
  classical
  set X := cover42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1
  obtain ⟨hub, hhub, hhubt⟩ := hZmeet
  simp only [mem_insert, mem_singleton] at hhub
  have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
  have hcard : t.card = 3 := hN.card_eq
  have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b := fun a ha b hb hab => hN.isClique ha hb hab
  have herase : (t.erase hub).card = 2 := by
    rw [card_erase_of_mem hhubt, hcard]
  rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hxy, ht_erase⟩
  have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
  have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
  have ht_eq : t = {hub, px, py} := by
    ext w; constructor
    · intro hw
      by_cases hwz : w = hub
      · simp [hwz]
      · have hw' : w ∈ t.erase hub := mem_erase.2 ⟨hwz, hw⟩
        rw [ht_erase] at hw'
        exact mem_insert_of_mem hw'
    · intro hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hhubt
      · exact (mem_erase.1 hpx_erase).2
      · exact (mem_erase.1 hpy_erase).2
  have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
  have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
  have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
  have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
  have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
    simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hxy]
  have him_rim : s(px, py) ∈ triEdges t := by
    rw [ht_eq, triEdges_eq_of_card3 hcard3]; simp
  have him_zx : s(hub, px) ∈ triEdges t := by
    rw [ht_eq, triEdges_eq_of_card3 hcard3]; simp [Sym2.eq_swap]
  have him_zy : s(hub, py) ∈ triEdges t := by
    rw [ht_eq, triEdges_eq_of_card3 hcard3]; simp [Sym2.eq_swap]
  have meet (e : Sym2 V) (heX : e ∈ X) (heT : e ∈ triEdges t) :
      ¬ Disjoint X (triEdges t) := fun h => Finset.disjoint_left.1 h heX heT
  have hzx : G.Adj hub px := hadj hub hhubt px hxyt hx_ne.symm
  have hzy : G.Adj hub py := hadj hub hhubt py hyyt hy_ne.symm
  have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hxy
  rcases hhub with rfl | rfl
  · -- hub = u
    have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
    have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
    rw [H.hNu] at hxN hyN
    by_cases hxv : px = H.v
    · subst hxv
      exact meet s(H.u, H.v) (by simp [X, cover42]) him_zx
    by_cases hyv : py = H.v
    · subst hyv
      exact meet s(H.u, H.v) (by simp [X, cover42]) him_zy
    have hxCA : px ∈ H.C ∪ H.A := by simpa [hxv] using hxN
    have hyCA : py ∈ H.C ∪ H.A := by simpa [hyv] using hyN
    by_cases hxAmem : px ∈ H.A
    · have hpa : px = a0 ∨ px = a1 := by simpa [hA] using hxAmem
      rcases hpa with hpa | hpa
      · exact meet s(H.u, a0) (by simp [X, cover42]) (hpa ▸ him_zx)
      · exact meet s(H.u, a1) (by simp [X, cover42]) (hpa ▸ him_zx)
    by_cases hyAmem : py ∈ H.A
    · have hpa : py = a0 ∨ py = a1 := by simpa [hA] using hyAmem
      rcases hpa with hpa | hpa
      · exact meet s(H.u, a0) (by simp [X, cover42]) (hpa ▸ him_zy)
      · exact meet s(H.u, a1) (by simp [X, cover42]) (hpa ▸ him_zy)
    have hxC : px ∈ H.C := by simpa [mem_union, hxAmem] using hxCA
    have hyC : py ∈ H.C := by simpa [mem_union, hyAmem] using hyCA
    rcases hcore_only px hxC py hyC hxyAdj with hr | hr
    · rw [hr] at him_rim; exact meet s(c0, c3) (by simp [X, cover42]) him_rim
    · rw [hr] at him_rim; exact meet s(c1, c2) (by simp [X, cover42]) him_rim
  · -- hub = v
    have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
    have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
    rw [H.hNv] at hxN hyN
    by_cases hxu : px = H.u
    · subst hxu
      have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zx
      exact meet s(H.u, H.v) (by simp [X, cover42]) heT
    by_cases hyu : py = H.u
    · subst hyu
      have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zy
      exact meet s(H.u, H.v) (by simp [X, cover42]) heT
    have hxCB : px ∈ H.C ∪ H.B := by simpa [hxu] using hxN
    have hyCB : py ∈ H.C ∪ H.B := by simpa [hyu] using hyN
    by_cases hxBmem : px ∈ H.B
    · have hpb : px = b0 ∨ px = b1 := by simpa [hB] using hxBmem
      rcases hpb with hpb | hpb
      · exact meet s(H.v, b0) (by simp [X, cover42]) (hpb ▸ him_zx)
      · exact meet s(H.v, b1) (by simp [X, cover42]) (hpb ▸ him_zx)
    by_cases hyBmem : py ∈ H.B
    · have hpb : py = b0 ∨ py = b1 := by simpa [hB] using hyBmem
      rcases hpb with hpb | hpb
      · exact meet s(H.v, b0) (by simp [X, cover42]) (hpb ▸ him_zy)
      · exact meet s(H.v, b1) (by simp [X, cover42]) (hpb ▸ him_zy)
    have hxC : px ∈ H.C := by simpa [mem_union, hxBmem] using hxCB
    have hyC : py ∈ H.C := by simpa [mem_union, hyBmem] using hyCB
    rcases hcore_only px hxC py hyC hxyAdj with hr | hr
    · rw [hr] at him_rim; exact meet s(c0, c3) (by simp [X, cover42]) him_rim
    · rw [hr] at him_rim; exact meet s(c1, c2) (by simp [X, cover42]) him_rim

/-- **Proposition 4.2** (full certificate under labelled attachments). -/
theorem prop42_certificate (H : HubConfig G)
    (c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hC : H.C = {c0, c1, c2, c3})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hcore : G.Adj c0 c3 ∧ G.Adj c1 c2)
    (hcore_only : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2))
    (hatt : G.Adj c1 a1 ∧ G.Adj c2 a0 ∧ G.Adj c0 b1)
    (h10 : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10) :
    ∃ cert : ReductionCertificate G ({H.u, H.v} : Finset V),
      cert.packing = packing42 H.u H.v c0 c1 c2 c3 a0 a1 b1 ∧
      cert.cover = cover42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 ∧
      cert.packing.card = 5 ∧ cert.cover.card = 10 := by
  let hinj := labels10_injective H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 h10
  let S := packing42 H.u H.v c0 c1 c2 c3 a0 a1 b1
  let X := cover42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1
  have uc0 : G.Adj H.u c0 := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uc1 : G.Adj H.u c1 := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uc2 : G.Adj H.u c2 := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uc3 : G.Adj H.u c3 := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua0 : G.Adj H.u a0 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ua1 : G.Adj H.u a1 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vc0 : G.Adj H.v c0 := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc1 : G.Adj H.v c1 := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc2 : G.Adj H.v c2 := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vb0 : G.Adj H.v b0 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vb1 : G.Adj H.v b1 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have t1 := card3_of_inj hinj (i := 0) (j := 2) (k := 5)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 := card3_of_inj hinj (i := 0) (j := 3) (k := 7)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 := card3_of_inj hinj (i := 0) (j := 4) (k := 6)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 := card3_of_inj hinj (i := 1) (j := 2) (k := 9)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 := card3_of_inj hinj (i := 1) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packing42_disjoint H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 hinj⟩
    intro t ht
    simp only [S, packing42, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uc0 uc3 hcore.1 t1
    · exact is3clique_of_adj G uc1 ua1 hatt.1 t2
    · exact is3clique_of_adj G uc2 ua0 hatt.2.1 t3
    · exact is3clique_of_adj G vc0 vb1 hatt.2.2 t4
    · exact is3clique_of_adj G vc1 vc2 hcore.2 t5
  have hXedges : X ⊆ G.edgeFinset := by
    intro e he
    simp only [X, cover42, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (mem_edgeFinset).2 H.huv
    · exact (mem_edgeFinset).2 ua0
    · exact (mem_edgeFinset).2 ua1
    · exact (mem_edgeFinset).2 vb0
    · exact (mem_edgeFinset).2 vb1
    · exact (mem_edgeFinset).2 hcore.1
    · exact (mem_edgeFinset).2 hcore.2
    · exact (mem_edgeFinset).2 hatt.1
    · exact (mem_edgeFinset).2 hatt.2.1
    · exact (mem_edgeFinset).2 hatt.2.2
  have hcardS := packing42_card' H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 hinj
  have hcardX := cover42_card H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 hinj
  refine ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := by
      have h1 := hcardS
      have h2 := hcardX
      simp [S, X, h1, h2]
    coversZ := fun t ht hZ => coversZ42 G H c0 c1 c2 c3 a0 a1 b0 b1 hC hA hB
      hcore_only hinj ht hZ
    external := fun t ht e he hZ => external42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1 hinj ht he hZ
  }, rfl, rfl, hcardS, hcardX⟩

/-- Opposite hub is in `N(u)`. -/
lemma opposite_hub_mem (H : HubConfig G) : H.v ∈ G.neighborFinset H.u := by
  rw [H.hNu]; exact mem_insert_self _ _

lemma privates_of (H : HubConfig G) :
    ∃ d0 d1, H.A = {d0, d1} ∧ d0 ≠ d1 ∧
      d0 ∈ G.neighborFinset H.u ∧ d1 ∈ G.neighborFinset H.u := by
  obtain ⟨d0, d1, hd01, hAeq⟩ := (card_eq_two (s := H.A)).1 H.hA
  exact ⟨d0, d1, hAeq, hd01,
    by rw [H.hNu, hAeq]; simp, by rw [H.hNu, hAeq]; simp⟩

lemma z_adj_core (H : HubConfig G) {c : V} (hc : c ∈ H.C) : G.Adj H.v c :=
  (G.mem_neighborFinset _ _).1 (mem_inter.1 (H.hC ▸ hc)).2

lemma core_mem_Nu (H : HubConfig G) {c : V} (hc : c ∈ H.C) :
    c ∈ G.neighborFinset H.u := by
  rw [H.hNu]; exact mem_insert_of_mem (mem_union_left _ hc)

lemma ne_z_of_core (H : HubConfig G) {c : V} (hc : c ∈ H.C) : H.v ≠ c :=
  fun h => H.hvA.2 (h ▸ hc)

lemma ne_z_of_priv (H : HubConfig G) {d : V} (hd : d ∈ H.A) : H.v ≠ d :=
  fun h => H.hvA.1 (h ▸ hd)

lemma ne_core_priv (H : HubConfig G) {c d : V} (hc : c ∈ H.C) (hd : d ∈ H.A) : c ≠ d :=
  fun h => Finset.disjoint_left.1 H.hAdisj hd (h ▸ hc)

/-- Pairwise distinctness of four labels of `C`. -/
lemma core4_distinct (H : HubConfig G) {p q r s : V} (hC : H.C = {p, q, r, s}) :
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s := by
  have hcard : ({p, q, r, s} : Finset V).card = 4 := by rw [← hC]; exact H.hCcard
  have le3 (a b c : V) : ({a, b, c} : Finset V).card ≤ 3 := by
    cases' eq_or_ne a b with h1 h1 <;> cases' eq_or_ne a c with h2 h2 <;>
      cases' eq_or_ne b c with h3 h3 <;>
        simp [h1, h2, h3, card_insert_of_notMem, card_insert_of_mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; subst h
    have heq : ({p, p, r, s} : Finset V) = {p, r, s} := by simp [insert_eq_of_mem]
    rw [heq] at hcard; have := le3 p r s; omega
  · intro h; subst h
    have heq : ({p, q, p, s} : Finset V) = {p, q, s} := by
      ext x; simp [or_comm, or_left_comm]
    rw [heq] at hcard; have := le3 p q s; omega
  · intro h; subst h
    have heq : ({p, q, r, p} : Finset V) = {p, q, r} := by
      ext x; simp [or_comm, or_left_comm]
    rw [heq] at hcard; have := le3 p q r; omega
  · intro h; subst h
    have heq : ({p, q, q, s} : Finset V) = {p, q, s} := by
      ext x; simp [or_comm, or_left_comm]
    rw [heq] at hcard; have := le3 p q s; omega
  · intro h; subst h
    have heq : ({p, q, r, q} : Finset V) = {p, q, r} := by
      ext x; simp [or_comm, or_left_comm]
    rw [heq] at hcard; have := le3 p q r; omega
  · intro h; subst h
    have heq : ({p, q, r, r} : Finset V) = {p, q, r} := by simp [insert_eq_of_mem]
    rw [heq] at hcard; have := le3 p q r; omega

/-- Lemma 4.1(1): no private edge under connected non-WKE 2K₂ link. -/
theorem lemma41_no_private (H : HubConfig G)
    (hconn : (linkGraph G H.u).Connected) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hd01 : d0 ≠ d1) :
    ¬ G.Adj d0 d1 := by
  classical
  intro hpriv
  -- M = {p0p1, q0q1, d0d1}, Q = {z, d0, d1}; outside edges are exactly the two core edges.
  have ⟨hp01, hp0q0, hp0q1, hp1q0, hp1q1, hq01⟩ := core4_distinct G H hC
  -- Reorder: core4_distinct on {p0,p1,q0,q1}
  have hdist := core4_distinct G H hC
  have hp0C : p0 ∈ H.C := by rw [hC]; simp
  have hp1C : p1 ∈ H.C := by rw [hC]; simp
  have hq0C : q0 ∈ H.C := by rw [hC]; simp
  have hq1C : q1 ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hp0N := core_mem_Nu G H hp0C
  have hp1N := core_mem_Nu G H hp1C
  have hq0N := core_mem_Nu G H hq0C
  have hq1N := core_mem_Nu G H hq1C
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have hd0N : d0 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hd1N : d1 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hz_ne_d0 := ne_z_of_priv G H hd0A
  have hz_ne_d1 := ne_z_of_priv G H hd1A
  -- Outside Q={z,d0,d1}: only core edges among {p0,p1,q0,q1}
  let Q : Finset V := {H.v, d0, d1}
  let M : Finset (Sym2 V) := {s(p0, p1), s(q0, q1), s(d0, d1)}
  have hQcard : Q.card = 3 := by
    change ({H.v, d0, d1} : Finset V).card = 3
    have h1 : H.v ∉ ({d0, d1} : Finset V) := by simp [hz_ne_d0, hz_ne_d1]
    have h2 : d0 ∉ ({d1} : Finset V) := by simp [hd01]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  -- Distinctness of matching edges
  have hne_pq : s(p0, p1) ≠ s(q0, q1) := by
    intro heq
    have : p0 = q0 ∨ p0 = q1 := by
      simpa [Sym2.mem_iff] using
        (show p0 ∈ s(q0, q1) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
    rcases this with rfl | rfl
    · exact hdist.2.1 rfl  -- p0 ≠ q0
    · exact hdist.2.2.1 rfl
  have hne_pd : s(p0, p1) ≠ s(d0, d1) := by
    intro heq
    have : p0 = d0 ∨ p0 = d1 := by
      simpa [Sym2.mem_iff] using
        (show p0 ∈ s(d0, d1) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
    rcases this with rfl | rfl
    · exact (ne_core_priv G H hp0C hd0A) rfl
    · exact (ne_core_priv G H hp0C hd1A) rfl
  have hne_qd : s(q0, q1) ≠ s(d0, d1) := by
    intro heq
    have : q0 = d0 ∨ q0 = d1 := by
      simpa [Sym2.mem_iff] using
        (show q0 ∈ s(d0, d1) by simpa [← heq] using Sym2.mem_mk_left q0 q1)
    rcases this with rfl | rfl
    · exact (ne_core_priv G H hq0C hd0A) rfl
    · exact (ne_core_priv G H hq0C hd1A) rfl
  have hMcard : M.card = 3 := by
    change ({s(p0, p1), s(q0, q1), s(d0, d1)} : Finset (Sym2 V)).card = 3
    have h1 : s(p0, p1) ∉ ({s(q0, q1), s(d0, d1)} : Finset (Sym2 V)) := by
      simp [hne_pq, hne_pd]
    have h2 : s(q0, q1) ∉ ({s(d0, d1)} : Finset (Sym2 V)) := by simp [hne_qd]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  have hdisj_pq : Disjoint s(p0, p1).toFinset s(q0, q1).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hdist.2.1
    · exact hdist.2.2.1
    · exact hdist.2.2.2.1
    · exact hdist.2.2.2.2.1
  have hdisj_pd : Disjoint s(p0, p1).toFinset s(d0, d1).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ne_core_priv G H hp0C hd0A
    · exact ne_core_priv G H hp0C hd1A
    · exact ne_core_priv G H hp1C hd0A
    · exact ne_core_priv G H hp1C hd1A
  have hdisj_qd : Disjoint s(q0, q1).toFinset s(d0, d1).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ne_core_priv G H hq0C hd0A
    · exact ne_core_priv G H hq0C hd1A
    · exact ne_core_priv G H hq1C hd0A
    · exact ne_core_priv G H hq1C hd1A
  have hM : IsEdgeMatching (linkGraph G H.u) M := by
    refine ⟨?_, ?_⟩
    · intro e he; simp only [M, mem_insert, mem_singleton] at he
      rcases he with h | h | h
      · subst h; exact Prop31.link_edge G H.u p0 p1 hp0N hp1N hcore.1
      · subst h; exact Prop31.link_edge G H.u q0 q1 hq0N hq1N hcore.2
      · subst h; exact Prop31.link_edge G H.u d0 d1 hd0N hd1N hpriv
    · intro e he f hf hne'
      simp only [M, mem_insert, mem_singleton] at he hf
      rcases he with he | he | he <;> rcases hf with hf | hf | hf
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj_pq
      · subst he; subst hf; exact hdisj_pd
      · subst he; subst hf; exact hdisj_pq.symm
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj_qd
      · subst he; subst hf; exact hdisj_pd.symm
      · subst he; subst hf; exact hdisj_qd.symm
      · subst he; subst hf; exact absurd rfl hne'
  have honly_out : ∀ e ∈ (linkGraph G H.u).edgeFinset,
      (∀ x ∈ e, x ∉ Q) → e = s(p0, p1) ∨ e = s(q0, q1) := by
    intro e he hQ
    revert he hQ
    refine Sym2.inductionOn e fun a b he hQ => ?_
    have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
    have hG : G.Adj a b := hab.2.2
    have haQ : a ∉ Q := hQ a (by simp)
    have hbQ : b ∉ Q := hQ b (by simp)
    -- a,b ∈ C (since not z and not in A = {d0,d1})
    have memC (x : V) (hxN : x ∈ G.neighborFinset H.u) (hxQ : x ∉ Q) : x ∈ H.C := by
      rw [H.hNu] at hxN
      simp only [Q, mem_insert, mem_union, mem_singleton, hAeq] at hxN hxQ
      rcases hxN with rfl | hC' | hA'
      · exact absurd (Or.inl rfl) hxQ
      · exact hC'
      · exact absurd (Or.inr hA') hxQ
    have haC := memC a hab.1 haQ
    have hbC := memC b hab.2.1 hbQ
    exact honly a haC b hbC hG
  have : IsWKE (linkGraph G H.u) :=
    isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hQ => by
      rcases honly_out e he hQ with h | h <;> simp [M, h]⟩
  exact hnot this

/-- Lemma 4.1(3): crossed private matching on some core edge. -/
theorem lemma41_cross (H : HubConfig G)
    (hconn : (linkGraph G H.u).Connected) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1)) :
    ∃ d0 d1, H.A = {d0, d1} ∧
      ((G.Adj p0 d0 ∧ G.Adj p1 d1) ∨ (G.Adj p0 d1 ∧ G.Adj p1 d0) ∨
       (G.Adj q0 d0 ∧ G.Adj q1 d1) ∨ (G.Adj q0 d1 ∧ G.Adj q1 d0)) := by
  obtain ⟨d0, d1, hAeq, hd01, _, _⟩ := privates_of G H
  have hnopriv := lemma41_no_private G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  refine ⟨d0, d1, hAeq, ?_⟩
  -- Parts 2–3: each core edge is hit; then crossed matching. Deferred.
  sorry

end MatchingCore

/-! ## Star core `K_{1,3}` (Lemma 4.3) -/

namespace StarCore

open MatchingCore

/-- No u-link edge lies entirely outside `{v, p}` when the core is a p-star, there is no
private edge, and no leaf meets `A`. -/
lemma star_empty_outside_center (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hpriv : ¬ G.Adj d0 d1)
    (hatt : ∀ x ∈ ({q, r, s} : Finset V), G.neighborFinset x ∩ H.A = ∅)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ x ∈ e, x ∉ ({H.v, p} : Finset V)) : False := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have haOut : a ∉ ({H.v, p} : Finset V) := hOut a (by simp)
  have hbOut : b ∉ ({H.v, p} : Finset V) := hOut b (by simp)
  have classify (x : V) (hxN : x ∈ G.neighborFinset H.u)
      (hxOut : x ∉ ({H.v, p} : Finset V)) : x ∈ H.C ∪ H.A ∧ x ≠ p := by
    rw [H.hNu] at hxN
    simp only [mem_insert, mem_union, mem_singleton] at hxN hxOut
    refine ⟨?_, fun hp => hxOut (Or.inr hp)⟩
    rcases hxN with rfl | hC' | hA'
    · exact absurd (Or.inl rfl) hxOut
    · exact mem_union_left _ hC'
    · exact mem_union_right _ hA'
  have haCl := classify a hab.1 haOut
  have hbCl := classify b hab.2.1 hbOut
  have leaf_of (x : V) (hxC : x ∈ H.C) (hxp : x ≠ p) : x ∈ ({q, r, s} : Finset V) := by
    have : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hxC
    simp only [mem_insert, mem_singleton] at this ⊢
    rcases this with rfl | h
    · exact absurd rfl hxp
    · exact h
  by_cases haC : a ∈ H.C
  · by_cases hbC : b ∈ H.C
    · have hem := honly a haC b hbC hG
      have hp_mem : p ∈ s(a, b) := by
        rcases hem with h | h | h
        · simpa [h] using (Sym2.mem_mk_left p q : p ∈ s(p, q))
        · simpa [h] using (Sym2.mem_mk_left p r : p ∈ s(p, r))
        · simpa [h] using (Sym2.mem_mk_left p s : p ∈ s(p, s))
      have : a = p ∨ b = p := by simpa [Sym2.mem_iff, eq_comm] using hp_mem
      rcases this with rfl | rfl
      · exact haCl.2 rfl
      · exact hbCl.2 rfl
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have haL := leaf_of a haC haCl.2
      have hempty := hatt a haL
      have : b ∈ G.neighborFinset a ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
      simpa [hempty] using this
  · have haA : a ∈ H.A := (mem_union.1 haCl.1).resolve_left haC
    by_cases hbC : b ∈ H.C
    · have hbL := leaf_of b hbC hbCl.2
      have hempty := hatt b hbL
      have : a ∈ G.neighborFinset b ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
      simpa [hempty] using this
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
      have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
      have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
      have : G.Adj d0 d1 := by
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hne
        · exact hG
        · exact hG.symm
        · exact absurd rfl hne
      exact hpriv this

/-- Star link is WKE when no leaf meets `A` and the private edge is absent. -/
theorem star_wke_no_attach_no_priv (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hstar : G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hpriv : ¬ G.Adj d0 d1)
    (hatt : ∀ x ∈ ({q, r, s} : Finset V), G.neighborFinset x ∩ H.A = ∅) :
    IsWKE (linkGraph G H.u) := by
  classical
  have ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hpN := core_mem_Nu G H hpC
  have hrN := core_mem_Nu G H hrC
  have hsN := core_mem_Nu G H hsC
  have hzs := z_adj_core G H hsC
  have hz_ne_p := ne_z_of_core G H hpC
  have hz_ne_r := ne_z_of_core G H hrC
  let Q : Finset V := {H.v, p}
  let M : Finset (Sym2 V) := {s(p, r), s(H.v, s)}
  have hne : s(p, r) ≠ s(H.v, s) := by
    intro heq
    have : p = H.v ∨ p = s := by
      simpa [Sym2.mem_iff] using
        (show p ∈ s(H.v, s) by simpa [← heq] using (Sym2.mem_mk_left p r))
    rcases this with rfl | rfl
    · exact hz_ne_p rfl
    · exact hps rfl
  have hdisj : Disjoint s(p, r).toFinset s(H.v, s).toFinset := by
    simp [Sym2.toFinset_mk_eq, Finset.disjoint_iff_ne, hz_ne_p.symm, hps, hz_ne_r.symm, hrs]
  have hM : IsEdgeMatching (linkGraph G H.u) M := by
    refine ⟨?_, ?_⟩
    · intro e he; simp only [M, mem_insert, mem_singleton] at he
      rcases he with h | h
      · subst h; exact Prop31.link_edge G H.u p r hpN hrN hstar.1
      · subst h; exact Prop31.link_edge G H.u H.v s hzN hsN hzs
    · intro e he f hf hne'
      simp only [M, mem_insert, mem_singleton] at he hf
      rcases he with he | he <;> rcases hf with hf | hf
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj
      · subst he; subst hf; exact hdisj.symm
      · subst he; subst hf; exact absurd rfl hne'
  have hQc : Q.card = 2 := by
    change ({H.v, p} : Finset V).card = 2
    rw [card_insert_of_notMem ((by simpa using hz_ne_p : H.v ∉ ({p} : Finset V))), card_singleton]
  have hMc : M.card = 2 := by
    change ({s(p, r), s(H.v, s)} : Finset (Sym2 V)).card = 2
    rw [card_insert_of_notMem ((by simpa using hne)), card_singleton]
  refine isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQc.trans hMc.symm), ?_⟩
  · intro e he hQ
    exact (star_empty_outside_center G H p q r s hC honly d0 d1 hAeq hpriv hatt he hQ).elim


/-- Outside `{v,p,q}` with no attachments at `r,s`: only possible edge is the private edge. -/
lemma star_outside_zpq (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (d0 d1 : V) (hAeq : H.A = {d0, d1})
    (hatt_rs : ∀ x ∈ ({r, s} : Finset V), G.neighborFinset x ∩ H.A = ∅)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ x ∈ e, x ∉ ({H.v, p, q} : Finset V)) :
    e = s(d0, d1) := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have haOut : a ∉ ({H.v, p, q} : Finset V) := hOut a (by simp)
  have hbOut : b ∉ ({H.v, p, q} : Finset V) := hOut b (by simp)
  have classify (x : V) (hxN : x ∈ G.neighborFinset H.u)
      (hxOut : x ∉ ({H.v, p, q} : Finset V)) : x ∈ H.C ∪ H.A ∧ x ≠ p ∧ x ≠ q := by
    rw [H.hNu] at hxN
    simp only [mem_insert, mem_union, mem_singleton] at hxN hxOut
    refine ⟨?_, fun hp => hxOut (Or.inr (Or.inl hp)), fun hq => hxOut (Or.inr (Or.inr hq))⟩
    rcases hxN with rfl | hC' | hA'
    · exact absurd (Or.inl rfl) hxOut
    · exact mem_union_left _ hC'
    · exact mem_union_right _ hA'
  have haCl := classify a hab.1 haOut
  have hbCl := classify b hab.2.1 hbOut
  have leaf_rs (x : V) (hxC : x ∈ H.C) (hxp : x ≠ p) (hxq : x ≠ q) :
      x ∈ ({r, s} : Finset V) := by
    have : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hxC
    simp only [mem_insert, mem_singleton] at this ⊢
    rcases this with rfl | rfl | rfl | rfl
    · exact absurd rfl hxp
    · exact absurd rfl hxq
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases haC : a ∈ H.C
  · by_cases hbC : b ∈ H.C
    · have hem := honly a haC b hbC hG
      have : a = p ∨ b = p ∨ a = q ∨ b = q := by
        rcases hem with h | h | h
        · have hp' : p ∈ s(a, b) := by simpa [h] using (Sym2.mem_mk_left p q)
          have : a = p ∨ b = p := by simpa [Sym2.mem_iff, eq_comm] using hp'
          rcases this with rfl | rfl <;> simp
        · have hp' : p ∈ s(a, b) := by simpa [h] using (Sym2.mem_mk_left p r)
          have : a = p ∨ b = p := by simpa [Sym2.mem_iff, eq_comm] using hp'
          rcases this with rfl | rfl <;> simp
        · have hp' : p ∈ s(a, b) := by simpa [h] using (Sym2.mem_mk_left p s)
          have : a = p ∨ b = p := by simpa [Sym2.mem_iff, eq_comm] using hp'
          rcases this with rfl | rfl <;> simp
      rcases this with rfl | rfl | rfl | rfl
      · exact absurd rfl haCl.2.1
      · exact absurd rfl hbCl.2.1
      · exact absurd rfl haCl.2.2
      · exact absurd rfl hbCl.2.2
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have haL := leaf_rs a haC haCl.2.1 haCl.2.2
      have hempty := hatt_rs a haL
      have : b ∈ G.neighborFinset a ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
      exact (by simpa [hempty] using this : False).elim
  · have haA : a ∈ H.A := (mem_union.1 haCl.1).resolve_left haC
    by_cases hbC : b ∈ H.C
    · have hbL := leaf_rs b hbC hbCl.2.1 hbCl.2.2
      have hempty := hatt_rs b hbL
      have : a ∈ G.neighborFinset b ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
      exact (by simpa [hempty] using this : False).elim
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
      have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
      have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne

/-- Star WKE: private edge present; at most leaf `q` may attach. -/
theorem star_wke_private_edge (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hstar : G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hd01 : d0 ≠ d1) (hpriv : G.Adj d0 d1)
    (hatt_rs : ∀ x ∈ ({r, s} : Finset V), G.neighborFinset x ∩ H.A = ∅) :
    IsWKE (linkGraph G H.u) := by
  classical
  have ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hpN := core_mem_Nu G H hpC
  have hrN := core_mem_Nu G H hrC
  have hsN := core_mem_Nu G H hsC
  have hd0N : d0 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hd1N : d1 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hzr := z_adj_core G H hrC
  have hz_ne_p := ne_z_of_core G H hpC
  have hz_ne_q := ne_z_of_core G H hqC
  have hz_ne_r := ne_z_of_core G H hrC
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have hz_ne_d0 := ne_z_of_priv G H hd0A
  have hz_ne_d1 := ne_z_of_priv G H hd1A
  have hp_ne_d0 := ne_core_priv G H hpC hd0A
  have hp_ne_d1 := ne_core_priv G H hpC hd1A
  have hr_ne_d0 := ne_core_priv G H hrC hd0A
  have hr_ne_d1 := ne_core_priv G H hrC hd1A
  have hs_ne_d0 := ne_core_priv G H hsC hd0A
  have hs_ne_d1 := ne_core_priv G H hsC hd1A
  let Q : Finset V := {H.v, p, q}
  let M : Finset (Sym2 V) := {s(d0, d1), s(H.v, r), s(p, s)}
  have hQcard : Q.card = 3 := by
    change ({H.v, p, q} : Finset V).card = 3
    have h1 : H.v ∉ ({p, q} : Finset V) := by simp [hz_ne_p, hz_ne_q]
    have h2 : p ∉ ({q} : Finset V) := by simp [hpq]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  have hne01 : s(d0, d1) ≠ s(H.v, r) := by
    intro heq
    have : d0 = H.v ∨ d0 = r := by
      simpa [Sym2.mem_iff] using
        (show d0 ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left d0 d1)
    rcases this with rfl | rfl
    · exact hz_ne_d0 rfl
    · exact (hr_ne_d0.symm rfl)
  have hne02 : s(d0, d1) ≠ s(p, s) := by
    intro heq
    have : d0 = p ∨ d0 = s := by
      simpa [Sym2.mem_iff] using
        (show d0 ∈ s(p, s) by simpa [← heq] using Sym2.mem_mk_left d0 d1)
    rcases this with rfl | rfl
    · exact (hp_ne_d0.symm rfl)
    · exact (hs_ne_d0.symm rfl)
  have hne12 : s(H.v, r) ≠ s(p, s) := by
    intro heq
    have : H.v = p ∨ H.v = s := by
      simpa [Sym2.mem_iff] using
        (show H.v ∈ s(p, s) by simpa [← heq] using Sym2.mem_mk_left H.v r)
    rcases this with rfl | rfl
    · exact hz_ne_p rfl
    · exact (ne_z_of_core G H hsC) rfl
  have hMcard : M.card = 3 := by
    change ({s(d0, d1), s(H.v, r), s(p, s)} : Finset (Sym2 V)).card = 3
    have h1 : s(d0, d1) ∉ ({s(H.v, r), s(p, s)} : Finset (Sym2 V)) := by
      simp [hne01, hne02]
    have h2 : s(H.v, r) ∉ ({s(p, s)} : Finset (Sym2 V)) := by simp [hne12]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  have hdisj01 : Disjoint s(d0, d1).toFinset s(H.v, r).toFinset := by
    simp [Sym2.toFinset_mk_eq, Finset.disjoint_iff_ne,
      hz_ne_d0.symm, hr_ne_d0.symm, hz_ne_d1.symm, hr_ne_d1.symm]
  have hdisj02 : Disjoint s(d0, d1).toFinset s(p, s).toFinset := by
    simp [Sym2.toFinset_mk_eq, Finset.disjoint_iff_ne,
      hp_ne_d0.symm, hs_ne_d0.symm, hp_ne_d1.symm, hs_ne_d1.symm]
  have hdisj12 : Disjoint s(H.v, r).toFinset s(p, s).toFinset := by
    simp [Sym2.toFinset_mk_eq, Finset.disjoint_iff_ne,
      hz_ne_p, (ne_z_of_core G H hsC), hpr.symm, hrs]
  have hM : IsEdgeMatching (linkGraph G H.u) M := by
    refine ⟨?_, ?_⟩
    · intro e he; simp only [M, mem_insert, mem_singleton] at he
      rcases he with h | h | h
      · subst h; exact Prop31.link_edge G H.u d0 d1 hd0N hd1N hpriv
      · subst h; exact Prop31.link_edge G H.u H.v r hzN hrN hzr
      · subst h; exact Prop31.link_edge G H.u p s hpN hsN hstar.2
    · intro e he f hf hne'
      simp only [M, mem_insert, mem_singleton] at he hf
      rcases he with he | he | he <;> rcases hf with hf | hf | hf
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj01
      · subst he; subst hf; exact hdisj02
      · subst he; subst hf; exact hdisj01.symm
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj12
      · subst he; subst hf; exact hdisj02.symm
      · subst he; subst hf; exact hdisj12.symm
      · subst he; subst hf; exact absurd rfl hne'
  refine isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), ?_⟩
  · intro e he hQ
    have heq := star_outside_zpq G H p q r s hC honly d0 d1 hAeq hatt_rs he hQ
    simp only [M, mem_insert, mem_singleton, heq, true_or]

/-- Star WKE: no private edge; leaf `q` attaches via `q–di`; `r,s` do not. -/
theorem star_wke_one_leaf (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hstar : G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (d0 d1 di : V) (hAeq : H.A = {d0, d1}) (hdi : di = d0 ∨ di = d1)
    (hpriv : ¬ G.Adj d0 d1) (hqdi : G.Adj q di)
    (hatt_rs : ∀ x ∈ ({r, s} : Finset V), G.neighborFinset x ∩ H.A = ∅) :
    IsWKE (linkGraph G H.u) := by
  classical
  have ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hpN := core_mem_Nu G H hpC
  have hqN := core_mem_Nu G H hqC
  have hrN := core_mem_Nu G H hrC
  have hsN := core_mem_Nu G H hsC
  have hdiA : di ∈ H.A := by rw [hAeq]; rcases hdi with rfl | rfl <;> simp
  have hdiN : di ∈ G.neighborFinset H.u := by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdiA)
  have hzs := z_adj_core G H hsC
  have hz_ne_p := ne_z_of_core G H hpC
  have hz_ne_q := ne_z_of_core G H hqC
  have hz_ne_di := ne_z_of_priv G H hdiA
  have hq_ne_di := ne_core_priv G H hqC hdiA
  have hp_ne_di := ne_core_priv G H hpC hdiA
  have hr_ne_di := ne_core_priv G H hrC hdiA
  have hs_ne_di := ne_core_priv G H hsC hdiA
  let Q : Finset V := {H.v, p, q}
  let M : Finset (Sym2 V) := {s(q, di), s(p, r), s(H.v, s)}
  have hQcard : Q.card = 3 := by
    change ({H.v, p, q} : Finset V).card = 3
    have h1 : H.v ∉ ({p, q} : Finset V) := by simp [hz_ne_p, hz_ne_q]
    have h2 : p ∉ ({q} : Finset V) := by simp [hpq]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  have hne01 : s(q, di) ≠ s(p, r) := by
    intro heq
    have : q = p ∨ q = r := by
      simpa [Sym2.mem_iff] using
        (show q ∈ s(p, r) by simpa [← heq] using Sym2.mem_mk_left q di)
    rcases this with rfl | rfl
    · exact hpq rfl
    · exact hqr rfl
  have hne02 : s(q, di) ≠ s(H.v, s) := by
    intro heq
    have : q = H.v ∨ q = s := by
      simpa [Sym2.mem_iff] using
        (show q ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left q di)
    rcases this with rfl | rfl
    · exact hz_ne_q.symm rfl
    · exact hqs rfl
  have hne12 : s(p, r) ≠ s(H.v, s) := by
    intro heq
    have : p = H.v ∨ p = s := by
      simpa [Sym2.mem_iff] using
        (show p ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left p r)
    rcases this with rfl | rfl
    · exact hz_ne_p rfl
    · exact hps rfl
  have hMcard : M.card = 3 := by
    change ({s(q, di), s(p, r), s(H.v, s)} : Finset (Sym2 V)).card = 3
    have h1 : s(q, di) ∉ ({s(p, r), s(H.v, s)} : Finset (Sym2 V)) := by
      simp [hne01, hne02]
    have h2 : s(p, r) ∉ ({s(H.v, s)} : Finset (Sym2 V)) := by simp [hne12]
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
  have hdisj01 : Disjoint s(q, di).toFinset s(p, r).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hpq.symm
    · exact hqr
    · exact hp_ne_di.symm
    · exact hr_ne_di.symm
  have hdisj02 : Disjoint s(q, di).toFinset s(H.v, s).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hz_ne_q.symm
    · exact hqs
    · exact hz_ne_di.symm
    · exact hs_ne_di.symm
  have hdisj12 : Disjoint s(p, r).toFinset s(H.v, s).toFinset := by
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    refine Finset.disjoint_iff_ne.2 ?_
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hz_ne_p.symm
    · exact hps
    · exact (ne_z_of_core G H hrC).symm
    · exact hrs
  have hM : IsEdgeMatching (linkGraph G H.u) M := by
    refine ⟨?_, ?_⟩
    · intro e he; simp only [M, mem_insert, mem_singleton] at he
      rcases he with h | h | h
      · subst h; exact Prop31.link_edge G H.u q di hqN hdiN hqdi
      · subst h; exact Prop31.link_edge G H.u p r hpN hrN hstar.1
      · subst h; exact Prop31.link_edge G H.u H.v s hzN hsN hzs
    · intro e he f hf hne'
      simp only [M, mem_insert, mem_singleton] at he hf
      rcases he with he | he | he <;> rcases hf with hf | hf | hf
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj01
      · subst he; subst hf; exact hdisj02
      · subst he; subst hf; exact hdisj01.symm
      · subst he; subst hf; exact absurd rfl hne'
      · subst he; subst hf; exact hdisj12
      · subst he; subst hf; exact hdisj02.symm
      · subst he; subst hf; exact hdisj12.symm
      · subst he; subst hf; exact absurd rfl hne'
  refine isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), ?_⟩
  · intro e he hQ
    have heq := star_outside_zpq G H p q r s hC honly d0 d1 hAeq hatt_rs he
      (by intro x hx; simpa [Q] using hQ x hx)
    have hab : (linkGraph G H.u).Adj d0 d1 := by
      have h := (mem_edgeFinset (G := linkGraph G H.u)).1 he
      simpa [heq] using h
    exact (hpriv hab.2.2).elim

/-- Lemma 4.3: non-WKE star link ⇒ at least two leaves meet `A`. -/
theorem star_two_leaf_attachments (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hstar : G.Adj p q ∧ G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (hnot : ¬ IsWKE (linkGraph G H.u)) :
    2 ≤ (H.attachSupport H.A ∩ {q, r, s}).card := by
  classical
  by_contra hlt
  have _hle : (H.attachSupport H.A ∩ {q, r, s}).card ≤ 1 := by omega
  obtain ⟨d0, d1, hAeq, hd01, _, _⟩ := privates_of G H
  have leaf_iff (x : V) (hx : x ∈ ({q, r, s} : Finset V)) :
      x ∈ H.attachSupport H.A ↔ (G.neighborFinset x ∩ H.A).Nonempty := by
    constructor
    · intro hx'; exact (mem_filter.1 hx').2
    · intro hne
      refine mem_filter.2 ⟨?_, hne⟩
      have : x ∈ ({p, q, r, s} : Finset V) := by
        simp only [mem_insert, mem_singleton] at hx ⊢; tauto
      simpa [← hC] using this
  have exists_leaf :
      ∃ leaf ∈ ({q, r, s} : Finset V),
        ∀ x ∈ ({q, r, s} : Finset V), x ≠ leaf →
          G.neighborFinset x ∩ H.A = ∅ := by
    by_cases hpos : (H.attachSupport H.A ∩ {q, r, s}).Nonempty
    · obtain ⟨leaf, hleaf⟩ := hpos
      have hleaf_mem : leaf ∈ ({q, r, s} : Finset V) := (mem_inter.1 hleaf).2
      refine ⟨leaf, hleaf_mem, ?_⟩
      intro x hx hne
      by_contra hne'
      have hx_att : x ∈ H.attachSupport H.A ∩ {q, r, s} :=
        mem_inter.2 ⟨(leaf_iff x hx).2 (Finset.nonempty_iff_ne_empty.2 hne'), hx⟩
      have : ({leaf, x} : Finset V) ⊆ H.attachSupport H.A ∩ {q, r, s} := by
        intro y hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl <;> first | exact hleaf | exact hx_att
      have hcard2 : ({leaf, x} : Finset V).card = 2 := by
        simp [card_insert_of_notMem, hne.symm]
      have : 2 ≤ (H.attachSupport H.A ∩ {q, r, s}).card :=
        hcard2 ▸ card_le_card this
      omega
    · refine ⟨q, by simp, ?_⟩
      intro x hx _
      by_contra hne
      have : x ∈ H.attachSupport H.A ∩ {q, r, s} :=
        mem_inter.2 ⟨(leaf_iff x hx).2 (Finset.nonempty_iff_ne_empty.2 hne), hx⟩
      exact absurd this (by simpa [Finset.not_nonempty_iff_eq_empty.1 hpos])
  obtain ⟨leaf, hleaf_mem, hothers⟩ := exists_leaf
  -- Apply WKE after renaming so the distinguished leaf is `q'`
  have apply_named (q' r' s' : V) (hC' : H.C = {p, q', r', s'})
      (hstar' : G.Adj p r' ∧ G.Adj p s')
      (honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, q') ∨ s(x, y) = s(p, r') ∨ s(x, y) = s(p, s'))
      (hq_eq : leaf = q') : IsWKE (linkGraph G H.u) := by
    have ⟨_hpq', hpr', hps', hqr', hqs', _hrs'⟩ := core4_distinct G H hC'
    have hatt_rs : ∀ x ∈ ({r', s'} : Finset V), G.neighborFinset x ∩ H.A = ∅ := by
      intro x hx
      have hxC : x ∈ H.C := by
        rw [hC']; simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> simp
      have hxL : x ∈ ({q, r, s} : Finset V) := by
        have : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hxC
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with hp | h
        · subst hp
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact absurd rfl hpr'
          · exact absurd rfl hps'
        · exact h
      have hx_ne : x ≠ leaf := by
        intro heq
        have hx_eq_q : x = q' := by rw [← hq_eq, heq]
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hqr' hx_eq_q.symm
        · exact hqs' hx_eq_q.symm
      exact hothers x hxL hx_ne
    by_cases hpriv : G.Adj d0 d1
    · exact star_wke_private_edge G H p q' r' s' hC' hstar' honly' d0 d1 hAeq hd01
        hpriv hatt_rs
    · by_cases hatt_q : (G.neighborFinset q' ∩ H.A).Nonempty
      · obtain ⟨di, hdi⟩ := hatt_q
        have hdiA : di ∈ H.A := (mem_inter.1 hdi).2
        have hdi' : di = d0 ∨ di = d1 := by rw [hAeq] at hdiA; simpa using hdiA
        have hqdi : G.Adj q' di := (G.mem_neighborFinset _ _).1 (mem_inter.1 hdi).1
        exact star_wke_one_leaf G H p q' r' s' hC' hstar' honly' d0 d1 di hAeq hdi'
          hpriv hqdi hatt_rs
      · have hatt_all : ∀ x ∈ ({q', r', s'} : Finset V),
            G.neighborFinset x ∩ H.A = ∅ := by
          intro x hx
          by_cases hxq : x = q'
          · subst hxq
            simpa [Finset.not_nonempty_iff_eq_empty] using hatt_q
          · have hx_rs : x ∈ ({r', s'} : Finset V) := by
              simp only [mem_insert, mem_singleton] at hx ⊢
              rcases hx with rfl | h
              · exact absurd rfl hxq
              · exact h
            exact hatt_rs x hx_rs
        exact star_wke_no_attach_no_priv G H p q' r' s' hC' hstar' honly'
          d0 d1 hAeq hpriv hatt_all
  have hleaf_or : leaf = q ∨ leaf = r ∨ leaf = s := by
    simpa [mem_insert, mem_singleton] using hleaf_mem
  rcases hleaf_or with hq | hr | hs
  · exact hnot (apply_named q r s hC ⟨hstar.2.1, hstar.2.2⟩ honly hq)
  · have hC' : H.C = {p, r, q, s} := by rw [hC]; ext x; simp [or_comm, or_left_comm]
    have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, r) ∨ s(x, y) = s(p, q) ∨ s(x, y) = s(p, s) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    exact hnot (apply_named r q s hC' ⟨hstar.1, hstar.2.2⟩ honly' hr)
  · have hC' : H.C = {p, s, q, r} := by rw [hC]; ext x; simp [or_comm, or_left_comm]
    have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, s) ∨ s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    exact hnot (apply_named s q r hC' ⟨hstar.1, hstar.2.1⟩ honly' hs)

end StarCore

/-! ## Path-of-length-two core (Lemma 4.4) -/

namespace PathCore

open MatchingCore

lemma path_empty_outside_center (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hpriv : ¬ G.Adj d0 d1)
    (hqe : G.neighborFinset q ∩ H.A = ∅) (hre : G.neighborFinset r ∩ H.A = ∅)
    (hse : G.neighborFinset s ∩ H.A = ∅)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ x ∈ e, x ∉ ({H.v, p} : Finset V)) : False := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have haOut : a ∉ ({H.v, p} : Finset V) := hOut a (by simp)
  have hbOut : b ∉ ({H.v, p} : Finset V) := hOut b (by simp)
  have classify (x : V) (hxN : x ∈ G.neighborFinset H.u)
      (hxOut : x ∉ ({H.v, p} : Finset V)) : x ∈ H.C ∪ H.A ∧ x ≠ p := by
    rw [H.hNu] at hxN
    simp only [mem_insert, mem_union, mem_singleton] at hxN hxOut
    refine ⟨?_, fun hp => hxOut (Or.inr hp)⟩
    rcases hxN with rfl | hC' | hA'
    · exact absurd (Or.inl rfl) hxOut
    · exact mem_union_left _ hC'
    · exact mem_union_right _ hA'
  have haCl := classify a hab.1 haOut
  have hbCl := classify b hab.2.1 hbOut
  have no_att (x : V) (hx : x = q ∨ x = r ∨ x = s) :
      G.neighborFinset x ∩ H.A = ∅ := by
    rcases hx with rfl | rfl | rfl <;> assumption
  by_cases haC : a ∈ H.C
  · by_cases hbC : b ∈ H.C
    · have hem := honly a haC b hbC hG
      have hp_mem : p ∈ s(a, b) := by
        rcases hem with h | h
        · simpa [h] using (Sym2.mem_mk_left p q : p ∈ s(p, q))
        · simpa [h] using (Sym2.mem_mk_left p r : p ∈ s(p, r))
      have : a = p ∨ b = p := by simpa [Sym2.mem_iff, eq_comm] using hp_mem
      rcases this with rfl | rfl
      · exact haCl.2 rfl
      · exact hbCl.2 rfl
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha_l : a = q ∨ a = r ∨ a = s := by
        have : a ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact haC
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact absurd rfl haCl.2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have : b ∈ G.neighborFinset a ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
      simpa [no_att a ha_l] using this
  · have haA : a ∈ H.A := (mem_union.1 haCl.1).resolve_left haC
    by_cases hbC : b ∈ H.C
    · have hb_l : b = q ∨ b = r ∨ b = s := by
        have : b ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hbC
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact absurd rfl hbCl.2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have : a ∈ G.neighborFinset b ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
      simpa [no_att b hb_l] using this
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
      have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
      have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
      have : G.Adj d0 d1 := by
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hne
        · exact hG
        · exact hG.symm
        · exact absurd rfl hne
      exact hpriv this

/-- Outside `{v,p,s}` with no attachments at `q,r`: only possible edge is private. -/
lemma path_outside_zps (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (d0 d1 : V) (hAeq : H.A = {d0, d1})
    (hqe : G.neighborFinset q ∩ H.A = ∅) (hre : G.neighborFinset r ∩ H.A = ∅)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ x ∈ e, x ∉ ({H.v, p, s} : Finset V)) :
    e = s(d0, d1) := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have haOut : a ∉ ({H.v, p, s} : Finset V) := hOut a (by simp)
  have hbOut : b ∉ ({H.v, p, s} : Finset V) := hOut b (by simp)
  have classify (x : V) (hxN : x ∈ G.neighborFinset H.u)
      (hxOut : x ∉ ({H.v, p, s} : Finset V)) : x ∈ H.C ∪ H.A ∧ x ≠ p ∧ x ≠ s := by
    rw [H.hNu] at hxN
    simp only [mem_insert, mem_union, mem_singleton] at hxN hxOut
    refine ⟨?_, fun hp => hxOut (Or.inr (Or.inl hp)), fun hs => hxOut (Or.inr (Or.inr hs))⟩
    rcases hxN with rfl | hC' | hA'
    · exact absurd (Or.inl rfl) hxOut
    · exact mem_union_left _ hC'
    · exact mem_union_right _ hA'
  have haCl := classify a hab.1 haOut
  have hbCl := classify b hab.2.1 hbOut
  have no_att (x : V) (hx : x = q ∨ x = r) : G.neighborFinset x ∩ H.A = ∅ := by
    rcases hx with rfl | rfl <;> assumption
  by_cases haC : a ∈ H.C
  · by_cases hbC : b ∈ H.C
    · have hem := honly a haC b hbC hG
      have : a = p ∨ b = p := by
        rcases hem with h | h
        · have hp' : p ∈ s(a, b) := by simpa [h] using (Sym2.mem_mk_left p q)
          simpa [Sym2.mem_iff, eq_comm] using hp'
        · have hp' : p ∈ s(a, b) := by simpa [h] using (Sym2.mem_mk_left p r)
          simpa [Sym2.mem_iff, eq_comm] using hp'
      rcases this with rfl | rfl
      · exact absurd rfl haCl.2.1
      · exact absurd rfl hbCl.2.1
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha_qr : a = q ∨ a = r := by
        have : a ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact haC
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact absurd rfl haCl.2.1
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl haCl.2.2
      have : b ∈ G.neighborFinset a ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
      simpa [no_att a ha_qr] using this
  · have haA : a ∈ H.A := (mem_union.1 haCl.1).resolve_left haC
    by_cases hbC : b ∈ H.C
    · have hb_qr : b = q ∨ b = r := by
        have : b ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hbC
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact absurd rfl hbCl.2.1
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hbCl.2.2
      have : a ∈ G.neighborFinset b ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
      simpa [no_att b hb_qr] using this
    · have hbA : b ∈ H.A := (mem_union.1 hbCl.1).resolve_left hbC
      have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
      have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
      have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne

theorem path_leaf_attachment (H : HubConfig G)
    (_hconn : (linkGraph G H.u).Connected) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hedges : G.Adj p q ∧ G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r)) :
    (G.neighborFinset q ∩ H.A).Nonempty ∨ (G.neighborFinset r ∩ H.A).Nonempty := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hqe, hre⟩ := h
  have hqe' : G.neighborFinset q ∩ H.A = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hqe
  have hre' : G.neighborFinset r ∩ H.A = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hre
  obtain ⟨d0, d1, hAeq, hd01, _, _⟩ := privates_of G H
  have ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hpN := core_mem_Nu G H hpC
  have hqN := core_mem_Nu G H hqC
  have hrN := core_mem_Nu G H hrC
  have hsN := core_mem_Nu G H hsC
  have hzr := z_adj_core G H hrC
  have hzs := z_adj_core G H hsC
  have hz_ne_p := ne_z_of_core G H hpC
  have hz_ne_q := ne_z_of_core G H hqC
  have hz_ne_r := ne_z_of_core G H hrC
  have hz_ne_s := ne_z_of_core G H hsC
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  by_cases hpriv : G.Adj d0 d1
  · -- Case 1: private edge. Q={z,p,s}, M={d0d1, pq, zr}
    let Q : Finset V := {H.v, p, s}
    let M : Finset (Sym2 V) := {s(d0, d1), s(p, q), s(H.v, r)}
    have hd0N : d0 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
    have hd1N : d1 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
    have hz_ne_d0 := ne_z_of_priv G H hd0A
    have hz_ne_d1 := ne_z_of_priv G H hd1A
    have hp_ne_d0 := ne_core_priv G H hpC hd0A
    have hp_ne_d1 := ne_core_priv G H hpC hd1A
    have hq_ne_d0 := ne_core_priv G H hqC hd0A
    have hq_ne_d1 := ne_core_priv G H hqC hd1A
    have hr_ne_d0 := ne_core_priv G H hrC hd0A
    have hr_ne_d1 := ne_core_priv G H hrC hd1A
    have hQcard : Q.card = 3 := by
      change ({H.v, p, s} : Finset V).card = 3
      have h1 : H.v ∉ ({p, s} : Finset V) := by simp [hz_ne_p, hz_ne_s]
      have h2 : p ∉ ({s} : Finset V) := by simp [hps]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hne01 : s(d0, d1) ≠ s(p, q) := by
      intro heq
      have : d0 = p ∨ d0 = q := by
        simpa [Sym2.mem_iff] using
          (show d0 ∈ s(p, q) by simpa [← heq] using Sym2.mem_mk_left d0 d1)
      rcases this with rfl | rfl
      · exact hp_ne_d0.symm rfl
      · exact hq_ne_d0.symm rfl
    have hne02 : s(d0, d1) ≠ s(H.v, r) := by
      intro heq
      have : d0 = H.v ∨ d0 = r := by
        simpa [Sym2.mem_iff] using
          (show d0 ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left d0 d1)
      rcases this with rfl | rfl
      · exact hz_ne_d0 rfl
      · exact hr_ne_d0.symm rfl
    have hne12 : s(p, q) ≠ s(H.v, r) := by
      intro heq
      have : p = H.v ∨ p = r := by
        simpa [Sym2.mem_iff] using
          (show p ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left p q)
      rcases this with rfl | rfl
      · exact hz_ne_p rfl
      · exact hpr rfl
    have hMcard : M.card = 3 := by
      change ({s(d0, d1), s(p, q), s(H.v, r)} : Finset (Sym2 V)).card = 3
      have h1 : s(d0, d1) ∉ ({s(p, q), s(H.v, r)} : Finset (Sym2 V)) := by
        simp [hne01, hne02]
      have h2 : s(p, q) ∉ ({s(H.v, r)} : Finset (Sym2 V)) := by simp [hne12]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hdisj01 : Disjoint s(d0, d1).toFinset s(p, q).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hp_ne_d0.symm
      · exact hq_ne_d0.symm
      · exact hp_ne_d1.symm
      · exact hq_ne_d1.symm
    have hdisj02 : Disjoint s(d0, d1).toFinset s(H.v, r).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hz_ne_d0.symm
      · exact hr_ne_d0.symm
      · exact hz_ne_d1.symm
      · exact hr_ne_d1.symm
    have hdisj12 : Disjoint s(p, q).toFinset s(H.v, r).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hz_ne_p.symm
      · exact hpr
      · exact hz_ne_q.symm
      · exact hqr
    have hM : IsEdgeMatching (linkGraph G H.u) M := by
      refine ⟨?_, ?_⟩
      · intro e he; simp only [M, mem_insert, mem_singleton] at he
        rcases he with h | h | h
        · subst h; exact Prop31.link_edge G H.u d0 d1 hd0N hd1N hpriv
        · subst h; exact Prop31.link_edge G H.u p q hpN hqN hedges.1
        · subst h; exact Prop31.link_edge G H.u H.v r hzN hrN hzr
      · intro e he f hf hne'
        simp only [M, mem_insert, mem_singleton] at he hf
        rcases he with he | he | he <;> rcases hf with hf | hf | hf
        · subst he; subst hf; exact absurd rfl hne'
        · subst he; subst hf; exact hdisj01
        · subst he; subst hf; exact hdisj02
        · subst he; subst hf; exact hdisj01.symm
        · subst he; subst hf; exact absurd rfl hne'
        · subst he; subst hf; exact hdisj12
        · subst he; subst hf; exact hdisj02.symm
        · subst he; subst hf; exact hdisj12.symm
        · subst he; subst hf; exact absurd rfl hne'
    have : IsWKE (linkGraph G H.u) :=
      isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hQ => by
        have heq := path_outside_zps G H p q r s hC honly d0 d1 hAeq hqe' hre' he hQ
        simp only [M, mem_insert, mem_singleton, heq, true_or]⟩
    exact hnot this
  · by_cases hs_att : (G.neighborFinset s ∩ H.A).Nonempty
    · -- Case 2: s–di present. Q={z,p,s}, M={sdi, pq, zr}
      obtain ⟨di, hdi⟩ := hs_att
      have hdiA : di ∈ H.A := (mem_inter.1 hdi).2
      have hdi' : di = d0 ∨ di = d1 := by rw [hAeq] at hdiA; simpa using hdiA
      have hsdi : G.Adj s di := (G.mem_neighborFinset _ _).1 (mem_inter.1 hdi).1
      have hdiN : di ∈ G.neighborFinset H.u := by
        rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdiA)
      have hz_ne_di := ne_z_of_priv G H hdiA
      have hp_ne_di := ne_core_priv G H hpC hdiA
      have hq_ne_di := ne_core_priv G H hqC hdiA
      have hr_ne_di := ne_core_priv G H hrC hdiA
      have hs_ne_di := ne_core_priv G H hsC hdiA
      let Q : Finset V := {H.v, p, s}
      let M : Finset (Sym2 V) := {s(s, di), s(p, q), s(H.v, r)}
      have hQcard : Q.card = 3 := by
        change ({H.v, p, s} : Finset V).card = 3
        have h1 : H.v ∉ ({p, s} : Finset V) := by simp [hz_ne_p, hz_ne_s]
        have h2 : p ∉ ({s} : Finset V) := by simp [hps]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hne01 : s(s, di) ≠ s(p, q) := by
        intro heq
        have : s = p ∨ s = q := by
          simpa [Sym2.mem_iff] using
            (show s ∈ s(p, q) by simpa [← heq] using Sym2.mem_mk_left s di)
        rcases this with rfl | rfl
        · exact hps.symm rfl
        · exact hqs.symm rfl
      have hne02 : s(s, di) ≠ s(H.v, r) := by
        intro heq
        have : s = H.v ∨ s = r := by
          simpa [Sym2.mem_iff] using
            (show s ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left s di)
        rcases this with rfl | rfl
        · exact hz_ne_s.symm rfl
        · exact hrs.symm rfl
      have hne12 : s(p, q) ≠ s(H.v, r) := by
        intro heq
        have : p = H.v ∨ p = r := by
          simpa [Sym2.mem_iff] using
            (show p ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left p q)
        rcases this with rfl | rfl
        · exact hz_ne_p rfl
        · exact hpr rfl
      have hMcard : M.card = 3 := by
        change ({s(s, di), s(p, q), s(H.v, r)} : Finset (Sym2 V)).card = 3
        have h1 : s(s, di) ∉ ({s(p, q), s(H.v, r)} : Finset (Sym2 V)) := by
          simp [hne01, hne02]
        have h2 : s(p, q) ∉ ({s(H.v, r)} : Finset (Sym2 V)) := by simp [hne12]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hdisj01 : Disjoint s(s, di).toFinset s(p, q).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hps.symm
        · exact hqs.symm
        · exact hp_ne_di.symm
        · exact hq_ne_di.symm
      have hdisj02 : Disjoint s(s, di).toFinset s(H.v, r).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hz_ne_s.symm
        · exact hrs.symm
        · exact hz_ne_di.symm
        · exact hr_ne_di.symm
      have hdisj12 : Disjoint s(p, q).toFinset s(H.v, r).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hz_ne_p.symm
        · exact hpr
        · exact hz_ne_q.symm
        · exact hqr
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u s di hsN hdiN hsdi
          · subst h; exact Prop31.link_edge G H.u p q hpN hqN hedges.1
          · subst h; exact Prop31.link_edge G H.u H.v r hzN hrN hzr
        · intro e he f hf hne'
          simp only [M, mem_insert, mem_singleton] at he hf
          rcases he with he | he | he <;> rcases hf with hf | hf | hf
          · subst he; subst hf; exact absurd rfl hne'
          · subst he; subst hf; exact hdisj01
          · subst he; subst hf; exact hdisj02
          · subst he; subst hf; exact hdisj01.symm
          · subst he; subst hf; exact absurd rfl hne'
          · subst he; subst hf; exact hdisj12
          · subst he; subst hf; exact hdisj02.symm
          · subst he; subst hf; exact hdisj12.symm
          · subst he; subst hf; exact absurd rfl hne'
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hQ => by
          have heq := path_outside_zps G H p q r s hC honly d0 d1 hAeq hqe' hre' he hQ
          have hab : (linkGraph G H.u).Adj d0 d1 := by
            have hh := (mem_edgeFinset (G := linkGraph G H.u)).1 he
            simpa [heq] using hh
          exact (hpriv hab.2.2).elim⟩
      exact hnot this
    · -- Case 3: no private, no s-attach (already proved)
      have hse : G.neighborFinset s ∩ H.A = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using hs_att
      let Q : Finset V := {H.v, p}
      let M : Finset (Sym2 V) := {s(p, q), s(H.v, s)}
      have hne : s(p, q) ≠ s(H.v, s) := by
        intro heq
        have : p = H.v ∨ p = s := by
          simpa [Sym2.mem_iff] using
            (show p ∈ s(H.v, s) by simpa [← heq] using (Sym2.mem_mk_left p q))
        rcases this with rfl | rfl
        · exact hz_ne_p rfl
        · exact hps rfl
      have hdisj : Disjoint s(p, q).toFinset s(H.v, s).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hz_ne_p.symm
        · exact hps
        · exact hz_ne_q.symm
        · exact hqs
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h
          · subst h; exact Prop31.link_edge G H.u p q hpN hqN hedges.1
          · subst h; exact Prop31.link_edge G H.u H.v s hzN hsN hzs
        · intro e he f hf hne'
          simp only [M, mem_insert, mem_singleton] at he hf
          rcases he with he | he <;> rcases hf with hf | hf
          · subst he; subst hf; exact absurd rfl hne'
          · subst he; subst hf; exact hdisj
          · subst he; subst hf; exact hdisj.symm
          · subst he; subst hf; exact absurd rfl hne'
      have hQc : Q.card = 2 := by
        change ({H.v, p} : Finset V).card = 2
        rw [card_insert_of_notMem ((by simpa using hz_ne_p : H.v ∉ ({p} : Finset V))),
          card_singleton]
      have hMc : M.card = 2 := by
        change ({s(p, q), s(H.v, s)} : Finset (Sym2 V)).card = 2
        rw [card_insert_of_notMem ((by simpa using hne)), card_singleton]
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQc.trans hMc.symm), fun e he hQ =>
          (path_empty_outside_center G H p q r s hC honly d0 d1 hAeq hpriv
            hqe' hre' hse he hQ).elim⟩
      exact hnot this


end PathCore


/-- **Theorem 1.3 (Structural codegree-four reduction).** -/
theorem structural_codegree_four (H : HubConfig G) (hA1 : H.A1) (_hA2 : H.A2) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  -- Under (A1), cores with ≤1 edge are excluded (Prop 3.1).
  have hge : 2 ≤ H.numCoreEdges := by
    by_contra hlt
    have : H.numCoreEdges ≤ 1 := by omega
    exact prop31 G H hA1 this
  -- Remaining nine cores: matching / star / path / … certificates.
  -- Wired pieces: Prop 4.2 certificate exists under labelled 2K₂ attachments;
  -- Lemmas 4.3–4.4 restrict star/path links. Full case split deferred.
  sorry


end Tuza.CodegreeFour
