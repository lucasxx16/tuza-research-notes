import TuzaFormal.Reducibility
import TuzaFormal.Classify
import Mathlib.Data.Fintype.Perm

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

/-- Connectivity of the link *on its vertex set* `N(z)` (paper: the link is the graph
induced on `N(z)`). Vertices outside `N(z)` are isolated in `linkGraph` and are ignored.
NB: `(linkGraph G z).Connected` on all of `V` is unsatisfiable for a hub config (the hub
itself is isolated); an earlier version used it, making (A1) inconsistent. -/
def LinkConnected (z : V) : Prop :=
  ∀ a ∈ G.neighborFinset z, ∀ b ∈ G.neighborFinset z, (linkGraph G z).Reachable a b

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
  LinkConnected G H.u ∧ ¬ IsWKE (linkGraph G H.u) ∧
  LinkConnected G H.v ∧ ¬ IsWKE (linkGraph G H.v)

/-- (A2) common-neighbour degree budget. -/
def A2 : Prop :=
  ∀ x ∈ H.C,
    H.coreDeg x + (G.neighborFinset x ∩ H.A).card + (G.neighborFinset x ∩ H.B).card ≤ 5

/-- Swap hubs: private sides A↔B. -/
def swap : HubConfig G where
  u := H.v
  v := H.u
  huv := H.huv.symm
  C := H.C
  A := H.B
  B := H.A
  hC := by rw [H.hC, inter_comm]
  hCcard := H.hCcard
  hNu := H.hNv
  hNv := H.hNu
  hA := H.hB
  hB := H.hA
  hAdisj := H.hBdisj
  hBdisj := H.hAdisj
  hABdisj := H.hABdisj.symm
  hvA := H.huB
  huB := H.hvA
  hdu := H.hdv
  hdv := H.hdu

lemma A1.swap (h : H.A1) : H.swap.A1 :=
  ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩


/-- Lemma 2.2 (edge-count half): a 4-vertex core has at most 6 edges. -/
theorem core_edge_bound : H.numCoreEdges ≤ 6 := by
  have hle : H.numCoreEdges ≤ (H.C.powersetCard 2).card := card_le_card (filter_subset _ _)
  have : (H.C.powersetCard 2).card = 6 := by
    rw [card_powersetCard, H.hCcard]; decide
  omega

end HubConfig

/-- Puleo's consequence used by the exclusions ([1, Cor 4.12]): a connected graph on
`n ≥ 6` vertices with an independent set of size `n − 3` is WKE. Stated for the link
graph on its vertex set `N(z)` (vertices outside `N(z)` are isolated in `linkGraph` and do
not affect WKE). Taken as an axiom pending a formalization of Puleo's paper. -/
axiom puleo_large_indep {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (z : W)
    (hn : 6 ≤ (F.neighborFinset z).card) (hconn : LinkConnected F z)
    (I : Finset W) (hIN : I ⊆ F.neighborFinset z)
    (hI : I.card = (F.neighborFinset z).card - 3)
    (hind : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ (linkGraph F z).Adj a b) :
    IsWKE (linkGraph F z)


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
    (hconn : LinkConnected G H.u) (h1 : H.numCoreEdges = 1) :
    IsWKE (linkGraph G H.u) := by
  classical
  obtain ⟨p, q, hpC, hqC, hpq, hpqAdj, hunique⟩ := exists_unique_core_edge G H h1
  obtain ⟨d0, d1, hd01, hAeq⟩ := (card_eq_two (s := H.A)).1 H.hA
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
    have hNcard : (G.neighborFinset H.u).card = 7 := by
      simpa [← SimpleGraph.card_neighborFinset_eq_degree] using H.hdu
    refine puleo_large_indep G H.u (by omega) hconn
      ({r, s, d0, d1} : Finset V) ?_ ?_ hind
    · intro w hw
      rw [H.hNu]
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact mem_insert_of_mem (mem_union_left _ hrC)
      · exact mem_insert_of_mem (mem_union_left _ hsC)
      · exact mem_insert_of_mem (mem_union_right _ (by rw [hAeq]; simp))
      · exact mem_insert_of_mem (mem_union_right _ (by rw [hAeq]; simp))
    · have hcard : ({r, s, d0, d1} : Finset V).card = 4 := by
        simp [card_insert_of_notMem, hrs, hs_ne_d0, hs_ne_d1, D.rd0, D.rd1, D.d01]
      rw [hcard, hNcard]


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
    have hWKE : IsWKE (linkGraph G H.u) :=
      puleo_large_indep G H.u (by omega) hA1.1 H.C
        (fun w hw => by rw [H.hNu]; exact mem_insert_of_mem (mem_union_left _ hw))
        (by rw [H.hCcard, hNcard]) hind
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
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
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

/-- `v` is not adjacent to a private vertex in `A`. -/
lemma not_adj_hub_priv (H : HubConfig G) {d : V} (hd : d ∈ H.A) : ¬ G.Adj H.v d := by
  intro h
  have : d ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 h
  rw [H.hNv] at this
  simp only [mem_insert, mem_union] at this
  rcases this with rfl | hC | hB
  · have huA : H.u ∉ H.A := by
      intro hu
      have : H.u ∉ G.neighborFinset H.u :=
        fun hn => G.irrefl ((G.mem_neighborFinset _ _).1 hn)
      rw [H.hNu] at this
      exact this (mem_insert_of_mem (mem_union_right _ hu))
    exact huA hd
  · exact Finset.disjoint_left.1 H.hAdisj hd hC
  · exact Finset.disjoint_left.1 H.hABdisj hd hB

/-- Lemma 4.1(1) continuation: each private has a core neighbor. -/
theorem lemma41_priv_has_core (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hd01 : d0 ≠ d1) :
    (G.neighborFinset d0 ∩ H.C).Nonempty ∧
    (G.neighborFinset d1 ∩ H.C).Nonempty := by
  classical
  have hnopriv := lemma41_no_private G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have hNcard : (G.neighborFinset H.u).card = 7 := by
    simpa [← SimpleGraph.card_neighborFinset_eq_degree] using H.hdu
  have aux (d : V) (hdA : d ∈ H.A) :
      (G.neighborFinset d ∩ H.C).Nonempty := by
    by_contra hempty
    have hempty' : G.neighborFinset d ∩ H.C = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hempty
    have hdeg0 : (linkGraph G H.u).degree d = 0 := by
      simp only [← card_neighborFinset_eq_degree]
      refine card_eq_zero.2 (eq_empty_iff_forall_notMem.2 ?_)
      intro x hx
      have hAdj : (linkGraph G H.u).Adj d x := (mem_neighborFinset _ _ _).1 hx
      have hG : G.Adj d x := hAdj.2.2
      have hxN := hAdj.2.1
      rw [H.hNu] at hxN
      simp only [mem_insert, mem_union] at hxN
      rcases hxN with rfl | hC' | hA'
      · exact not_adj_hub_priv G H hdA hG.symm
      · have : x ∈ G.neighborFinset d ∩ H.C :=
          mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hC'⟩
        simpa [hempty'] using this
      · have hxA : x ∈ H.A := hA'
        have hxne : d ≠ x := fun eq => G.irrefl (eq ▸ hG)
        have hd' : d = d0 ∨ d = d1 := by rw [hAeq] at hdA; simpa using hdA
        have hx' : x = d0 ∨ x = d1 := by rw [hAeq] at hxA; simpa using hxA
        have : G.Adj d0 d1 := by
          rcases hd' with rfl | rfl <;> rcases hx' with rfl | rfl
          · exact absurd rfl hxne
          · exact hG
          · exact hG.symm
          · exact absurd rfl hxne
        exact hnopriv this
    obtain ⟨y, hy, hyne⟩ : ∃ y ∈ G.neighborFinset H.u, y ≠ d := by
      by_contra h
      push Not at h
      have hsub : G.neighborFinset H.u ⊆ {d} := by
        intro z hz
        exact mem_singleton.2 (h z hz)
      have : (G.neighborFinset H.u).card ≤ 1 :=
        (card_le_card hsub).trans (by simp)
      omega
    exact (not_reachable_of_left_degree_zero hyne.symm hdeg0) (hconn d (by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdA)) y hy)
  exact ⟨aux d0 (by rw [hAeq]; simp), aux d1 (by rw [hAeq]; simp)⟩

/-- Lemma 4.1(2): the core edge `p0p1` meets a private neighbor. -/
theorem lemma41_edge_hit (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hd01 : d0 ≠ d1) :
    (G.neighborFinset p0 ∩ H.A).Nonempty ∨ (G.neighborFinset p1 ∩ H.A).Nonempty := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hp0e, hp1e⟩ := h
  have hp0e' : G.neighborFinset p0 ∩ H.A = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hp0e
  have hp1e' : G.neighborFinset p1 ∩ H.A = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hp1e
  have hnopriv := lemma41_no_private G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have ⟨hd0core, _hd1core⟩ :=
    lemma41_priv_has_core G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have hdist := core4_distinct G H hC
  obtain ⟨c, hc⟩ := hd0core
  have hcC : c ∈ H.C := (mem_inter.1 hc).2
  have hAdj : G.Adj d0 c := (G.mem_neighborFinset _ _).1 (mem_inter.1 hc).1
  have hc_q : c = q0 ∨ c = q1 := by
    have hcmem : c ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hcC
    simp only [mem_insert, mem_singleton] at hcmem
    rcases hcmem with hcp0 | hcp1 | hcq0 | hcq1
    · have : d0 ∈ G.neighborFinset p0 ∩ H.A := by
        rw [← hcp0]
        exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hAdj.symm, by rw [hAeq]; simp⟩
      exact (by simpa [hp0e'] using this : False).elim
    · have : d0 ∈ G.neighborFinset p1 ∩ H.A := by
        rw [← hcp1]
        exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hAdj.symm, by rw [hAeq]; simp⟩
      exact (by simpa [hp1e'] using this : False).elim
    · exact Or.inl hcq0
    · exact Or.inr hcq1
  -- WKE: Q = {z,q0,q1}, M = {p0p1, d0–c, z–(other q)}
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
  have hz_ne_q0 := ne_z_of_core G H hq0C
  have hz_ne_q1 := ne_z_of_core G H hq1C
  have hq01 := hdist.2.2.2.2.2
  have hp01 := hdist.1
  have hp0q0 := hdist.2.1
  have hp0q1 := hdist.2.2.1
  have hp1q0 := hdist.2.2.2.1
  have hp1q1 := hdist.2.2.2.2.1
  -- Outside edges of Q={z,q0,q1} are only p0p1
  have only_p_out (qj qk : V) (hqj_eq : qj = q0 ∨ qj = q1) (hqk_eq : qk = q0 ∨ qk = q1)
      (hqjk : qj ≠ qk)
      {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
      (hOut : ∀ x ∈ e, x ∉ ({H.v, q0, q1} : Finset V)) :
      e = s(p0, p1) := by
    revert he hOut
    refine Sym2.inductionOn e fun a b he hOut => ?_
    have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
    have hG : G.Adj a b := hab.2.2
    have haQ : a ∉ ({H.v, q0, q1} : Finset V) := hOut a (by simp)
    have hbQ : b ∉ ({H.v, q0, q1} : Finset V) := hOut b (by simp)
    have classify (x : V) (hxN : x ∈ G.neighborFinset H.u)
        (hxQ : x ∉ ({H.v, q0, q1} : Finset V)) : x ∈ ({p0, p1} : Finset V) ∪ H.A := by
      rw [H.hNu] at hxN
      simp only [mem_insert, mem_union, mem_singleton] at hxN hxQ
      rcases hxN with rfl | hC' | hA'
      · exact absurd (Or.inl rfl) hxQ
      · -- in C but not q0/q1 → p0 or p1
        have : x ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hC'
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact mem_union_left _ (by simp)
        · exact mem_union_left _ (by simp)
        · exact absurd (Or.inr (Or.inl rfl)) hxQ
        · exact absurd (Or.inr (Or.inr rfl)) hxQ
      · exact mem_union_right _ hA'
    have haCl := classify a hab.1 haQ
    have hbCl := classify b hab.2.1 hbQ
    by_cases haC : a ∈ ({p0, p1} : Finset V)
    · by_cases hbC : b ∈ ({p0, p1} : Finset V)
      · -- both in {p0,p1}: must be the core edge
        have ha' : a = p0 ∨ a = p1 := by simpa using haC
        have hb' : b = p0 ∨ b = p1 := by simpa using hbC
        have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hne
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hne
      · -- b ∈ A, a ∈ {p0,p1}: attachment at p — forbidden
        have hbA : b ∈ H.A := (mem_union.1 hbCl).resolve_left hbC
        have ha' : a = p0 ∨ a = p1 := by simpa using haC
        have : b ∈ G.neighborFinset a ∩ H.A :=
          mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
        rcases ha' with rfl | rfl
        · simpa [hp0e'] using this
        · simpa [hp1e'] using this
    · have haA : a ∈ H.A := (mem_union.1 haCl).resolve_left haC
      by_cases hbC : b ∈ ({p0, p1} : Finset V)
      · have hb' : b = p0 ∨ b = p1 := by simpa using hbC
        have : a ∈ G.neighborFinset b ∩ H.A :=
          mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
        rcases hb' with rfl | rfl
        · simpa [hp0e'] using this
        · simpa [hp1e'] using this
      · -- both in A: private edge
        have hbA : b ∈ H.A := (mem_union.1 hbCl).resolve_left hbC
        have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
        have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
        have hne : a ≠ b := fun eq => G.irrefl (eq ▸ hG)
        have : G.Adj d0 d1 := by
          rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
          · exact absurd rfl hne
          · exact hG
          · exact hG.symm
          · exact absurd rfl hne
        exact (hnopriv this).elim
  -- Case split on which q-endpoint is c (avoid subst destroying names)
  rcases hc_q with hc0 | hc1
  · -- c = q0, other = q1
    let Q : Finset V := {H.v, q0, q1}
    let M : Finset (Sym2 V) := {s(p0, p1), s(d0, q0), s(H.v, q1)}
    have hAdj' : G.Adj d0 q0 := by rwa [hc0] at hAdj
    have hzr := z_adj_core G H hq1C
    have hQcard : Q.card = 3 := by
      change ({H.v, q0, q1} : Finset V).card = 3
      have h1 : H.v ∉ ({q0, q1} : Finset V) := by simp [hz_ne_q0, hz_ne_q1]
      have h2 : q0 ∉ ({q1} : Finset V) := by simp [hq01]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hne01 : s(p0, p1) ≠ s(d0, q0) := by
      intro heq
      have : p0 = d0 ∨ p0 = q0 := by
        simpa [Sym2.mem_iff] using
          (show p0 ∈ s(d0, q0) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
      rcases this with rfl | rfl
      · exact (ne_core_priv G H hp0C hd0A) rfl
      · exact hp0q0 rfl
    have hne02 : s(p0, p1) ≠ s(H.v, q1) := by
      intro heq
      have : p0 = H.v ∨ p0 = q1 := by
        simpa [Sym2.mem_iff] using
          (show p0 ∈ s(H.v, q1) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
      rcases this with rfl | rfl
      · exact (ne_z_of_core G H hp0C) rfl
      · exact hp0q1 rfl
    have hne12 : s(d0, q0) ≠ s(H.v, q1) := by
      intro heq
      have : d0 = H.v ∨ d0 = q1 := by
        simpa [Sym2.mem_iff] using
          (show d0 ∈ s(H.v, q1) by simpa [← heq] using Sym2.mem_mk_left d0 q0)
      rcases this with rfl | rfl
      · exact (ne_z_of_priv G H hd0A) rfl
      · exact (ne_core_priv G H hq1C hd0A).symm rfl
    have hMcard : M.card = 3 := by
      change ({s(p0, p1), s(d0, q0), s(H.v, q1)} : Finset (Sym2 V)).card = 3
      have h1 : s(p0, p1) ∉ ({s(d0, q0), s(H.v, q1)} : Finset (Sym2 V)) := by
        simp [hne01, hne02]
      have h2 : s(d0, q0) ∉ ({s(H.v, q1)} : Finset (Sym2 V)) := by simp [hne12]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hdisj01 : Disjoint s(p0, p1).toFinset s(d0, q0).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ne_core_priv G H hp0C hd0A
      · exact hp0q0
      · exact ne_core_priv G H hp1C hd0A
      · exact hp1q0
    have hdisj02 : Disjoint s(p0, p1).toFinset s(H.v, q1).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (ne_z_of_core G H hp0C).symm
      · exact hp0q1
      · exact (ne_z_of_core G H hp1C).symm
      · exact hp1q1
    have hdisj12 : Disjoint s(d0, q0).toFinset s(H.v, q1).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (ne_z_of_priv G H hd0A).symm
      · exact (ne_core_priv G H hq1C hd0A).symm
      · exact hz_ne_q0.symm
      · exact hq01
    have hM : IsEdgeMatching (linkGraph G H.u) M := by
      refine ⟨?_, ?_⟩
      · intro e he; simp only [M, mem_insert, mem_singleton] at he
        rcases he with h | h | h
        · subst h; exact Prop31.link_edge G H.u p0 p1 hp0N hp1N hcore.1
        · subst h; exact Prop31.link_edge G H.u d0 q0 hd0N hq0N hAdj'
        · subst h; exact Prop31.link_edge G H.u H.v q1 hzN hq1N hzr
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
        have heq := only_p_out q0 q1 (Or.inl rfl) (Or.inr rfl) hq01 he
          (by intro x hx; simpa [Q] using hQ x hx)
        simp only [M, mem_insert, mem_singleton, heq, true_or]⟩
    exact hnot this
  · -- c = q1, other = q0
    let Q : Finset V := {H.v, q0, q1}
    let M : Finset (Sym2 V) := {s(p0, p1), s(d0, q1), s(H.v, q0)}
    have hAdj' : G.Adj d0 q1 := by rwa [hc1] at hAdj
    have hzr := z_adj_core G H hq0C
    have hQcard : Q.card = 3 := by
      change ({H.v, q0, q1} : Finset V).card = 3
      have h1 : H.v ∉ ({q0, q1} : Finset V) := by simp [hz_ne_q0, hz_ne_q1]
      have h2 : q0 ∉ ({q1} : Finset V) := by simp [hq01]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hne01 : s(p0, p1) ≠ s(d0, q1) := by
      intro heq
      have : p0 = d0 ∨ p0 = q1 := by
        simpa [Sym2.mem_iff] using
          (show p0 ∈ s(d0, q1) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
      rcases this with rfl | rfl
      · exact (ne_core_priv G H hp0C hd0A) rfl
      · exact hp0q1 rfl
    have hne02 : s(p0, p1) ≠ s(H.v, q0) := by
      intro heq
      have : p0 = H.v ∨ p0 = q0 := by
        simpa [Sym2.mem_iff] using
          (show p0 ∈ s(H.v, q0) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
      rcases this with rfl | rfl
      · exact (ne_z_of_core G H hp0C) rfl
      · exact hp0q0 rfl
    have hne12 : s(d0, q1) ≠ s(H.v, q0) := by
      intro heq
      have : d0 = H.v ∨ d0 = q0 := by
        simpa [Sym2.mem_iff] using
          (show d0 ∈ s(H.v, q0) by simpa [← heq] using Sym2.mem_mk_left d0 q1)
      rcases this with rfl | rfl
      · exact (ne_z_of_priv G H hd0A) rfl
      · exact (ne_core_priv G H hq0C hd0A).symm rfl
    have hMcard : M.card = 3 := by
      change ({s(p0, p1), s(d0, q1), s(H.v, q0)} : Finset (Sym2 V)).card = 3
      have h1 : s(p0, p1) ∉ ({s(d0, q1), s(H.v, q0)} : Finset (Sym2 V)) := by
        simp [hne01, hne02]
      have h2 : s(d0, q1) ∉ ({s(H.v, q0)} : Finset (Sym2 V)) := by simp [hne12]
      rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
    have hdisj01 : Disjoint s(p0, p1).toFinset s(d0, q1).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ne_core_priv G H hp0C hd0A
      · exact hp0q1
      · exact ne_core_priv G H hp1C hd0A
      · exact hp1q1
    have hdisj02 : Disjoint s(p0, p1).toFinset s(H.v, q0).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (ne_z_of_core G H hp0C).symm
      · exact hp0q0
      · exact (ne_z_of_core G H hp1C).symm
      · exact hp1q0
    have hdisj12 : Disjoint s(d0, q1).toFinset s(H.v, q0).toFinset := by
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
      refine Finset.disjoint_iff_ne.2 ?_
      intro a ha b hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (ne_z_of_priv G H hd0A).symm
      · exact (ne_core_priv G H hq0C hd0A).symm
      · exact hz_ne_q1.symm
      · exact hq01.symm
    have hM : IsEdgeMatching (linkGraph G H.u) M := by
      refine ⟨?_, ?_⟩
      · intro e he; simp only [M, mem_insert, mem_singleton] at he
        rcases he with h | h | h
        · subst h; exact Prop31.link_edge G H.u p0 p1 hp0N hp1N hcore.1
        · subst h; exact Prop31.link_edge G H.u d0 q1 hd0N hq1N hAdj'
        · subst h; exact Prop31.link_edge G H.u H.v q0 hzN hq0N hzr
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
        have heq := only_p_out q1 q0 (Or.inr rfl) (Or.inl rfl) hq01.symm he
          (by intro x hx; simpa [Q] using hQ x hx)
        simp only [M, mem_insert, mem_singleton, heq, true_or]⟩
    exact hnot this

/-- Crossed private matching on a labelled core edge. -/
def HasCrossedAttach (G : SimpleGraph V) (p0 p1 d0 d1 : V) : Prop :=
  (G.Adj p0 d0 ∧ G.Adj p1 d1) ∨ (G.Adj p0 d1 ∧ G.Adj p1 d0)

/-- Lemma 4.1(3): crossed private matching on some core edge. -/
theorem lemma41_cross (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1)) :
    ∃ d0 d1, H.A = {d0, d1} ∧
      (HasCrossedAttach G p0 p1 d0 d1 ∨ HasCrossedAttach G q0 q1 d0 d1) := by
  obtain ⟨d0, d1, hAeq, hd01, _, _⟩ := privates_of G H
  have hnopriv := lemma41_no_private G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have hprivcore :=
    lemma41_priv_has_core G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have hhit_p := lemma41_edge_hit G H hconn hnot p0 p1 q0 q1 hC hcore honly d0 d1 hAeq hd01
  have hhit_q : (G.neighborFinset q0 ∩ H.A).Nonempty ∨
      (G.neighborFinset q1 ∩ H.A).Nonempty := by
    have hC' : H.C = {q0, q1, p0, p1} := by rw [hC]; ext x; simp [or_comm, or_left_comm]
    have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(q0, q1) ∨ s(x, y) = s(p0, p1) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with h | h <;> simp [h, or_comm]
    simpa using lemma41_edge_hit G H hconn hnot q0 q1 p0 p1 hC'
      ⟨hcore.2, hcore.1⟩ honly' d0 d1 hAeq hd01
  refine ⟨d0, d1, hAeq, ?_⟩
  by_contra hcross
  push Not at hcross
  obtain ⟨hnop, hnoq⟩ := hcross
  -- Unfold ¬HasCrossedAttach
  simp only [HasCrossedAttach, not_or, not_and] at hnop hnoq
  have hdist := core4_distinct G H hC
  have hp0C : p0 ∈ H.C := by rw [hC]; simp
  have hp1C : p1 ∈ H.C := by rw [hC]; simp
  have hq0C : q0 ∈ H.C := by rw [hC]; simp
  have hq1C : q1 ∈ H.C := by rw [hC]; simp
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  -- Exactly-one-endpoint vs both-endpoints
  by_cases hone_p :
      ¬((G.neighborFinset p0 ∩ H.A).Nonempty ∧ (G.neighborFinset p1 ∩ H.A).Nonempty)
  · by_cases hone_q :
        ¬((G.neighborFinset q0 ∩ H.A).Nonempty ∧ (G.neighborFinset q1 ∩ H.A).Nonempty)
    · -- Case: one-sided on both core edges. Pick p*, q*; Q={z,p*,q*} covers the link.
      -- Choose p* among {p0,p1} that may attach (from hhit_p), similarly q*.
      have ⟨pstar, hpstar, hpstar_att, hpother_empty⟩ :
          ∃ pstar ∈ ({p0, p1} : Finset V),
            (G.neighborFinset pstar ∩ H.A).Nonempty ∧
            ∀ p' ∈ ({p0, p1} : Finset V), p' ≠ pstar →
              G.neighborFinset p' ∩ H.A = ∅ := by
        rcases hhit_p with h0 | h1
        · refine ⟨p0, by simp, h0, ?_⟩
          intro p' hp' hne
          have hp'1 : p' = p1 := by
            simp only [mem_insert, mem_singleton] at hp'
            rcases hp' with heq | heq
            · exact absurd heq hne
            · exact heq
          rw [hp'1]
          have : ¬(G.neighborFinset p1 ∩ H.A).Nonempty := by
            intro h1'
            exact hone_p ⟨h0, h1'⟩
          simpa [Finset.not_nonempty_iff_eq_empty] using this
        · refine ⟨p1, by simp, h1, ?_⟩
          intro p' hp' hne
          have hp'0 : p' = p0 := by
            simp only [mem_insert, mem_singleton] at hp'
            rcases hp' with heq | heq
            · exact heq
            · exact absurd heq hne
          rw [hp'0]
          have : ¬(G.neighborFinset p0 ∩ H.A).Nonempty := by
            intro h0'
            exact hone_p ⟨h0', h1⟩
          simpa [Finset.not_nonempty_iff_eq_empty] using this
      have ⟨qstar, hqstar, hqstar_att, hqother_empty⟩ :
          ∃ qstar ∈ ({q0, q1} : Finset V),
            (G.neighborFinset qstar ∩ H.A).Nonempty ∧
            ∀ q' ∈ ({q0, q1} : Finset V), q' ≠ qstar →
              G.neighborFinset q' ∩ H.A = ∅ := by
        rcases hhit_q with h0 | h1
        · refine ⟨q0, by simp, h0, ?_⟩
          intro q' hq' hne
          have hq'1 : q' = q1 := by
            simp only [mem_insert, mem_singleton] at hq'
            rcases hq' with heq | heq
            · exact absurd heq hne
            · exact heq
          rw [hq'1]
          have : ¬(G.neighborFinset q1 ∩ H.A).Nonempty := by
            intro h1'; exact hone_q ⟨h0, h1'⟩
          simpa [Finset.not_nonempty_iff_eq_empty] using this
        · refine ⟨q1, by simp, h1, ?_⟩
          intro q' hq' hne
          have hq'0 : q' = q0 := by
            simp only [mem_insert, mem_singleton] at hq'
            rcases hq' with heq | heq
            · exact heq
            · exact absurd heq hne
          rw [hq'0]
          have : ¬(G.neighborFinset q0 ∩ H.A).Nonempty := by
            intro h0'; exact hone_q ⟨h0', h1⟩
          simpa [Finset.not_nonempty_iff_eq_empty] using this
      obtain ⟨di, hdi⟩ := hpstar_att
      have hdiA : di ∈ H.A := (mem_inter.1 hdi).2
      have hAdj_di : G.Adj pstar di := (G.mem_neighborFinset _ _).1 (mem_inter.1 hdi).1
      have hzN := opposite_hub_mem G H
      have hpstarC : pstar ∈ H.C := by
        have : pstar = p0 ∨ pstar = p1 := by simpa using hpstar
        rcases this with heq | heq <;> (rw [heq]; assumption)
      have hqstarC : qstar ∈ H.C := by
        have : qstar = q0 ∨ qstar = q1 := by simpa using hqstar
        rcases this with heq | heq <;> (rw [heq]; assumption)
      obtain ⟨pmate, hpm_ne, hpmeq⟩ :
          ∃ pm, pm ≠ pstar ∧ ({pstar, pm} : Finset V) = {p0, p1} := by
        have hps : pstar = p0 ∨ pstar = p1 := by simpa using hpstar
        rcases hps with heq | heq
        · have hne : p1 ≠ pstar := by rw [heq]; exact hdist.1.symm
          have hf : ({pstar, p1} : Finset V) = {p0, p1} := by rw [heq]
          exact ⟨p1, hne, hf⟩
        · have hne : p0 ≠ pstar := by rw [heq]; exact hdist.1
          have hf : ({pstar, p0} : Finset V) = {p0, p1} := by
            rw [heq]; ext x; simp [or_comm]
          exact ⟨p0, hne, hf⟩
      obtain ⟨qmate, hqm_ne, hqmeq⟩ :
          ∃ qm, qm ≠ qstar ∧ ({qstar, qm} : Finset V) = {q0, q1} := by
        have hqs : qstar = q0 ∨ qstar = q1 := by simpa using hqstar
        rcases hqs with heq | heq
        · have hne : q1 ≠ qstar := by rw [heq]; exact hdist.2.2.2.2.2.symm
          have hf : ({qstar, q1} : Finset V) = {q0, q1} := by rw [heq]
          exact ⟨q1, hne, hf⟩
        · have hne : q0 ≠ qstar := by rw [heq]; exact hdist.2.2.2.2.2
          have hf : ({qstar, q0} : Finset V) = {q0, q1} := by
            rw [heq]; ext x; simp [or_comm]
          exact ⟨q0, hne, hf⟩
      have hpmate_in : pmate ∈ ({p0, p1} : Finset V) := by
        have : pmate ∈ ({pstar, pmate} : Finset V) := by simp
        rwa [hpmeq] at this
      have hqmate_in : qmate ∈ ({q0, q1} : Finset V) := by
        have : qmate ∈ ({qstar, qmate} : Finset V) := by simp
        rwa [hqmeq] at this
      have hpmateC : pmate ∈ H.C := by
        simp only [mem_insert, mem_singleton] at hpmate_in
        rcases hpmate_in with heq | heq <;> (rw [heq]; assumption)
      have hqmateC : qmate ∈ H.C := by
        simp only [mem_insert, mem_singleton] at hqmate_in
        rcases hqmate_in with heq | heq <;> (rw [heq]; assumption)
      have hpother : G.neighborFinset pmate ∩ H.A = ∅ :=
        hpother_empty pmate hpmate_in hpm_ne
      have hqother : G.neighborFinset qmate ∩ H.A = ∅ :=
        hqother_empty qmate hqmate_in hqm_ne
      have hpstarN := core_mem_Nu G H hpstarC
      have hpmateN := core_mem_Nu G H hpmateC
      have hq0N := core_mem_Nu G H hq0C
      have hq1N := core_mem_Nu G H hq1C
      have hdiN : di ∈ G.neighborFinset H.u := by
        rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdiA)
      have hz_pm := z_adj_core G H hpmateC
      have hz_ne_ps := ne_z_of_core G H hpstarC
      have hz_ne_qs := ne_z_of_core G H hqstarC
      have hz_ne_q0 := ne_z_of_core G H hq0C
      have hz_ne_q1 := ne_z_of_core G H hq1C
      have hps_ne_qs : pstar ≠ qstar := by
        intro heq
        have hps : pstar = p0 ∨ pstar = p1 := by simpa using hpstar
        have hqs : qstar = q0 ∨ qstar = q1 := by simpa using hqstar
        rcases hps with hp | hp <;> rcases hqs with hq | hq
        · exact hdist.2.1 (hp.symm.trans (heq.trans hq))
        · exact hdist.2.2.1 (hp.symm.trans (heq.trans hq))
        · exact hdist.2.2.2.1 (hp.symm.trans (heq.trans hq))
        · exact hdist.2.2.2.2.1 (hp.symm.trans (heq.trans hq))
      let Q : Finset V := {H.v, pstar, qstar}
      let M : Finset (Sym2 V) := {s(di, pstar), s(H.v, pmate), s(q0, q1)}
      have hQcard : Q.card = 3 := by
        change ({H.v, pstar, qstar} : Finset V).card = 3
        have h1 : H.v ∉ ({pstar, qstar} : Finset V) := by simp [hz_ne_ps, hz_ne_qs]
        have h2 : pstar ∉ ({qstar} : Finset V) := by simp [hps_ne_qs]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hne01 : s(di, pstar) ≠ s(H.v, pmate) := by
        intro heq
        have : di = H.v ∨ di = pmate := by
          simpa [Sym2.mem_iff] using
            (show di ∈ s(H.v, pmate) by simpa [← heq] using Sym2.mem_mk_left di pstar)
        rcases this with rfl | rfl
        · exact (ne_z_of_priv G H hdiA) rfl
        · exact (ne_core_priv G H hpmateC hdiA).symm rfl
      have hne02 : s(di, pstar) ≠ s(q0, q1) := by
        intro heq
        have : di = q0 ∨ di = q1 := by
          simpa [Sym2.mem_iff] using
            (show di ∈ s(q0, q1) by simpa [← heq] using Sym2.mem_mk_left di pstar)
        rcases this with rfl | rfl
        · exact (ne_core_priv G H hq0C hdiA).symm rfl
        · exact (ne_core_priv G H hq1C hdiA).symm rfl
      have hne12 : s(H.v, pmate) ≠ s(q0, q1) := by
        intro heq
        have : H.v = q0 ∨ H.v = q1 := by
          simpa [Sym2.mem_iff] using
            (show H.v ∈ s(q0, q1) by simpa [← heq] using Sym2.mem_mk_left H.v pmate)
        rcases this with rfl | rfl
        · exact hz_ne_q0 rfl
        · exact hz_ne_q1 rfl
      have hMcard : M.card = 3 := by
        change ({s(di, pstar), s(H.v, pmate), s(q0, q1)} : Finset (Sym2 V)).card = 3
        have h1 : s(di, pstar) ∉ ({s(H.v, pmate), s(q0, q1)} : Finset (Sym2 V)) := by
          simp [hne01, hne02]
        have h2 : s(H.v, pmate) ∉ ({s(q0, q1)} : Finset (Sym2 V)) := by simp [hne12]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hdisj01 : Disjoint s(di, pstar).toFinset s(H.v, pmate).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (ne_z_of_priv G H hdiA).symm
        · exact (ne_core_priv G H hpmateC hdiA).symm
        · exact hz_ne_ps.symm
        · exact hpm_ne.symm
      have hdisj02 : Disjoint s(di, pstar).toFinset s(q0, q1).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        have hps : pstar = p0 ∨ pstar = p1 := by simpa using hpstar
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (ne_core_priv G H hq0C hdiA).symm
        · exact (ne_core_priv G H hq1C hdiA).symm
        · rcases hps with hp | hp
          · exact hp ▸ hdist.2.1
          · exact hp ▸ hdist.2.2.2.1
        · rcases hps with hp | hp
          · exact hp ▸ hdist.2.2.1
          · exact hp ▸ hdist.2.2.2.2.1
      have hdisj12 : Disjoint s(H.v, pmate).toFinset s(q0, q1).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb
        simp only [mem_insert, mem_singleton] at ha hb
        have hpm : pmate = p0 ∨ pmate = p1 := by simpa using hpmate_in
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hz_ne_q0
        · exact hz_ne_q1
        · rcases hpm with hp | hp
          · exact hp ▸ hdist.2.1
          · exact hp ▸ hdist.2.2.2.1
        · rcases hpm with hp | hp
          · exact hp ▸ hdist.2.2.1
          · exact hp ▸ hdist.2.2.2.2.1
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u di pstar hdiN hpstarN hAdj_di.symm
          · subst h; exact Prop31.link_edge G H.u H.v pmate hzN hpmateN hz_pm
          · subst h; exact Prop31.link_edge G H.u q0 q1 hq0N hq1N hcore.2
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
      -- Every link edge meets Q
      have hcover : ∀ e ∈ (linkGraph G H.u).edgeFinset, ∃ x ∈ e, x ∈ Q := by
        intro e he
        revert he
        refine Sym2.inductionOn e fun a b he => ?_
        have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
        have hG : G.Adj a b := hab.2.2
        by_cases haQ : a ∈ ({H.v, pstar, qstar} : Finset V)
        · exact ⟨a, by simp, by simpa [Q] using haQ⟩
        by_cases hbQ : b ∈ ({H.v, pstar, qstar} : Finset V)
        · exact ⟨b, by simp, by simpa [Q] using hbQ⟩
        have haN := hab.1
        have hbN := hab.2.1
        have classif (x : V) (hxN : x ∈ G.neighborFinset H.u)
            (hxQ : x ∉ ({H.v, pstar, qstar} : Finset V)) :
            x = pmate ∨ x = qmate ∨ x ∈ H.A := by
          rw [H.hNu] at hxN
          simp only [mem_insert, mem_union, mem_singleton, not_or] at hxN hxQ
          rcases hxN with rfl | hCmem | hAmem
          · exact absurd rfl hxQ.1
          · obtain ⟨hne_ps, hne_qs⟩ := hxQ.2
            have hxC4 : x ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hCmem
            simp only [mem_insert, mem_singleton] at hxC4
            -- x ∈ {p0,p1,q0,q1} \ {pstar,qstar} = {pmate,qmate}
            have hin_p : x ∈ ({p0, p1} : Finset V) → x = pmate := by
              intro hx
              have : x ∈ ({pstar, pmate} : Finset V) := by rwa [hpmeq]
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact absurd heq hne_ps
              · exact heq
            have hin_q : x ∈ ({q0, q1} : Finset V) → x = qmate := by
              intro hx
              have : x ∈ ({qstar, qmate} : Finset V) := by rwa [hqmeq]
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact absurd heq hne_qs
              · exact heq
            rcases hxC4 with hx | hx | hx | hx
            · exact Or.inl (hin_p (by simp [hx]))
            · exact Or.inl (hin_p (by simp [hx]))
            · exact Or.inr (Or.inl (hin_q (by simp [hx])))
            · exact Or.inr (Or.inl (hin_q (by simp [hx])))
          · exact Or.inr (Or.inr hAmem)
        have haCl := classif a haN haQ
        have hbCl := classif b hbN hbQ
        -- Case analysis on both outside → contradiction (no such edge)
        rcases haCl with ha | ha | haA
        · -- a = pmate
          rcases hbCl with hb | hb | hbA
          · exact False.elim (by rw [ha, hb] at hG; exact hG.ne rfl)
          · -- pmate–qmate
            have hG' : G.Adj pmate qmate := by rwa [ha, hb] at hG
            rcases honly pmate hpmateC qmate hqmateC hG' with hpedge | hqedge
            · have : qmate ∈ ({p0, p1} : Finset V) := by
                have : qmate ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              have hq_in_p := this
              have hq_in_q := hqmate_in
              simp only [mem_insert, mem_singleton] at hq_in_p hq_in_q
              rcases hq_in_p with hq | hq <;> rcases hq_in_q with hr | hr
              · exact False.elim (hdist.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.2.2.1 (hq.symm.trans hr))
            · have : pmate ∈ ({q0, q1} : Finset V) := by
                have : pmate ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              have hp_in_p := hpmate_in
              have hp_in_q := this
              simp only [mem_insert, mem_singleton] at hp_in_p hp_in_q
              rcases hp_in_p with hp | hp <;> rcases hp_in_q with hq | hq
              · exact False.elim (hdist.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.2.2.1 (hp.symm.trans hq))
          · have : b ∈ G.neighborFinset pmate ∩ H.A := by
              rw [← ha]; exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
            exact (by simpa [hpother] using this : False).elim
        · -- a = qmate
          rcases hbCl with hb | hb | hbA
          · have hG' : G.Adj qmate pmate := by rwa [ha, hb] at hG
            rcases honly qmate hqmateC pmate hpmateC hG' with hpedge | hqedge
            · have : qmate ∈ ({p0, p1} : Finset V) := by
                have : qmate ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              have hq_in_p := this
              have hq_in_q := hqmate_in
              simp only [mem_insert, mem_singleton] at hq_in_p hq_in_q
              rcases hq_in_p with hq | hq <;> rcases hq_in_q with hr | hr
              · exact False.elim (hdist.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.2.1 (hq.symm.trans hr))
              · exact False.elim (hdist.2.2.2.2.1 (hq.symm.trans hr))
            · have : pmate ∈ ({q0, q1} : Finset V) := by
                have : pmate ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              have hp_in_p := hpmate_in
              have hp_in_q := this
              simp only [mem_insert, mem_singleton] at hp_in_p hp_in_q
              rcases hp_in_p with hp | hp <;> rcases hp_in_q with hq | hq
              · exact False.elim (hdist.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.2.1 (hp.symm.trans hq))
              · exact False.elim (hdist.2.2.2.2.1 (hp.symm.trans hq))
          · exact False.elim (by rw [ha, hb] at hG; exact hG.ne rfl)
          · have : b ∈ G.neighborFinset qmate ∩ H.A := by
              rw [← ha]; exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG, hbA⟩
            exact (by simpa [hqother] using this : False).elim
        · -- a ∈ A
          rcases hbCl with hb | hb | hbA
          · have : a ∈ G.neighborFinset pmate ∩ H.A := by
              rw [← hb]; exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
            exact (by simpa [hpother] using this : False).elim
          · have : a ∈ G.neighborFinset qmate ∩ H.A := by
              rw [← hb]; exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hG.symm, haA⟩
            exact (by simpa [hqother] using this : False).elim
          · have ha' : a = d0 ∨ a = d1 := by rw [hAeq] at haA; simpa using haA
            have hb' : b = d0 ∨ b = d1 := by rw [hAeq] at hbA; simpa using hbA
            have hneab : a ≠ b := hG.ne
            have : G.Adj d0 d1 := by
              rcases ha' with haeq | haeq <;> rcases hb' with hbeq | hbeq
              · exact absurd (haeq.trans hbeq.symm) hneab
              · rwa [haeq, hbeq] at hG
              · exact (by rwa [haeq, hbeq] at hG : G.Adj d1 d0).symm
              · exact absurd (haeq.trans hbeq.symm) hneab
            exact (hnopriv this).elim
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut =>
          (hcover e he).elim fun x hx => absurd hx.2 (hOut x hx.1)⟩
      exact hnot this
    · -- Both q-endpoints attach: same-singleton on q-edge (dual).
      push Not at hone_q
      have hq0A : (G.neighborFinset q0 ∩ H.A).Nonempty := hone_q.1
      have hq1A : (G.neighborFinset q1 ∩ H.A).Nonempty := hone_q.2
      have same_sing : ∃ d, G.neighborFinset q0 ∩ H.A = {d} ∧
          G.neighborFinset q1 ∩ H.A = {d} := by
        have h0sub : G.neighborFinset q0 ∩ H.A ⊆ ({d0, d1} : Finset V) := by
          intro x hx; have : x ∈ H.A := (mem_inter.1 hx).2
          rw [hAeq] at this; simpa using this
        have h1sub : G.neighborFinset q1 ∩ H.A ⊆ ({d0, d1} : Finset V) := by
          intro x hx; have : x ∈ H.A := (mem_inter.1 hx).2
          rw [hAeq] at this; simpa using this
        have not_both (q : V) (hq : q = q0 ∨ q = q1) :
            ¬(G.Adj q d0 ∧ G.Adj q d1) := by
          intro ⟨hd0a, hd1a⟩
          rcases hq with rfl | rfl
          · obtain ⟨x, hx⟩ := hq1A
            have hxA : x ∈ H.A := (mem_inter.1 hx).2
            have hAdjx : G.Adj q1 x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
            have hx' : x = d0 ∨ x = d1 := by rw [hAeq] at hxA; simpa using hxA
            rcases hx' with rfl | rfl
            · exact hnoq.2 hd1a hAdjx
            · exact hnoq.1 hd0a hAdjx
          · obtain ⟨x, hx⟩ := hq0A
            have hxA : x ∈ H.A := (mem_inter.1 hx).2
            have hAdjx : G.Adj q0 x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
            have hx' : x = d0 ∨ x = d1 := by rw [hAeq] at hxA; simpa using hxA
            rcases hx' with rfl | rfl
            · exact hnoq.1 hAdjx hd1a
            · exact hnoq.2 hAdjx hd0a
        have card1 (q : V) (hne : (G.neighborFinset q ∩ H.A).Nonempty)
            (hsub : G.neighborFinset q ∩ H.A ⊆ ({d0, d1} : Finset V))
            (hnot : ¬(G.Adj q d0 ∧ G.Adj q d1)) :
            ∃ d, G.neighborFinset q ∩ H.A = {d} := by
          have hcard : (G.neighborFinset q ∩ H.A).card = 1 := by
            have hle : (G.neighborFinset q ∩ H.A).card ≤ 2 :=
              (card_le_card hsub).trans (by
                rw [card_insert_of_notMem (by simp [hd01]), card_singleton])
            have hge : 0 < (G.neighborFinset q ∩ H.A).card := card_pos.2 hne
            by_contra hne1
            have h2 : (G.neighborFinset q ∩ H.A).card = 2 := by omega
            have heqAB : G.neighborFinset q ∩ H.A = {d0, d1} := by
              refine eq_of_subset_of_card_le hsub ?_
              have hcard01 : ({d0, d1} : Finset V).card = 2 := by
                rw [card_insert_of_notMem (by simp [hd01]), card_singleton]
              omega
            have hd0m : d0 ∈ G.neighborFinset q ∩ H.A := by rw [heqAB]; simp
            have hd1m : d1 ∈ G.neighborFinset q ∩ H.A := by rw [heqAB]; simp
            exact hnot ⟨(G.mem_neighborFinset _ _).1 (mem_inter.1 hd0m).1,
              (G.mem_neighborFinset _ _).1 (mem_inter.1 hd1m).1⟩
          exact (card_eq_one.1 hcard)
        obtain ⟨e0, he0⟩ := card1 q0 hq0A h0sub (not_both q0 (Or.inl rfl))
        obtain ⟨e1, he1⟩ := card1 q1 hq1A h1sub (not_both q1 (Or.inr rfl))
        have heq01 : e0 = e1 := by
          by_contra hne
          have e0A : e0 ∈ H.A := by
            have : e0 ∈ G.neighborFinset q0 ∩ H.A := by rw [he0]; simp
            exact (mem_inter.1 this).2
          have e1A : e1 ∈ H.A := by
            have : e1 ∈ G.neighborFinset q1 ∩ H.A := by rw [he1]; simp
            exact (mem_inter.1 this).2
          have e0' : e0 = d0 ∨ e0 = d1 := by rw [hAeq] at e0A; simpa using e0A
          have e1' : e1 = d0 ∨ e1 = d1 := by rw [hAeq] at e1A; simpa using e1A
          have hAdj0 : G.Adj q0 e0 := by
            have : e0 ∈ G.neighborFinset q0 ∩ H.A := by rw [he0]; simp
            exact (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1
          have hAdj1 : G.Adj q1 e1 := by
            have : e1 ∈ G.neighborFinset q1 ∩ H.A := by rw [he1]; simp
            exact (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1
          rcases e0' with rfl | rfl <;> rcases e1' with rfl | rfl
          · exact absurd rfl hne
          · exact hnoq.1 hAdj0 hAdj1
          · exact hnoq.2 hAdj0 hAdj1
          · exact absurd rfl hne
        subst heq01
        exact ⟨e0, he0, he1⟩
      obtain ⟨d, hd0eq, hd1eq⟩ := same_sing
      have hdA : d ∈ H.A := by
        have : d ∈ G.neighborFinset q0 ∩ H.A := by rw [hd0eq]; simp
        exact (mem_inter.1 this).2
      have hd_eq : d = d0 ∨ d = d1 := by rw [hAeq] at hdA; simpa using hdA
      obtain ⟨dbar, hdbar_ne, hdbarA⟩ : ∃ db, db ≠ d ∧ db ∈ H.A := by
        rcases hd_eq with heq | heq
        · exact ⟨d1, fun h => hd01 (heq.symm.trans h.symm), hd1A⟩
        · exact ⟨d0, fun h => hd01 (h.trans heq), hd0A⟩
      have hA_pair : ({d, dbar} : Finset V) = {d0, d1} := by
        have hb : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
        rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
        · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
        · rw [hd0e, hb1]  -- {d0,d1}={d0,d1}
        · rw [hd1e, hb0]; ext x; simp [or_comm]
        · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
      have not_adj_q (p : V) (hp : p = q0 ∨ p = q1) : ¬ G.Adj p dbar := by
        intro hadj
        have hineq : G.neighborFinset p ∩ H.A = {d} := by
          rcases hp with heq | heq <;> (rw [heq]; assumption)
        have : dbar ∈ G.neighborFinset p ∩ H.A :=
          mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hdbarA⟩
        have : dbar = d := by
          have hmem : dbar ∈ ({d} : Finset V) := by rwa [hineq] at this
          simpa using hmem
        exact hdbar_ne this
      have hdbar_p : (G.neighborFinset dbar ∩ ({p0, p1} : Finset V)).Nonempty := by
        have hcoreN : (G.neighborFinset dbar ∩ H.C).Nonempty := by
          have : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
          rcases this with heq | heq
          · rw [heq]; exact hprivcore.1
          · rw [heq]; exact hprivcore.2
        obtain ⟨c, hc⟩ := hcoreN
        have hcC : c ∈ H.C := (mem_inter.1 hc).2
        have hAdj : G.Adj dbar c := (G.mem_neighborFinset _ _).1 (mem_inter.1 hc).1
        have hcmem : c ∈ ({q0, q1, p0, p1} : Finset V) := by
          have : c ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hcC
          simpa [or_comm, or_left_comm] using this
        simp only [mem_insert, mem_singleton] at hcmem
        refine ⟨c, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hAdj, ?_⟩⟩
        rcases hcmem with heq | heq | heq | heq
        · exact False.elim (not_adj_q q0 (Or.inl rfl) (heq ▸ hAdj.symm))
        · exact False.elim (not_adj_q q1 (Or.inr rfl) (heq ▸ hAdj.symm))
        · simp [heq]
        · simp [heq]
      have d_not_both_p : ¬(G.Adj d p0 ∧ G.Adj d p1) := by
        intro ⟨hp0, hp1⟩
        obtain ⟨x, hx⟩ := hdbar_p
        have hx' : x = p0 ∨ x = p1 := by simpa using (mem_inter.1 hx).2
        have hAdjx : G.Adj dbar x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
        have hb : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
        rcases hx' with hx0 | hx1
        · -- x = p0
          rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
          · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
          · -- d=d0 dbar=d1
            have h1 : G.Adj p0 d1 := (hx0 ▸ hb1 ▸ hAdjx).symm
            have h2 : G.Adj p1 d0 := hd0e ▸ hp1.symm
            exact hnop.2 h1 h2
          · have h1 : G.Adj p0 d0 := (hx0 ▸ hb0 ▸ hAdjx).symm
            have h2 : G.Adj p1 d1 := hd1e ▸ hp1.symm
            exact hnop.1 h1 h2
          · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
        · rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
          · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
          · have h1 : G.Adj p0 d0 := hd0e ▸ hp0.symm
            have h2 : G.Adj p1 d1 := (hx1 ▸ hb1 ▸ hAdjx).symm
            exact hnop.1 h1 h2
          · have h1 : G.Adj p0 d1 := hd1e ▸ hp0.symm
            have h2 : G.Adj p1 d0 := (hx1 ▸ hb0 ▸ hAdjx).symm
            exact hnop.2 h1 h2
          · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
      obtain ⟨r, s, hrs_eq, hr_ne_s, hr_owns⟩ :
          ∃ r s, ({r, s} : Finset V) = {p0, p1} ∧ r ≠ s ∧
            G.neighborFinset d ∩ ({p0, p1} : Finset V) ⊆ {r} := by
        by_cases hp0d : G.Adj d p0
        · refine ⟨p0, p1, by ext x; simp [or_comm], hdist.1, ?_⟩
          intro x hx
          have hxN : x ∈ G.neighborFinset d := (mem_inter.1 hx).1
          have hxq : x = p0 ∨ x = p1 := by simpa using (mem_inter.1 hx).2
          rcases hxq with heq | heq
          · simpa [heq] using (mem_singleton_self p0)
          · subst heq
            exact False.elim (d_not_both_p ⟨hp0d, (G.mem_neighborFinset _ _).1 hxN⟩)
        · refine ⟨p1, p0, by ext x; simp [or_comm], hdist.1.symm, ?_⟩
          intro x hx
          have hxN : x ∈ G.neighborFinset d := (mem_inter.1 hx).1
          have hxq : x = p0 ∨ x = p1 := by simpa using (mem_inter.1 hx).2
          rcases hxq with heq | heq
          · subst heq; exact False.elim (hp0d ((G.mem_neighborFinset _ _).1 hxN))
          · simpa [heq] using (mem_singleton_self p1)
      have hrC : r ∈ H.C := by
        have : r ∈ ({p0, p1} : Finset V) := by
          have : r ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at this
        rcases this with heq | heq <;> (rw [heq]; assumption)
      have hsC : s ∈ H.C := by
        have : s ∈ ({p0, p1} : Finset V) := by
          have : s ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at this
        rcases this with heq | heq <;> (rw [heq]; assumption)
      have hzN := opposite_hub_mem G H
      have hq0N := core_mem_Nu G H hq0C
      have hq1N := core_mem_Nu G H hq1C
      have hrN := core_mem_Nu G H hrC
      have hsN := core_mem_Nu G H hsC
      have hdbarN : dbar ∈ G.neighborFinset H.u := by
        rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdbarA)
      have hz_ne_d := ne_z_of_priv G H hdA
      have hz_ne_r := ne_z_of_core G H hrC
      have hz_ne_s := ne_z_of_core G H hsC
      have hd_ne_r := ne_core_priv G H hrC hdA
      have hdbar_ne_r := ne_core_priv G H hrC hdbarA
      have hdbar_ne_s := ne_core_priv G H hsC hdbarA
      have hq0s : q0 ≠ s := by
        have hs_in : s ∈ ({p0, p1} : Finset V) := by
          have : s ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at hs_in
        rcases hs_in with heq | heq
        · exact (heq ▸ hdist.2.1).symm
        · exact (heq ▸ hdist.2.2.2.1).symm
      have hq1s : q1 ≠ s := by
        have hs_in : s ∈ ({p0, p1} : Finset V) := by
          have : s ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at hs_in
        rcases hs_in with heq | heq
        · exact (heq ▸ hdist.2.2.1).symm
        · exact (heq ▸ hdist.2.2.2.2.1).symm
      have hq0r : q0 ≠ r := by
        have hr_in : r ∈ ({p0, p1} : Finset V) := by
          have : r ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at hr_in
        rcases hr_in with heq | heq
        · exact (heq ▸ hdist.2.1).symm
        · exact (heq ▸ hdist.2.2.2.1).symm
      have hq1r : q1 ≠ r := by
        have hr_in : r ∈ ({p0, p1} : Finset V) := by
          have : r ∈ ({r, s} : Finset V) := by simp
          rwa [hrs_eq] at this
        simp only [mem_insert, mem_singleton] at hr_in
        rcases hr_in with heq | heq
        · exact (heq ▸ hdist.2.2.1).symm
        · exact (heq ▸ hdist.2.2.2.2.1).symm
      -- Outside edges ⊆ {q0q1, dbar–s}
      have only_out {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
          (hOut : ∀ x ∈ e, x ∉ ({H.v, d, r} : Finset V)) :
          e = s(q0, q1) ∨ e = s(dbar, s) := by
        revert he hOut
        refine Sym2.inductionOn e fun a b he hOut => ?_
        have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
        have hG : G.Adj a b := hab.2.2
        have haQ : a ∉ ({H.v, d, r} : Finset V) := hOut a (by simp)
        have hbQ : b ∉ ({H.v, d, r} : Finset V) := hOut b (by simp)
        have classif (x : V) (hxN : x ∈ G.neighborFinset H.u)
            (hxQ : x ∉ ({H.v, d, r} : Finset V)) :
            x = q0 ∨ x = q1 ∨ x = s ∨ x = dbar := by
          rw [H.hNu] at hxN
          simp only [mem_insert, mem_union, mem_singleton, not_or] at hxN hxQ
          rcases hxN with rfl | hCmem | hAmem
          · exact absurd rfl hxQ.1
          · obtain ⟨hne_d, hne_r⟩ := hxQ.2
            have hxC4 : x ∈ ({q0, q1, p0, p1} : Finset V) := by
              have : x ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hCmem
              simpa [or_comm, or_left_comm] using this
            simp only [mem_insert, mem_singleton] at hxC4
            rcases hxC4 with heq | heq | heq | heq
            · exact Or.inl heq
            · exact Or.inr (Or.inl heq)
            · -- x = p0
              have hmem : p0 ∈ ({p0, p1} : Finset V) := by simp
              have : p0 ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
              simp only [mem_insert, mem_singleton] at this
              rcases this with hr0 | hs0
              · exact absurd (heq.trans hr0) hne_r
              · exact Or.inr (Or.inr (Or.inl (heq.trans hs0)))
            · have hmem : p1 ∈ ({p0, p1} : Finset V) := by simp
              have : p1 ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
              simp only [mem_insert, mem_singleton] at this
              rcases this with hr1 | hs1
              · exact absurd (heq.trans hr1) hne_r
              · exact Or.inr (Or.inr (Or.inl (heq.trans hs1)))
          · have hx_ne_d : x ≠ d := hxQ.2.1
            have : x ∈ ({d, dbar} : Finset V) := by
              have hx01 : x ∈ ({d0, d1} : Finset V) := by rw [hAeq] at hAmem; simpa using hAmem
              rwa [hA_pair]
            simp only [mem_insert, mem_singleton] at this
            rcases this with heq | heq
            · exact absurd heq hx_ne_d
            · exact Or.inr (Or.inr (Or.inr heq))
        have haCl := classif a hab.1 haQ
        have hbCl := classif b hab.2.1 hbQ
        -- Flatten outside-edge cases
        rcases haCl with ha | ha | ha | ha
        · rcases hbCl with hb | hb | hb | hb
          · exact False.elim (hG.ne (ha.trans hb.symm))
          · exact Or.inl (by rw [ha, hb])
          · exact False.elim (by
              have hG' : G.Adj q0 s := by rwa [ha, hb] at hG
              rcases honly q0 hq0C s hsC hG' with hpedge | hqedge
              · have : q0 ∈ ({p0, p1} : Finset V) := by
                  have : q0 ∈ s(p0, p1).toFinset := by
                    simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p0 p1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hdist.2.1 heq.symm
                · exact hdist.2.2.2.1 heq.symm
              · have : s ∈ ({q0, q1} : Finset V) := by
                  have : s ∈ s(q0, q1).toFinset := by
                    simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right q0 q1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hq0s heq.symm
                · exact hq1s heq.symm)
          · exact False.elim (not_adj_q q0 (Or.inl rfl) (by rwa [ha, hb] at hG))
        · rcases hbCl with hb | hb | hb | hb
          · exact Or.inl (by rw [ha, hb]; exact Sym2.eq_swap)
          · exact False.elim (hG.ne (ha.trans hb.symm))
          · exact False.elim (by
              have hG' : G.Adj q1 s := by rwa [ha, hb] at hG
              rcases honly q1 hq1C s hsC hG' with hpedge | hqedge
              · have : q1 ∈ ({p0, p1} : Finset V) := by
                  have : q1 ∈ s(p0, p1).toFinset := by
                    simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p0 p1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hdist.2.2.1 heq.symm
                · exact hdist.2.2.2.2.1 heq.symm
              · have : s ∈ ({q0, q1} : Finset V) := by
                  have : s ∈ s(q0, q1).toFinset := by
                    simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right q0 q1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hq0s heq.symm
                · exact hq1s heq.symm)
          · exact False.elim (not_adj_q q1 (Or.inr rfl) (by rwa [ha, hb] at hG))
        · rcases hbCl with hb | hb | hb | hb
          · exact False.elim (by
              have hG' : G.Adj s q0 := by rwa [ha, hb] at hG
              rcases honly s hsC q0 hq0C hG' with hpedge | hqedge
              · have : q0 ∈ ({p0, p1} : Finset V) := by
                  have : q0 ∈ s(p0, p1).toFinset := by
                    simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p0 p1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hdist.2.1 heq.symm
                · exact hdist.2.2.2.1 heq.symm
              · have : s ∈ ({q0, q1} : Finset V) := by
                  have : s ∈ s(q0, q1).toFinset := by
                    simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left q0 q1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hq0s heq.symm
                · exact hq1s heq.symm)
          · exact False.elim (by
              have hG' : G.Adj s q1 := by rwa [ha, hb] at hG
              rcases honly s hsC q1 hq1C hG' with hpedge | hqedge
              · have : q1 ∈ ({p0, p1} : Finset V) := by
                  have : q1 ∈ s(p0, p1).toFinset := by
                    simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p0 p1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hdist.2.2.1 heq.symm
                · exact hdist.2.2.2.2.1 heq.symm
              · have : s ∈ ({q0, q1} : Finset V) := by
                  have : s ∈ s(q0, q1).toFinset := by
                    simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left q0 q1
                  simpa [Sym2.toFinset_mk_eq] using this
                simp only [mem_insert, mem_singleton] at this
                rcases this with heq | heq
                · exact hq0s heq.symm
                · exact hq1s heq.symm)
          · exact False.elim (hG.ne (ha.trans hb.symm))
          · exact Or.inr (by rw [ha, hb]; exact Sym2.eq_swap)
        · rcases hbCl with hb | hb | hb | hb
          · exact False.elim (not_adj_q q0 (Or.inl rfl) (by have hGs := hG.symm; rwa [hb, ha] at hGs))
          · exact False.elim (not_adj_q q1 (Or.inr rfl) (by have hGs := hG.symm; rwa [hb, ha] at hGs))
          · exact Or.inr (by rw [ha, hb])
          · exact False.elim (hG.ne (ha.trans hb.symm))
      by_cases hds : G.Adj dbar s
      · let Q : Finset V := {H.v, d, r}
        let M : Finset (Sym2 V) := {s(q0, q1), s(dbar, s), s(H.v, r)}
        have hzr := z_adj_core G H hrC
        have hQcard : Q.card = 3 := by
          change ({H.v, d, r} : Finset V).card = 3
          have h1 : H.v ∉ ({d, r} : Finset V) := by
            simp only [mem_insert, mem_singleton, not_or]; exact ⟨hz_ne_d, hz_ne_r⟩
          have h2 : d ∉ ({r} : Finset V) := by
            simp only [mem_singleton]; exact hd_ne_r.symm
          rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
        have hne01 : s(q0, q1) ≠ s(dbar, s) := by
          intro heq
          have : q0 = dbar ∨ q0 = s := by
            simpa [Sym2.mem_iff] using
              (show q0 ∈ s(dbar, s) by simpa [← heq] using Sym2.mem_mk_left q0 q1)
          rcases this with heq' | heq'
          · exact (ne_core_priv G H hq0C hdbarA) heq'
          · exact hq0s heq'
        have hne02 : s(q0, q1) ≠ s(H.v, r) := by
          intro heq
          have : q0 = H.v ∨ q0 = r := by
            simpa [Sym2.mem_iff] using
              (show q0 ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left q0 q1)
          rcases this with heq' | heq'
          · exact (ne_z_of_core G H hq0C) heq'.symm
          · exact hq0r heq'
        have hne12 : s(dbar, s) ≠ s(H.v, r) := by
          intro heq
          have : dbar = H.v ∨ dbar = r := by
            simpa [Sym2.mem_iff] using
              (show dbar ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left dbar s)
          rcases this with heq' | heq'
          · exact (ne_z_of_priv G H hdbarA) heq'.symm
          · exact hdbar_ne_r heq'.symm
        have hMcard : M.card = 3 := by
          change ({s(q0, q1), s(dbar, s), s(H.v, r)} : Finset (Sym2 V)).card = 3
          have h1 : s(q0, q1) ∉ ({s(dbar, s), s(H.v, r)} : Finset (Sym2 V)) := by
            simp [hne01, hne02]
          have h2 : s(dbar, s) ∉ ({s(H.v, r)} : Finset (Sym2 V)) := by simp [hne12]
          rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
        have hdisj01 : Disjoint s(q0, q1).toFinset s(dbar, s).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_core_priv G H hq0C hdbarA)
          · exact ha ▸ hb ▸ hq0s
          · exact ha ▸ hb ▸ (ne_core_priv G H hq1C hdbarA)
          · exact ha ▸ hb ▸ hq1s
        have hdisj02 : Disjoint s(q0, q1).toFinset s(H.v, r).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_z_of_core G H hq0C).symm
          · exact ha ▸ hb ▸ hq0r
          · exact ha ▸ hb ▸ (ne_z_of_core G H hq1C).symm
          · exact ha ▸ hb ▸ hq1r
        have hdisj12 : Disjoint s(dbar, s).toFinset s(H.v, r).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_z_of_priv G H hdbarA).symm
          · exact ha ▸ hb ▸ hdbar_ne_r.symm
          · exact ha ▸ hb ▸ hz_ne_s.symm
          · exact ha ▸ hb ▸ hr_ne_s.symm
        have hM : IsEdgeMatching (linkGraph G H.u) M := by
          refine ⟨?_, ?_⟩
          · intro e he; simp only [M, mem_insert, mem_singleton] at he
            rcases he with h | h | h
            · subst h; exact Prop31.link_edge G H.u q0 q1 hq0N hq1N hcore.2
            · subst h; exact Prop31.link_edge G H.u dbar s hdbarN hsN hds
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
          isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
            have hout := only_out he (by intro x hx; simpa [Q] using hOut x hx)
            rcases hout with heq | heq <;> simp only [M, mem_insert, mem_singleton, heq, true_or, or_true]⟩
        exact hnot this
      · -- ¬dbar–s ⇒ dbar–r; M = {q0q1, dbar r, z s}
        have hdr : G.Adj dbar r := by
          obtain ⟨x, hx⟩ := hdbar_p
          have hx' : x = p0 ∨ x = p1 := by simpa using (mem_inter.1 hx).2
          have hAdj : G.Adj dbar x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
          have hmem : x ∈ ({p0, p1} : Finset V) := by simpa using hx'
          have : x ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
          simp only [mem_insert, mem_singleton] at this
          rcases this with heq | heq
          · exact heq ▸ hAdj
          · exact False.elim (hds (heq ▸ hAdj))
        let Q : Finset V := {H.v, d, r}
        let M : Finset (Sym2 V) := {s(q0, q1), s(dbar, r), s(H.v, s)}
        have hzs := z_adj_core G H hsC
        have hQcard : Q.card = 3 := by
          change ({H.v, d, r} : Finset V).card = 3
          have h1 : H.v ∉ ({d, r} : Finset V) := by
            simp only [mem_insert, mem_singleton, not_or]; exact ⟨hz_ne_d, hz_ne_r⟩
          have h2 : d ∉ ({r} : Finset V) := by
            simp only [mem_singleton]; exact hd_ne_r.symm
          rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
        have hne01 : s(q0, q1) ≠ s(dbar, r) := by
          intro heq
          have : q0 = dbar ∨ q0 = r := by
            simpa [Sym2.mem_iff] using
              (show q0 ∈ s(dbar, r) by simpa [← heq] using Sym2.mem_mk_left q0 q1)
          rcases this with heq' | heq'
          · exact (ne_core_priv G H hq0C hdbarA) heq'
          · exact hq0r heq'
        have hne02 : s(q0, q1) ≠ s(H.v, s) := by
          intro heq
          have : q0 = H.v ∨ q0 = s := by
            simpa [Sym2.mem_iff] using
              (show q0 ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left q0 q1)
          rcases this with heq' | heq'
          · exact (ne_z_of_core G H hq0C) heq'.symm
          · exact hq0s heq'
        have hne12 : s(dbar, r) ≠ s(H.v, s) := by
          intro heq
          have : dbar = H.v ∨ dbar = s := by
            simpa [Sym2.mem_iff] using
              (show dbar ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left dbar r)
          rcases this with heq' | heq'
          · exact (ne_z_of_priv G H hdbarA) heq'.symm
          · exact hdbar_ne_s heq'.symm
        have hMcard : M.card = 3 := by
          change ({s(q0, q1), s(dbar, r), s(H.v, s)} : Finset (Sym2 V)).card = 3
          have h1 : s(q0, q1) ∉ ({s(dbar, r), s(H.v, s)} : Finset (Sym2 V)) := by
            simp [hne01, hne02]
          have h2 : s(dbar, r) ∉ ({s(H.v, s)} : Finset (Sym2 V)) := by simp [hne12]
          rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
        have hdisj01 : Disjoint s(q0, q1).toFinset s(dbar, r).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_core_priv G H hq0C hdbarA)
          · exact ha ▸ hb ▸ hq0r
          · exact ha ▸ hb ▸ (ne_core_priv G H hq1C hdbarA)
          · exact ha ▸ hb ▸ hq1r
        have hdisj02 : Disjoint s(q0, q1).toFinset s(H.v, s).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_z_of_core G H hq0C).symm
          · exact ha ▸ hb ▸ hq0s
          · exact ha ▸ hb ▸ (ne_z_of_core G H hq1C).symm
          · exact ha ▸ hb ▸ hq1s
        have hdisj12 : Disjoint s(dbar, r).toFinset s(H.v, s).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact ha ▸ hb ▸ (ne_z_of_priv G H hdbarA).symm
          · exact ha ▸ hb ▸ hdbar_ne_s.symm
          · exact ha ▸ hb ▸ hz_ne_r.symm
          · exact ha ▸ hb ▸ hr_ne_s
        have hM : IsEdgeMatching (linkGraph G H.u) M := by
          refine ⟨?_, ?_⟩
          · intro e he; simp only [M, mem_insert, mem_singleton] at he
            rcases he with h | h | h
            · subst h; exact Prop31.link_edge G H.u q0 q1 hq0N hq1N hcore.2
            · subst h; exact Prop31.link_edge G H.u dbar r hdbarN hrN hdr
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
        have : IsWKE (linkGraph G H.u) :=
          isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
            have hout := only_out he (by intro x hx; simpa [Q] using hOut x hx)
            rcases hout with heq | heq
            · simp only [M, mem_insert, mem_singleton, heq, true_or]
            · have hab : (linkGraph G H.u).Adj dbar s := by
                have : s(dbar, s) ∈ (linkGraph G H.u).edgeFinset := by simpa [← heq] using he
                exact (mem_edgeFinset (G := linkGraph G H.u)).1 this
              exact False.elim (hds hab.2.2)⟩
        exact hnot this
  · -- Both p-endpoints attach; same-singleton on p-edge
    push Not at hone_p
    have hp0A : (G.neighborFinset p0 ∩ H.A).Nonempty := hone_p.1
    have hp1A : (G.neighborFinset p1 ∩ H.A).Nonempty := hone_p.2
    have same_sing : ∃ d, G.neighborFinset p0 ∩ H.A = {d} ∧
        G.neighborFinset p1 ∩ H.A = {d} := by
      have h0sub : G.neighborFinset p0 ∩ H.A ⊆ ({d0, d1} : Finset V) := by
        intro x hx; have : x ∈ H.A := (mem_inter.1 hx).2
        rw [hAeq] at this; simpa using this
      have h1sub : G.neighborFinset p1 ∩ H.A ⊆ ({d0, d1} : Finset V) := by
        intro x hx; have : x ∈ H.A := (mem_inter.1 hx).2
        rw [hAeq] at this; simpa using this
      have not_both (p : V) (hp : p = p0 ∨ p = p1) :
          ¬(G.Adj p d0 ∧ G.Adj p d1) := by
        intro ⟨hd0a, hd1a⟩
        rcases hp with rfl | rfl
        · obtain ⟨x, hx⟩ := hp1A
          have hxA : x ∈ H.A := (mem_inter.1 hx).2
          have hAdjx : G.Adj p1 x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
          have hx' : x = d0 ∨ x = d1 := by rw [hAeq] at hxA; simpa using hxA
          rcases hx' with rfl | rfl
          · exact hnop.2 hd1a hAdjx
          · exact hnop.1 hd0a hAdjx
        · obtain ⟨x, hx⟩ := hp0A
          have hxA : x ∈ H.A := (mem_inter.1 hx).2
          have hAdjx : G.Adj p0 x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
          have hx' : x = d0 ∨ x = d1 := by rw [hAeq] at hxA; simpa using hxA
          rcases hx' with rfl | rfl
          · exact hnop.1 hAdjx hd1a
          · exact hnop.2 hAdjx hd0a
      have card1 (p : V) (hne : (G.neighborFinset p ∩ H.A).Nonempty)
          (hsub : G.neighborFinset p ∩ H.A ⊆ ({d0, d1} : Finset V))
          (hnot : ¬(G.Adj p d0 ∧ G.Adj p d1)) :
          ∃ d, G.neighborFinset p ∩ H.A = {d} := by
        have hcard : (G.neighborFinset p ∩ H.A).card = 1 := by
          have hle : (G.neighborFinset p ∩ H.A).card ≤ 2 :=
            (card_le_card hsub).trans (by
              rw [card_insert_of_notMem (by simp [hd01]), card_singleton])
          have hge : 0 < (G.neighborFinset p ∩ H.A).card := card_pos.2 hne
          by_contra hne1
          have h2 : (G.neighborFinset p ∩ H.A).card = 2 := by omega
          have heqAB : G.neighborFinset p ∩ H.A = {d0, d1} := by
            refine eq_of_subset_of_card_le hsub ?_
            have hcard01 : ({d0, d1} : Finset V).card = 2 := by
              rw [card_insert_of_notMem (by simp [hd01]), card_singleton]
            omega
          have hd0m : d0 ∈ G.neighborFinset p ∩ H.A := by rw [heqAB]; simp
          have hd1m : d1 ∈ G.neighborFinset p ∩ H.A := by rw [heqAB]; simp
          exact hnot ⟨(G.mem_neighborFinset _ _).1 (mem_inter.1 hd0m).1,
            (G.mem_neighborFinset _ _).1 (mem_inter.1 hd1m).1⟩
        exact (card_eq_one.1 hcard)
      obtain ⟨e0, he0⟩ := card1 p0 hp0A h0sub (not_both p0 (Or.inl rfl))
      obtain ⟨e1, he1⟩ := card1 p1 hp1A h1sub (not_both p1 (Or.inr rfl))
      have heq01 : e0 = e1 := by
        by_contra hne
        have e0A : e0 ∈ H.A := by
          have : e0 ∈ G.neighborFinset p0 ∩ H.A := by rw [he0]; simp
          exact (mem_inter.1 this).2
        have e1A : e1 ∈ H.A := by
          have : e1 ∈ G.neighborFinset p1 ∩ H.A := by rw [he1]; simp
          exact (mem_inter.1 this).2
        have e0' : e0 = d0 ∨ e0 = d1 := by rw [hAeq] at e0A; simpa using e0A
        have e1' : e1 = d0 ∨ e1 = d1 := by rw [hAeq] at e1A; simpa using e1A
        have hAdj0 : G.Adj p0 e0 := by
          have : e0 ∈ G.neighborFinset p0 ∩ H.A := by rw [he0]; simp
          exact (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1
        have hAdj1 : G.Adj p1 e1 := by
          have : e1 ∈ G.neighborFinset p1 ∩ H.A := by rw [he1]; simp
          exact (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1
        rcases e0' with rfl | rfl <;> rcases e1' with rfl | rfl
        · exact absurd rfl hne
        · exact hnop.1 hAdj0 hAdj1
        · exact hnop.2 hAdj0 hAdj1
        · exact absurd rfl hne
      subst heq01
      exact ⟨e0, he0, he1⟩
    obtain ⟨d, hd0eq, hd1eq⟩ := same_sing
    have hdA : d ∈ H.A := by
      have : d ∈ G.neighborFinset p0 ∩ H.A := by rw [hd0eq]; simp
      exact (mem_inter.1 this).2
    have hd_eq : d = d0 ∨ d = d1 := by rw [hAeq] at hdA; simpa using hdA
    obtain ⟨dbar, hdbar_ne, hdbarA⟩ : ∃ db, db ≠ d ∧ db ∈ H.A := by
      rcases hd_eq with heq | heq
      · exact ⟨d1, fun h => hd01 (heq.symm.trans h.symm), hd1A⟩
      · exact ⟨d0, fun h => hd01 (h.trans heq), hd0A⟩
    have hA_pair : ({d, dbar} : Finset V) = {d0, d1} := by
      have hb : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
      rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
      · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
      · rw [hd0e, hb1]  -- {d0,d1}={d0,d1}
      · rw [hd1e, hb0]; ext x; simp [or_comm]
      · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
    have not_adj_p (p : V) (hp : p = p0 ∨ p = p1) : ¬ G.Adj p dbar := by
      intro hadj
      have hineq : G.neighborFinset p ∩ H.A = {d} := by
        rcases hp with heq | heq <;> (rw [heq]; assumption)
      have : dbar ∈ G.neighborFinset p ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hdbarA⟩
      have : dbar = d := by
        have hmem : dbar ∈ ({d} : Finset V) := by rwa [hineq] at this
        simpa using hmem
      exact hdbar_ne this
    have hdbar_q : (G.neighborFinset dbar ∩ ({q0, q1} : Finset V)).Nonempty := by
      have hcoreN : (G.neighborFinset dbar ∩ H.C).Nonempty := by
        have : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
        rcases this with heq | heq
        · rw [heq]; exact hprivcore.1
        · rw [heq]; exact hprivcore.2
      obtain ⟨c, hc⟩ := hcoreN
      have hcC : c ∈ H.C := (mem_inter.1 hc).2
      have hAdj : G.Adj dbar c := (G.mem_neighborFinset _ _).1 (mem_inter.1 hc).1
      have hcmem : c ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hcC
      simp only [mem_insert, mem_singleton] at hcmem
      refine ⟨c, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hAdj, ?_⟩⟩
      rcases hcmem with heq | heq | heq | heq
      · exact False.elim (not_adj_p p0 (Or.inl rfl) (heq ▸ hAdj.symm))
      · exact False.elim (not_adj_p p1 (Or.inr rfl) (heq ▸ hAdj.symm))
      · simp [heq]
      · simp [heq]
    have d_not_both_q : ¬(G.Adj d q0 ∧ G.Adj d q1) := by
      intro ⟨hq0, hq1⟩
      obtain ⟨x, hx⟩ := hdbar_q
      have hx' : x = q0 ∨ x = q1 := by simpa using (mem_inter.1 hx).2
      have hAdjx : G.Adj dbar x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
      have hb : dbar = d0 ∨ dbar = d1 := by rw [hAeq] at hdbarA; simpa using hdbarA
      rcases hx' with hx0 | hx1
      · -- x = q0
        rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
        · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
        · -- d=d0 dbar=d1
          have h1 : G.Adj q0 d1 := (hx0 ▸ hb1 ▸ hAdjx).symm
          have h2 : G.Adj q1 d0 := hd0e ▸ hq1.symm
          exact hnoq.2 h1 h2
        · have h1 : G.Adj q0 d0 := (hx0 ▸ hb0 ▸ hAdjx).symm
          have h2 : G.Adj q1 d1 := hd1e ▸ hq1.symm
          exact hnoq.1 h1 h2
        · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
      · rcases hd_eq with hd0e | hd1e <;> rcases hb with hb0 | hb1
        · exact False.elim (hdbar_ne (hb0.trans hd0e.symm))
        · have h1 : G.Adj q0 d0 := hd0e ▸ hq0.symm
          have h2 : G.Adj q1 d1 := (hx1 ▸ hb1 ▸ hAdjx).symm
          exact hnoq.1 h1 h2
        · have h1 : G.Adj q0 d1 := hd1e ▸ hq0.symm
          have h2 : G.Adj q1 d0 := (hx1 ▸ hb0 ▸ hAdjx).symm
          exact hnoq.2 h1 h2
        · exact False.elim (hdbar_ne (hb1.trans hd1e.symm))
    obtain ⟨r, s, hrs_eq, hr_ne_s, hr_owns⟩ :
        ∃ r s, ({r, s} : Finset V) = {q0, q1} ∧ r ≠ s ∧
          G.neighborFinset d ∩ ({q0, q1} : Finset V) ⊆ {r} := by
      by_cases hq0d : G.Adj d q0
      · refine ⟨q0, q1, by ext x; simp [or_comm], hdist.2.2.2.2.2, ?_⟩
        intro x hx
        have hxN : x ∈ G.neighborFinset d := (mem_inter.1 hx).1
        have hxq : x = q0 ∨ x = q1 := by simpa using (mem_inter.1 hx).2
        rcases hxq with heq | heq
        · simpa [heq] using (mem_singleton_self q0)
        · subst heq
          exact False.elim (d_not_both_q ⟨hq0d, (G.mem_neighborFinset _ _).1 hxN⟩)
      · refine ⟨q1, q0, by ext x; simp [or_comm], hdist.2.2.2.2.2.symm, ?_⟩
        intro x hx
        have hxN : x ∈ G.neighborFinset d := (mem_inter.1 hx).1
        have hxq : x = q0 ∨ x = q1 := by simpa using (mem_inter.1 hx).2
        rcases hxq with heq | heq
        · subst heq; exact False.elim (hq0d ((G.mem_neighborFinset _ _).1 hxN))
        · simpa [heq] using (mem_singleton_self q1)
    have hrC : r ∈ H.C := by
      have : r ∈ ({q0, q1} : Finset V) := by
        have : r ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with heq | heq <;> (rw [heq]; assumption)
    have hsC : s ∈ H.C := by
      have : s ∈ ({q0, q1} : Finset V) := by
        have : s ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with heq | heq <;> (rw [heq]; assumption)
    have hzN := opposite_hub_mem G H
    have hp0N := core_mem_Nu G H hp0C
    have hp1N := core_mem_Nu G H hp1C
    have hrN := core_mem_Nu G H hrC
    have hsN := core_mem_Nu G H hsC
    have hdbarN : dbar ∈ G.neighborFinset H.u := by
      rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdbarA)
    have hz_ne_d := ne_z_of_priv G H hdA
    have hz_ne_r := ne_z_of_core G H hrC
    have hz_ne_s := ne_z_of_core G H hsC
    have hd_ne_r := ne_core_priv G H hrC hdA
    have hdbar_ne_r := ne_core_priv G H hrC hdbarA
    have hdbar_ne_s := ne_core_priv G H hsC hdbarA
    have hp0s : p0 ≠ s := by
      have hs_in : s ∈ ({q0, q1} : Finset V) := by
        have : s ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at hs_in
      rcases hs_in with heq | heq
      · exact heq ▸ hdist.2.1
      · exact heq ▸ hdist.2.2.1
    have hp1s : p1 ≠ s := by
      have hs_in : s ∈ ({q0, q1} : Finset V) := by
        have : s ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at hs_in
      rcases hs_in with heq | heq
      · exact heq ▸ hdist.2.2.2.1
      · exact heq ▸ hdist.2.2.2.2.1
    have hp0r : p0 ≠ r := by
      have hr_in : r ∈ ({q0, q1} : Finset V) := by
        have : r ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at hr_in
      rcases hr_in with heq | heq
      · exact heq ▸ hdist.2.1
      · exact heq ▸ hdist.2.2.1
    have hp1r : p1 ≠ r := by
      have hr_in : r ∈ ({q0, q1} : Finset V) := by
        have : r ∈ ({r, s} : Finset V) := by simp
        rwa [hrs_eq] at this
      simp only [mem_insert, mem_singleton] at hr_in
      rcases hr_in with heq | heq
      · exact heq ▸ hdist.2.2.2.1
      · exact heq ▸ hdist.2.2.2.2.1
    -- Outside edges ⊆ {p0p1, dbar–s}
    have only_out {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
        (hOut : ∀ x ∈ e, x ∉ ({H.v, d, r} : Finset V)) :
        e = s(p0, p1) ∨ e = s(dbar, s) := by
      revert he hOut
      refine Sym2.inductionOn e fun a b he hOut => ?_
      have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
      have hG : G.Adj a b := hab.2.2
      have haQ : a ∉ ({H.v, d, r} : Finset V) := hOut a (by simp)
      have hbQ : b ∉ ({H.v, d, r} : Finset V) := hOut b (by simp)
      have classif (x : V) (hxN : x ∈ G.neighborFinset H.u)
          (hxQ : x ∉ ({H.v, d, r} : Finset V)) :
          x = p0 ∨ x = p1 ∨ x = s ∨ x = dbar := by
        rw [H.hNu] at hxN
        simp only [mem_insert, mem_union, mem_singleton, not_or] at hxN hxQ
        rcases hxN with rfl | hCmem | hAmem
        · exact absurd rfl hxQ.1
        · obtain ⟨hne_d, hne_r⟩ := hxQ.2
          have hxC4 : x ∈ ({p0, p1, q0, q1} : Finset V) := by rw [← hC]; exact hCmem
          simp only [mem_insert, mem_singleton] at hxC4
          rcases hxC4 with heq | heq | heq | heq
          · exact Or.inl heq
          · exact Or.inr (Or.inl heq)
          · -- x = q0
            have hmem : q0 ∈ ({q0, q1} : Finset V) := by simp
            have : q0 ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
            simp only [mem_insert, mem_singleton] at this
            rcases this with hr0 | hs0
            · exact absurd (heq.trans hr0) hne_r
            · exact Or.inr (Or.inr (Or.inl (heq.trans hs0)))
          · have hmem : q1 ∈ ({q0, q1} : Finset V) := by simp
            have : q1 ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
            simp only [mem_insert, mem_singleton] at this
            rcases this with hr1 | hs1
            · exact absurd (heq.trans hr1) hne_r
            · exact Or.inr (Or.inr (Or.inl (heq.trans hs1)))
        · have hx_ne_d : x ≠ d := hxQ.2.1
          have : x ∈ ({d, dbar} : Finset V) := by
            have hx01 : x ∈ ({d0, d1} : Finset V) := by rw [hAeq] at hAmem; simpa using hAmem
            rwa [hA_pair]
          simp only [mem_insert, mem_singleton] at this
          rcases this with heq | heq
          · exact absurd heq hx_ne_d
          · exact Or.inr (Or.inr (Or.inr heq))
      have haCl := classif a hab.1 haQ
      have hbCl := classif b hab.2.1 hbQ
      -- Flatten outside-edge cases
      rcases haCl with ha | ha | ha | ha
      · rcases hbCl with hb | hb | hb | hb
        · exact False.elim (hG.ne (ha.trans hb.symm))
        · exact Or.inl (by rw [ha, hb])
        · exact False.elim (by
            have hG' : G.Adj p0 s := by rwa [ha, hb] at hG
            rcases honly p0 hp0C s hsC hG' with hpedge | hqedge
            · have : s ∈ ({p0, p1} : Finset V) := by
                have : s ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hp0s heq.symm
              · exact hp1s heq.symm
            · have : p0 ∈ ({q0, q1} : Finset V) := by
                have : p0 ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hdist.2.1 heq
              · exact hdist.2.2.1 heq)
        · exact False.elim (not_adj_p p0 (Or.inl rfl) (by rwa [ha, hb] at hG))
      · rcases hbCl with hb | hb | hb | hb
        · exact Or.inl (by rw [ha, hb]; exact Sym2.eq_swap)
        · exact False.elim (hG.ne (ha.trans hb.symm))
        · exact False.elim (by
            have hG' : G.Adj p1 s := by rwa [ha, hb] at hG
            rcases honly p1 hp1C s hsC hG' with hpedge | hqedge
            · have : s ∈ ({p0, p1} : Finset V) := by
                have : s ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hp0s heq.symm
              · exact hp1s heq.symm
            · have : p1 ∈ ({q0, q1} : Finset V) := by
                have : p1 ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hdist.2.2.2.1 heq
              · exact hdist.2.2.2.2.1 heq)
        · exact False.elim (not_adj_p p1 (Or.inr rfl) (by rwa [ha, hb] at hG))
      · rcases hbCl with hb | hb | hb | hb
        · exact False.elim (by
            have hG' : G.Adj s p0 := by rwa [ha, hb] at hG
            rcases honly s hsC p0 hp0C hG' with hpedge | hqedge
            · have : s ∈ ({p0, p1} : Finset V) := by
                have : s ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hp0s heq.symm
              · exact hp1s heq.symm
            · have : p0 ∈ ({q0, q1} : Finset V) := by
                have : p0 ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hdist.2.1 heq
              · exact hdist.2.2.1 heq)
        · exact False.elim (by
            have hG' : G.Adj s p1 := by rwa [ha, hb] at hG
            rcases honly s hsC p1 hp1C hG' with hpedge | hqedge
            · have : s ∈ ({p0, p1} : Finset V) := by
                have : s ∈ s(p0, p1).toFinset := by
                  simpa [← hpedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p0 p1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hp0s heq.symm
              · exact hp1s heq.symm
            · have : p1 ∈ ({q0, q1} : Finset V) := by
                have : p1 ∈ s(q0, q1).toFinset := by
                  simpa [← hqedge, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right q0 q1
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at this
              rcases this with heq | heq
              · exact hdist.2.2.2.1 heq
              · exact hdist.2.2.2.2.1 heq)
        · exact False.elim (hG.ne (ha.trans hb.symm))
        · exact Or.inr (by rw [ha, hb]; exact Sym2.eq_swap)
      · rcases hbCl with hb | hb | hb | hb
        · exact False.elim (not_adj_p p0 (Or.inl rfl) (by have hGs := hG.symm; rwa [hb, ha] at hGs))
        · exact False.elim (not_adj_p p1 (Or.inr rfl) (by have hGs := hG.symm; rwa [hb, ha] at hGs))
        · exact Or.inr (by rw [ha, hb])
        · exact False.elim (hG.ne (ha.trans hb.symm))
    by_cases hds : G.Adj dbar s
    · let Q : Finset V := {H.v, d, r}
      let M : Finset (Sym2 V) := {s(p0, p1), s(dbar, s), s(H.v, r)}
      have hzr := z_adj_core G H hrC
      have hQcard : Q.card = 3 := by
        change ({H.v, d, r} : Finset V).card = 3
        have h1 : H.v ∉ ({d, r} : Finset V) := by
          simp only [mem_insert, mem_singleton, not_or]; exact ⟨hz_ne_d, hz_ne_r⟩
        have h2 : d ∉ ({r} : Finset V) := by
          simp only [mem_singleton]; exact hd_ne_r.symm
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hne01 : s(p0, p1) ≠ s(dbar, s) := by
        intro heq
        have : p0 = dbar ∨ p0 = s := by
          simpa [Sym2.mem_iff] using
            (show p0 ∈ s(dbar, s) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
        rcases this with heq' | heq'
        · exact (ne_core_priv G H hp0C hdbarA) heq'
        · exact hp0s heq'
      have hne02 : s(p0, p1) ≠ s(H.v, r) := by
        intro heq
        have : p0 = H.v ∨ p0 = r := by
          simpa [Sym2.mem_iff] using
            (show p0 ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
        rcases this with heq' | heq'
        · exact (ne_z_of_core G H hp0C) heq'.symm
        · exact hp0r heq'
      have hne12 : s(dbar, s) ≠ s(H.v, r) := by
        intro heq
        have : dbar = H.v ∨ dbar = r := by
          simpa [Sym2.mem_iff] using
            (show dbar ∈ s(H.v, r) by simpa [← heq] using Sym2.mem_mk_left dbar s)
        rcases this with heq' | heq'
        · exact (ne_z_of_priv G H hdbarA) heq'.symm
        · exact hdbar_ne_r heq'.symm
      have hMcard : M.card = 3 := by
        change ({s(p0, p1), s(dbar, s), s(H.v, r)} : Finset (Sym2 V)).card = 3
        have h1 : s(p0, p1) ∉ ({s(dbar, s), s(H.v, r)} : Finset (Sym2 V)) := by
          simp [hne01, hne02]
        have h2 : s(dbar, s) ∉ ({s(H.v, r)} : Finset (Sym2 V)) := by simp [hne12]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hdisj01 : Disjoint s(p0, p1).toFinset s(dbar, s).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_core_priv G H hp0C hdbarA)
        · exact ha ▸ hb ▸ hp0s
        · exact ha ▸ hb ▸ (ne_core_priv G H hp1C hdbarA)
        · exact ha ▸ hb ▸ hp1s
      have hdisj02 : Disjoint s(p0, p1).toFinset s(H.v, r).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_z_of_core G H hp0C).symm
        · exact ha ▸ hb ▸ hp0r
        · exact ha ▸ hb ▸ (ne_z_of_core G H hp1C).symm
        · exact ha ▸ hb ▸ hp1r
      have hdisj12 : Disjoint s(dbar, s).toFinset s(H.v, r).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_z_of_priv G H hdbarA).symm
        · exact ha ▸ hb ▸ hdbar_ne_r.symm
        · exact ha ▸ hb ▸ hz_ne_s.symm
        · exact ha ▸ hb ▸ hr_ne_s.symm
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u p0 p1 hp0N hp1N hcore.1
          · subst h; exact Prop31.link_edge G H.u dbar s hdbarN hsN hds
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
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
          have hout := only_out he (by intro x hx; simpa [Q] using hOut x hx)
          rcases hout with heq | heq <;> simp only [M, mem_insert, mem_singleton, heq, true_or, or_true]⟩
      exact hnot this
    · -- ¬dbar–s ⇒ dbar–r; M = {p0p1, dbar r, z s}
      have hdr : G.Adj dbar r := by
        obtain ⟨x, hx⟩ := hdbar_q
        have hx' : x = q0 ∨ x = q1 := by simpa using (mem_inter.1 hx).2
        have hAdj : G.Adj dbar x := (G.mem_neighborFinset _ _).1 (mem_inter.1 hx).1
        have hmem : x ∈ ({q0, q1} : Finset V) := by simpa using hx'
        have : x ∈ ({r, s} : Finset V) := by rwa [← hrs_eq] at hmem
        simp only [mem_insert, mem_singleton] at this
        rcases this with heq | heq
        · exact heq ▸ hAdj
        · exact False.elim (hds (heq ▸ hAdj))
      let Q : Finset V := {H.v, d, r}
      let M : Finset (Sym2 V) := {s(p0, p1), s(dbar, r), s(H.v, s)}
      have hzs := z_adj_core G H hsC
      have hQcard : Q.card = 3 := by
        change ({H.v, d, r} : Finset V).card = 3
        have h1 : H.v ∉ ({d, r} : Finset V) := by
          simp only [mem_insert, mem_singleton, not_or]; exact ⟨hz_ne_d, hz_ne_r⟩
        have h2 : d ∉ ({r} : Finset V) := by
          simp only [mem_singleton]; exact hd_ne_r.symm
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hne01 : s(p0, p1) ≠ s(dbar, r) := by
        intro heq
        have : p0 = dbar ∨ p0 = r := by
          simpa [Sym2.mem_iff] using
            (show p0 ∈ s(dbar, r) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
        rcases this with heq' | heq'
        · exact (ne_core_priv G H hp0C hdbarA) heq'
        · exact hp0r heq'
      have hne02 : s(p0, p1) ≠ s(H.v, s) := by
        intro heq
        have : p0 = H.v ∨ p0 = s := by
          simpa [Sym2.mem_iff] using
            (show p0 ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left p0 p1)
        rcases this with heq' | heq'
        · exact (ne_z_of_core G H hp0C) heq'.symm
        · exact hp0s heq'
      have hne12 : s(dbar, r) ≠ s(H.v, s) := by
        intro heq
        have : dbar = H.v ∨ dbar = s := by
          simpa [Sym2.mem_iff] using
            (show dbar ∈ s(H.v, s) by simpa [← heq] using Sym2.mem_mk_left dbar r)
        rcases this with heq' | heq'
        · exact (ne_z_of_priv G H hdbarA) heq'.symm
        · exact hdbar_ne_s heq'.symm
      have hMcard : M.card = 3 := by
        change ({s(p0, p1), s(dbar, r), s(H.v, s)} : Finset (Sym2 V)).card = 3
        have h1 : s(p0, p1) ∉ ({s(dbar, r), s(H.v, s)} : Finset (Sym2 V)) := by
          simp [hne01, hne02]
        have h2 : s(dbar, r) ∉ ({s(H.v, s)} : Finset (Sym2 V)) := by simp [hne12]
        rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_singleton]
      have hdisj01 : Disjoint s(p0, p1).toFinset s(dbar, r).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_core_priv G H hp0C hdbarA)
        · exact ha ▸ hb ▸ hp0r
        · exact ha ▸ hb ▸ (ne_core_priv G H hp1C hdbarA)
        · exact ha ▸ hb ▸ hp1r
      have hdisj02 : Disjoint s(p0, p1).toFinset s(H.v, s).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_z_of_core G H hp0C).symm
        · exact ha ▸ hb ▸ hp0s
        · exact ha ▸ hb ▸ (ne_z_of_core G H hp1C).symm
        · exact ha ▸ hb ▸ hp1s
      have hdisj12 : Disjoint s(dbar, r).toFinset s(H.v, s).toFinset := by
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
        refine Finset.disjoint_iff_ne.2 ?_
        intro a ha b hb; simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact ha ▸ hb ▸ (ne_z_of_priv G H hdbarA).symm
        · exact ha ▸ hb ▸ hdbar_ne_s.symm
        · exact ha ▸ hb ▸ hz_ne_r.symm
        · exact ha ▸ hb ▸ hr_ne_s
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u p0 p1 hp0N hp1N hcore.1
          · subst h; exact Prop31.link_edge G H.u dbar r hdbarN hrN hdr
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
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
          have hout := only_out he (by intro x hx; simpa [Q] using hOut x hx)
          rcases hout with heq | heq
          · simp only [M, mem_insert, mem_singleton, heq, true_or]
          · have hab : (linkGraph G H.u).Adj dbar s := by
              have : s(dbar, s) ∈ (linkGraph G H.u).edgeFinset := by simpa [← heq] using he
              exact (mem_edgeFinset (G := linkGraph G H.u)).1 this
            exact False.elim (hds hab.2.2)⟩
      exact hnot this
/-- Ten distinct labels from hub partitions (u,v,C,A,B). -/
lemma labels10_of_hub (H : HubConfig G)
    {c0 c1 c2 c3 a0 a1 b0 b1 : V}
    (hC : H.C = {c0, c1, c2, c3})
    (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (hC4 : ({c0, c1, c2, c3} : Finset V).card = 4)
    (ha01 : a0 ≠ a1) (hb01 : b0 ≠ b1) :
    ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10 := by
  classical
  have huv : H.u ≠ H.v := fun eq => G.irrefl (eq ▸ H.huv)
  have huN : H.u ∉ G.neighborFinset H.u :=
    fun hn => G.irrefl ((G.mem_neighborFinset _ _).1 hn)
  have hvN : H.v ∉ G.neighborFinset H.v :=
    fun hn => G.irrefl ((G.mem_neighborFinset _ _).1 hn)
  have huA : H.u ∉ H.A := by
    intro h; rw [H.hNu] at huN
    exact huN (mem_insert_of_mem (mem_union_right _ h))
  have hvA : H.v ∉ H.A := H.hvA.1
  have huB : H.u ∉ H.B := H.huB.1
  have hvB : H.v ∉ H.B := by
    intro h; rw [H.hNv] at hvN
    exact hvN (mem_insert_of_mem (mem_union_right _ h))
  have huC : H.u ∉ H.C := H.huB.2
  have hvC : H.v ∉ H.C := H.hvA.2
  have heq : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V) =
      ({H.u, H.v} : Finset V) ∪ H.C ∪ H.A ∪ H.B := by
    rw [hC, hA, hB]; ext x; simp [or_comm, or_left_comm, or_assoc]
  rw [heq]
  have hUV : ({H.u, H.v} : Finset V).card = 2 := by
    simp [card_insert_of_notMem, huv, card_singleton]
  have hUVdisjC : Disjoint ({H.u, H.v} : Finset V) H.C := by
    refine Finset.disjoint_left.2 ?_
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huC
    · exact hvC
  have hUVdisjA : Disjoint ({H.u, H.v} : Finset V) H.A := by
    refine Finset.disjoint_left.2 ?_
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hUVdisjB : Disjoint ({H.u, H.v} : Finset V) H.B := by
    refine Finset.disjoint_left.2 ?_
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hCAdisj := H.hAdisj.symm
  have hCBdisj := H.hBdisj.symm
  have hABdisj := H.hABdisj
  have hA2 : H.A.card = 2 := H.hA
  have hB2 : H.B.card = 2 := H.hB
  have hC4' : H.C.card = 4 := H.hCcard
  -- card of successive unions
  have h1 : (({H.u, H.v} : Finset V) ∪ H.C).card = 6 := by
    rw [card_union_of_disjoint hUVdisjC, hUV, hC4']
  have h2 : ((({H.u, H.v} : Finset V) ∪ H.C) ∪ H.A).card = 8 := by
    have d : Disjoint (({H.u, H.v} : Finset V) ∪ H.C) H.A :=
      Finset.disjoint_union_left.2 ⟨hUVdisjA, H.hAdisj.symm⟩
    rw [card_union_of_disjoint d, h1, hA2]
  have h3 : (((({H.u, H.v} : Finset V) ∪ H.C) ∪ H.A) ∪ H.B).card = 10 := by
    have d : Disjoint ((({H.u, H.v} : Finset V) ∪ H.C) ∪ H.A) H.B :=
      Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨hUVdisjB, H.hBdisj.symm⟩,
        H.hABdisj⟩
    rw [card_union_of_disjoint d, h2, hB2]
  -- need unused hC4, ha01, hb01 for API compat
  exact h3

/-- Apply Prop 4.2 certificate once labels are oriented. -/
lemma matching_core_of_labels (H : HubConfig G) (_hA1 : H.A1)
    (c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hC : H.C = {c0, c1, c2, c3})
    (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (hcore : G.Adj c0 c3 ∧ G.Adj c1 c2)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2))
    (hatt : G.Adj c1 a1 ∧ G.Adj c2 a0 ∧ G.Adj c0 b1)
    (h10 : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  obtain ⟨cert, _⟩ := prop42_certificate G H c0 c1 c2 c3 a0 a1 b0 b1
    hC hA hB hcore honly hatt h10
  exact ⟨cert⟩

/-- Prop 4.2: matching core + (A1) ⇒ `{u,v}` reducible. -/
theorem matching_core_reducible (H : HubConfig G) (hA1 : H.A1)
    (p0 p1 q0 q1 : V) (hC : H.C = {p0, p1, q0, q1})
    (hcore : G.Adj p0 p1 ∧ G.Adj q0 q1)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨a0, a1, hAeq, hcross⟩ :=
    lemma41_cross G H hA1.1 hA1.2.1 p0 p1 q0 q1 hC hcore honly
  obtain ⟨b0₀, b1₀, hb01₀, hBeq₀⟩ := (card_eq_two (s := H.B)).1 H.hB
  have ha01 : a0 ≠ a1 := by
    intro heq; have hA2 := H.hA; rw [hAeq, heq] at hA2; simp at hA2
  let Hs := H.swap
  have hA1s : Hs.A1 := hA1.swap
  have hAs : Hs.A = H.B := rfl
  have hCs : Hs.C = H.C := rfl
  have sym_of_pair {x y x' y' : V} (heq : ({x, y} : Finset V) = {x', y'})
      (hne : x ≠ y) : s(x, y) = s(x', y') := by
    have hx : x = x' ∨ x = y' := by
      have : x ∈ ({x', y'} : Finset V) := by rw [← heq]; simp
      simpa using this
    have hy : y = x' ∨ y = y' := by
      have : y ∈ ({x', y'} : Finset V) := by rw [← heq]; simp
      simpa using this
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hne
    · rw [hx, hy]
    · rw [hx, hy]; exact Sym2.eq_swap
    · exact absurd (hx.trans hy.symm) hne
  have adj_of_pair {x y x' y' : V} (heq : ({x, y} : Finset V) = {x', y'})
      (hne : x ≠ y) (hAdj : G.Adj x' y') : G.Adj x y := by
    have hx : x = x' ∨ x = y' := by
      have : x ∈ ({x', y'} : Finset V) := by rw [← heq]; simp
      simpa using this
    have hy : y = x' ∨ y = y' := by
      have : y ∈ ({x', y'} : Finset V) := by rw [← heq]; simp
      simpa using this
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hne
    · exact hx ▸ hy ▸ hAdj
    · exact hx ▸ hy ▸ hAdj.symm
    · exact absurd (hx.trans hy.symm) hne
  have pair_ne {x y x' y' : V} (heq : ({x, y} : Finset V) = {x', y'})
      (hne' : x' ≠ y') : x ≠ y := by
    intro heqxy
    have : ({x', y'} : Finset V).card = 1 := by
      rw [← heq, heqxy]; simp
    have : ({x', y'} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp [hne']), card_singleton]
    omega
  have reorient_B (b1 : V) (hb1 : b1 ∈ H.B) :
      ∃ b0, H.B = {b0, b1} ∧ b0 ≠ b1 := by
    have hb1m : b1 = b0₀ ∨ b1 = b1₀ := by rw [hBeq₀] at hb1; simpa using hb1
    rcases hb1m with heq | heq
    · refine ⟨b1₀, ?_, heq ▸ hb01₀.symm⟩
      rw [hBeq₀, heq]; ext x; simp [or_comm]
    · refine ⟨b0₀, ?_, heq ▸ hb01₀⟩
      rw [hBeq₀, heq]
  -- Orient crossed A-matching on one core edge; B-hit on the other via Hs.
  rcases hcross with hcross_p | hcross_q
  · obtain ⟨c1, c2, hc12, hattA⟩ :
        ∃ c1 c2, ({c1, c2} : Finset V) = {p0, p1} ∧ G.Adj c1 a1 ∧ G.Adj c2 a0 := by
      rcases hcross_p with h | h
      · exact ⟨p1, p0, by ext x; simp [or_comm], h.2, h.1⟩
      · exact ⟨p0, p1, by ext x; simp, h.1, h.2⟩
    have hC' : Hs.C = {q0, q1, p0, p1} := by
      change H.C = _; rw [hC]; ext x; simp [or_comm, or_left_comm]
    have honly' : ∀ x ∈ Hs.C, ∀ y ∈ Hs.C, G.Adj x y →
        s(x, y) = s(q0, q1) ∨ s(x, y) = s(p0, p1) := by
      intro x hx y hy hAdj
      have hxC : x ∈ H.C := by change x ∈ H.C at hx; exact hx
      have hyC : y ∈ H.C := by change y ∈ H.C at hy; exact hy
      rcases honly x hxC y hyC hAdj with h | h <;> simp [h, or_comm]
    have hBeq_s : Hs.A = {b0₀, b1₀} := by change H.B = _; exact hBeq₀
    have hhitB := lemma41_edge_hit G Hs hA1s.1 hA1s.2.1 q0 q1 p0 p1 hC'
      ⟨hcore.2, hcore.1⟩ honly' b0₀ b1₀ hBeq_s hb01₀
    have hhitB' : (G.neighborFinset q0 ∩ H.B).Nonempty ∨
        (G.neighborFinset q1 ∩ H.B).Nonempty := by
      change _ ∨ _ at hhitB; exact hhitB
    obtain ⟨c0, c3, b1, hc03, hb1B, hattB⟩ :
        ∃ c0 c3 b1, ({c0, c3} : Finset V) = {q0, q1} ∧
          b1 ∈ H.B ∧ G.Adj c0 b1 := by
      rcases hhitB' with hq0 | hq1
      · obtain ⟨b1, hb1⟩ := hq0
        exact ⟨q0, q1, b1, by ext x; simp, (mem_inter.1 hb1).2,
          (G.mem_neighborFinset _ _).1 (mem_inter.1 hb1).1⟩
      · obtain ⟨b1, hb1⟩ := hq1
        exact ⟨q1, q0, b1, by ext x; simp [or_comm], (mem_inter.1 hb1).2,
          (G.mem_neighborFinset _ _).1 (mem_inter.1 hb1).1⟩
    obtain ⟨b0, hBeq, hb01⟩ := reorient_B b1 hb1B
    have hdist := core4_distinct G H hC
    have hne12 := pair_ne hc12 hdist.1
    have hne03 := pair_ne hc03 hdist.2.2.2.2.2
    have hCeq : H.C = {c0, c1, c2, c3} := by
      have hpair : ({p0, p1, q0, q1} : Finset V) = {c0, c1, c2, c3} := by
        have hu : ({p0, p1, q0, q1} : Finset V) = {p0, p1} ∪ {q0, q1} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have hv : ({c0, c1, c2, c3} : Finset V) = {c1, c2} ∪ {c0, c3} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        rw [hu, hv, ← hc12, ← hc03]
      rw [hC, hpair]
    have hcore' : G.Adj c0 c3 ∧ G.Adj c1 c2 :=
      ⟨adj_of_pair hc03 hne03 hcore.2, adj_of_pair hc12 hne12 hcore.1⟩
    have honly'' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with hp | hq
      · exact Or.inr (hp.trans (sym_of_pair hc12 hne12).symm)
      · exact Or.inl (hq.trans (sym_of_pair hc03 hne03).symm)
    have h10 : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10 := by
      have hC4 : ({c0, c1, c2, c3} : Finset V).card = 4 := by rw [← hCeq]; exact H.hCcard
      exact labels10_of_hub G H hCeq hAeq hBeq hC4 ha01 hb01
    exact matching_core_of_labels G H hA1 c0 c1 c2 c3 a0 a1 b0 b1
      hCeq hAeq hBeq hcore' honly'' ⟨hattA.1, hattA.2, hattB⟩ h10
  · obtain ⟨c1, c2, hc12, hattA⟩ :
        ∃ c1 c2, ({c1, c2} : Finset V) = {q0, q1} ∧ G.Adj c1 a1 ∧ G.Adj c2 a0 := by
      rcases hcross_q with h | h
      · exact ⟨q1, q0, by ext x; simp [or_comm], h.2, h.1⟩
      · exact ⟨q0, q1, by ext x; simp, h.1, h.2⟩
    have hC' : Hs.C = {p0, p1, q0, q1} := by change H.C = _; exact hC
    have honly' : ∀ x ∈ Hs.C, ∀ y ∈ Hs.C, G.Adj x y →
        s(x, y) = s(p0, p1) ∨ s(x, y) = s(q0, q1) := by
      intro x hx y hy hAdj
      have hxC : x ∈ H.C := by change x ∈ H.C at hx; exact hx
      have hyC : y ∈ H.C := by change y ∈ H.C at hy; exact hy
      exact honly x hxC y hyC hAdj
    have hBeq_s : Hs.A = {b0₀, b1₀} := by change H.B = _; exact hBeq₀
    have hhitB := lemma41_edge_hit G Hs hA1s.1 hA1s.2.1 p0 p1 q0 q1 hC'
      hcore honly' b0₀ b1₀ hBeq_s hb01₀
    have hhitB' : (G.neighborFinset p0 ∩ H.B).Nonempty ∨
        (G.neighborFinset p1 ∩ H.B).Nonempty := by
      change _ ∨ _ at hhitB; exact hhitB
    obtain ⟨c0, c3, b1, hc03, hb1B, hattB⟩ :
        ∃ c0 c3 b1, ({c0, c3} : Finset V) = {p0, p1} ∧
          b1 ∈ H.B ∧ G.Adj c0 b1 := by
      rcases hhitB' with hp0 | hp1
      · obtain ⟨b1, hb1⟩ := hp0
        exact ⟨p0, p1, b1, by ext x; simp, (mem_inter.1 hb1).2,
          (G.mem_neighborFinset _ _).1 (mem_inter.1 hb1).1⟩
      · obtain ⟨b1, hb1⟩ := hp1
        exact ⟨p1, p0, b1, by ext x; simp [or_comm], (mem_inter.1 hb1).2,
          (G.mem_neighborFinset _ _).1 (mem_inter.1 hb1).1⟩
    obtain ⟨b0, hBeq, hb01⟩ := reorient_B b1 hb1B
    have hdist := core4_distinct G H hC
    have hne12 := pair_ne hc12 hdist.2.2.2.2.2
    have hne03 := pair_ne hc03 hdist.1
    have hCeq : H.C = {c0, c1, c2, c3} := by
      have hpair : ({p0, p1, q0, q1} : Finset V) = {c0, c1, c2, c3} := by
        have hu : ({p0, p1, q0, q1} : Finset V) = {p0, p1} ∪ {q0, q1} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have hv : ({c0, c1, c2, c3} : Finset V) = {c0, c3} ∪ {c1, c2} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        rw [hu, hv, ← hc03, ← hc12]
      rw [hC, hpair]
    have hcore' : G.Adj c0 c3 ∧ G.Adj c1 c2 :=
      ⟨adj_of_pair hc03 hne03 hcore.1, adj_of_pair hc12 hne12 hcore.2⟩
    have honly'' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with hp | hq
      · exact Or.inl (hp.trans (sym_of_pair hc03 hne03).symm)
      · exact Or.inr (hq.trans (sym_of_pair hc12 hne12).symm)
    have h10 : ({H.u, H.v, c0, c1, c2, c3, a0, a1, b0, b1} : Finset V).card = 10 := by
      have hC4 : ({c0, c1, c2, c3} : Finset V).card = 4 := by rw [← hCeq]; exact H.hCcard
      exact labels10_of_hub G H hCeq hAeq hBeq hC4 ha01 hb01
    exact matching_core_of_labels G H hA1 c0 c1 c2 c3 a0 a1 b0 b1
      hCeq hAeq hBeq hcore' honly'' ⟨hattA.1, hattA.2, hattB⟩ h10


/-! ### Lemma 4.5 certificate (shared by Props 4.6–4.7) -/

/-- Fin-10 packing for Lemma 4.5: triangles `{u,v,s}`, `{u,p,r}`, `{u,q,a1}`, `{v,p,q}`, `{v,r,b1}`.
Labels: `0=u,1=v,2=p,3=q,4=r,5=s,6=a0,7=a1,8=b0,9=b1`. -/
def packing10_45 : Finset (Finset (Fin 10)) :=
  {{0, 1, 5}, {0, 2, 4}, {0, 3, 7}, {1, 2, 3}, {1, 4, 9}}

/-- Base cover (nine edges); optional `ps = s(2,5)` added when present. -/
def cover10_45 : Finset (Sym2 (Fin 10)) :=
  {s(0, 1), s(0, 6), s(0, 7), s(1, 8), s(1, 9),
   s(2, 3), s(2, 4), s(3, 7), s(4, 9)}

lemma packing10_45_card : packing10_45.card = 5 := by native_decide

lemma cover10_45_card : cover10_45.card = 9 := by native_decide

lemma packing10_45_pairwise_inter_le_one :
    ∀ s ∈ packing10_45, ∀ t ∈ packing10_45, s ≠ t → (s ∩ t).card ≤ 1 := by
  native_decide

def packing45 (u v p q r s a b : V) : Finset (Finset V) :=
  {{u, v, s}, {u, p, r}, {u, q, a}, {v, p, q}, {v, r, b}}

def cover45 (u v p q r a0 a1 b0 b1 a b : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, a0), s(u, a1), s(v, b0), s(v, b1),
   s(p, q), s(p, r), s(q, a), s(r, b)}

private lemma packing45_image_eq (u v p q r s a0 a1 b0 b1 : V) :
    packing10_45.image (mapTri (labels10 u v p q r s a0 a1 b0 b1)) =
      packing45 u v p q r s a1 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, _, f9⟩ := map_lab u v p q r s a0 a1 b0 b1
  set f := labels10 u v p q r s a0 a1 b0 b1 with hf
  have e1 : mapTri f {0, 1, 5} = ({u, v, s} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f5]
  have e2 : mapTri f {0, 2, 4} = ({u, p, r} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f4]
  have e3 : mapTri f {0, 3, 7} = ({u, q, a1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f7]
  have e4 : mapTri f {1, 2, 3} = ({v, p, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f3]
  have e5 : mapTri f {1, 4, 9} = ({v, r, b1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f9]
  simp only [packing10_45, packing45, image_insert, image_singleton, e1, e2, e3, e4, e5]

private lemma cover45_image_eq (u v p q r s a0 a1 b0 b1 : V) :
    cover10_45.image (Sym2.map (labels10 u v p q r s a0 a1 b0 b1)) =
      cover45 u v p q r a0 a1 b0 b1 a1 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, _, f6, f7, f8, f9⟩ := map_lab u v p q r s a0 a1 b0 b1
  set f := labels10 u v p q r s a0 a1 b0 b1
  have mk (i j : Fin 10) {x y : V} (hi : f i = x) (hj : f j = y) :
      Sym2.map f s(i, j) = s(x, y) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_45, cover45, image_insert, image_singleton,
    mk 0 1 f0 f1, mk 0 6 f0 f6, mk 0 7 f0 f7, mk 1 8 f1 f8, mk 1 9 f1 f9,
    mk 2 3 f2 f3, mk 2 4 f2 f4, mk 3 7 f3 f7, mk 4 9 f4 f9]

lemma packing45_card (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    (packing45 u v p q r s a1 b1).card = 5 := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packing45_image_eq u v p q r s a0 a1 b0 b1,
    card_image_of_injective _ hinjT, packing10_45_card]

lemma packing45_disjoint (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    ∀ σ ∈ packing45 u v p q r s a1 b1,
      ∀ τ ∈ packing45 u v p q r s a1 b1,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  intro σ hs τ ht hst
  rw [← packing45_image_eq u v p q r s a0 a1 b0 b1] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  have hs0t0 : s0 ≠ t0 := fun h => by subst h; exact hst rfl
  have hinter := packing10_45_pairwise_inter_le_one s0 hs0 t0 ht0 hs0t0
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

lemma cover45_card (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    (cover45 u v p q r a0 a1 b0 b1 a1 b1).card = 9 := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← cover45_image_eq u v p q r s a0 a1 b0 b1,
    card_image_of_injective _ hinjE, cover10_45_card]

lemma external45 (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ packing45 u v p q r s a1 b1)
    {e : Sym2 V} (he : e ∈ triEdges t)
    (hZ : ∀ z ∈ ({u, v} : Finset V), z ∉ e) :
    e ∈ cover45 u v p q r a0 a1 b0 b1 a1 b1 := by
  have hu : u ∉ e := hZ u (by simp)
  have hv : v ∉ e := hZ v (by simp)
  have t1 : ({u, v, s} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 1) (k := 5)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 : ({u, p, r} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 2) (k := 4)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 : ({u, q, a1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 3) (k := 7)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 : ({v, p, q} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 2) (k := 3)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 : ({v, r, b1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 4) (k := 9)
      (by decide) (by decide) (by decide) rfl rfl rfl
  simp only [packing45, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · -- external of uvs avoiding {u,v} is s(v,s) or s(u,s) — wait, omit u gives vs; omit both?
    -- Z={u,v}, so both u and v avoided. Only possible external edge is none from {u,v,s}
    -- Actually triEdges of {u,v,s} are uv, us, vs. Avoiding u and v means e has neither → impossible?
    -- Paper: "None uses a spoke to s, so uvs shares no edge with them" for packing disjointness.
    -- For external: edges of packing triangles that avoid Z={u,v}.
    -- For uvs: edges are uv, us, vs. uv meets Z; us meets u∈Z; vs meets v∈Z. So NO external edges!
    -- Contradiction: he says e ∈ triEdges and avoids Z — impossible for this triangle.
    -- So we need False.elim.
    have : False := by
      -- e ∈ {uv, us, vs} and u∉e and v∉e
      have hcard := t1
      have heq := triEdges_eq_of_card3 hcard
      rw [heq] at he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hu (by simp)
      · exact hu (by simp)
      · exact hv (by simp)
    exact this.elim
  · have h := triEdges_omit_vertex t2 he hu; rw [h]; simp [cover45]
  · have h := triEdges_omit_vertex t3 he hu; rw [h]; simp [cover45]
  · have h := triEdges_omit_vertex t4 he hv; rw [h]; simp [cover45]
  · have h := triEdges_omit_vertex t5 he hv; rw [h]; simp [cover45]

/-- Lemma 4.5: path/star fragment with crossed A/B leaf attachments ⇒ reducible. -/
theorem lemma45_certificate (H : HubConfig G)
    (p q r s a0 a1 b0 b1 : V)
    (hC : H.C = {p, q, r, s})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hpq : G.Adj p q) (hpr : G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (hatt : G.Adj q a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v p q r s a0 a1 b0 b1 h10
  let S := packing45 H.u H.v p q r s a1 b1
  -- Cover: base nine edges, plus ps if present
  let X0 := cover45 H.u H.v p q r a0 a1 b0 b1 a1 b1
  let X : Finset (Sym2 V) := if G.Adj p s then insert s(p, s) X0 else X0
  have uvs : G.Adj H.u H.v := H.huv
  have us : G.Adj H.u s := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have vs : G.Adj H.v s := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ur : G.Adj H.u r := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua0 : G.Adj H.u a0 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ua1 : G.Adj H.u a1 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vr : G.Adj H.v r := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vb0 : G.Adj H.v b0 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vb1 : G.Adj H.v b1 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have t1 := card3_of_inj hinj (i := 0) (j := 1) (k := 5)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 := card3_of_inj hinj (i := 0) (j := 2) (k := 4)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 := card3_of_inj hinj (i := 0) (j := 3) (k := 7)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 := card3_of_inj hinj (i := 1) (j := 2) (k := 3)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 := card3_of_inj hinj (i := 1) (j := 4) (k := 9)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packing45_disjoint H.u H.v p q r s a0 a1 b0 b1 hinj⟩
    intro t ht
    simp only [S, packing45, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uvs us vs t1
    · exact is3clique_of_adj G up ur hpr t2
    · exact is3clique_of_adj G uq ua1 hatt.1 t3
    · exact is3clique_of_adj G vp vq hpq t4
    · exact is3clique_of_adj G vr vb1 hatt.2 t5
  have hX0edges : X0 ⊆ G.edgeFinset := by
    intro e he
    simp only [X0, cover45, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (mem_edgeFinset).2 uvs
    · exact (mem_edgeFinset).2 ua0
    · exact (mem_edgeFinset).2 ua1
    · exact (mem_edgeFinset).2 vb0
    · exact (mem_edgeFinset).2 vb1
    · exact (mem_edgeFinset).2 hpq
    · exact (mem_edgeFinset).2 hpr
    · exact (mem_edgeFinset).2 hatt.1
    · exact (mem_edgeFinset).2 hatt.2
  have hXedges : X ⊆ G.edgeFinset := by
    intro e he
    by_cases hps : G.Adj p s
    · have he' : e ∈ insert s(p, s) X0 := by simpa [X, hps] using he
      rcases mem_insert.1 he' with rfl | he0
      · exact (mem_edgeFinset).2 hps
      · exact hX0edges he0
    · have he0 : e ∈ X0 := by simpa [X, hps] using he
      exact hX0edges he0
  have hcardS := packing45_card H.u H.v p q r s a0 a1 b0 b1 hinj
  have hcardX0 := cover45_card H.u H.v p q r s a0 a1 b0 b1 hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 5 := hcardS
    by_cases hps : G.Adj p s
    · have : X = insert s(p, s) X0 := by simp [X, hps]
      have hle : X.card ≤ X0.card + 1 := by
        rw [this]; exact card_insert_le _ _
      have : X0.card = 9 := hcardX0
      omega
    · have : X = X0 := by simp [X, hps]
      rw [this, hcardX0, hS]; omega
  -- coversZ: every triangle through u or v meets X
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ z ∈ ({H.u, H.v} : Finset V), z ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    -- Reuse coversZ42-style case split; X contains all A/B spokes and core edges pq,pr,(ps)
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
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
    have memX0 {e : Sym2 V} (he : e ∈ X0) : e ∈ X := by
      by_cases hps : G.Adj p s <;> simp [X, hps, he]
    have memXps (hps : G.Adj p s) : s(p, s) ∈ X := by simp [X, hps]
    have hzx : G.Adj hub px := hadj hub hhubt px hxyt hx_ne.symm
    have hzy : G.Adj hub py := hadj hub hhubt py hyyt hy_ne.symm
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hxy
    rcases hhub with rfl | rfl
    · -- hub = u
      have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv; exact meet s(H.u, H.v) (memX0 (by simp [X0, cover45])) him_zx
      by_cases hyv : py = H.v
      · subst hyv; exact meet s(H.u, H.v) (memX0 (by simp [X0, cover45])) him_zy
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxAmem : px ∈ H.A
      · have hpa : px = a0 ∨ px = a1 := by simpa [hA] using hxAmem
        rcases hpa with hpa | hpa
        · exact meet s(H.u, a0) (memX0 (by simp [X0, cover45])) (hpa ▸ him_zx)
        · exact meet s(H.u, a1) (memX0 (by simp [X0, cover45])) (hpa ▸ him_zx)
      by_cases hyAmem : py ∈ H.A
      · have hpa : py = a0 ∨ py = a1 := by simpa [hA] using hyAmem
        rcases hpa with hpa | hpa
        · exact meet s(H.u, a0) (memX0 (by simp [X0, cover45])) (hpa ▸ him_zy)
        · exact meet s(H.u, a1) (memX0 (by simp [X0, cover45])) (hpa ▸ him_zy)
      have hxC : px ∈ H.C := by simpa [mem_union, hxAmem] using hxCA
      have hyC : py ∈ H.C := by simpa [mem_union, hyAmem] using hyCA
      rcases honly px hxC py hyC hxyAdj with hr | hr | hr
      · rw [hr] at him_rim; exact meet s(p, q) (memX0 (by simp [X0, cover45])) him_rim
      · rw [hr] at him_rim; exact meet s(p, r) (memX0 (by simp [X0, cover45])) him_rim
      · rw [hr] at him_rim
        have hps : G.Adj p s := by
          have heq : s(px, py) = s(p, s) := hr
          have hem : s(px, py) ∈ G.edgeFinset := (mem_edgeFinset).2 hxyAdj
          exact (mem_edgeFinset).1 (heq ▸ hem)
        exact meet s(p, s) (memXps hps) him_rim
    · -- hub = v
      have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zx
        exact meet s(H.u, H.v) (memX0 (by simp [X0, cover45])) heT
      by_cases hyu : py = H.u
      · subst hyu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zy
        exact meet s(H.u, H.v) (memX0 (by simp [X0, cover45])) heT
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxBmem : px ∈ H.B
      · have hpb : px = b0 ∨ px = b1 := by simpa [hB] using hxBmem
        rcases hpb with hpb | hpb
        · exact meet s(H.v, b0) (memX0 (by simp [X0, cover45])) (hpb ▸ him_zx)
        · exact meet s(H.v, b1) (memX0 (by simp [X0, cover45])) (hpb ▸ him_zx)
      by_cases hyBmem : py ∈ H.B
      · have hpb : py = b0 ∨ py = b1 := by simpa [hB] using hyBmem
        rcases hpb with hpb | hpb
        · exact meet s(H.v, b0) (memX0 (by simp [X0, cover45])) (hpb ▸ him_zy)
        · exact meet s(H.v, b1) (memX0 (by simp [X0, cover45])) (hpb ▸ him_zy)
      have hxC : px ∈ H.C := by simpa [mem_union, hxBmem] using hxCB
      have hyC : py ∈ H.C := by simpa [mem_union, hyBmem] using hyCB
      rcases honly px hxC py hyC hxyAdj with hr | hr | hr
      · rw [hr] at him_rim; exact meet s(p, q) (memX0 (by simp [X0, cover45])) him_rim
      · rw [hr] at him_rim; exact meet s(p, r) (memX0 (by simp [X0, cover45])) him_rim
      · rw [hr] at him_rim
        have hps : G.Adj p s := by
          have heq : s(px, py) = s(p, s) := hr
          have hem : s(px, py) ∈ G.edgeFinset := (mem_edgeFinset).2 hxyAdj
          exact (mem_edgeFinset).1 (heq ▸ hem)
        exact meet s(p, s) (memXps hps) him_rim
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t, (∀ z ∈ ({H.u, H.v} : Finset V), z ∉ e) →
      e ∈ X := by
    intro t ht e he hZ
    have he0 := external45 H.u H.v p q r s a0 a1 b0 b1 hinj ht he hZ
    by_cases hps : G.Adj p s
    · simpa [X, hps] using (mem_insert_of_mem he0 : e ∈ insert s(p, s) X0)
    · simpa [X, hps] using he0
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩


/-! ### Lemma 4.8: P₄ fragment certificate -/

/-- Fin-10 packing for Lemma 4.8: `{uvs, uqr, upa, vpq, vrb}`. -/
def packing10_48 : Finset (Finset (Fin 10)) :=
  {{0, 1, 5}, {0, 3, 4}, {0, 2, 7}, {1, 2, 3}, {1, 4, 9}}

/-- Ten-edge cover for Lemma 4.8. -/
def cover10_48 : Finset (Sym2 (Fin 10)) :=
  {s(0, 1), s(0, 6), s(0, 7), s(1, 8), s(1, 9),
   s(2, 3), s(3, 4), s(4, 5), s(2, 7), s(4, 9)}

lemma packing10_48_card : packing10_48.card = 5 := by native_decide
lemma cover10_48_card : cover10_48.card = 10 := by native_decide
lemma packing10_48_pairwise_inter_le_one :
    ∀ σ ∈ packing10_48, ∀ τ ∈ packing10_48, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

def packing48 (u v p q r s a b : V) : Finset (Finset V) :=
  {{u, v, s}, {u, q, r}, {u, p, a}, {v, p, q}, {v, r, b}}

def cover48 (u v p q r s a0 a1 b0 b1 a b : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, a0), s(u, a1), s(v, b0), s(v, b1),
   s(p, q), s(q, r), s(r, s), s(p, a), s(r, b)}

private lemma packing48_image_eq (u v p q r s a0 a1 b0 b1 : V) :
    packing10_48.image (mapTri (labels10 u v p q r s a0 a1 b0 b1)) =
      packing48 u v p q r s a1 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, _, f9⟩ := map_lab u v p q r s a0 a1 b0 b1
  set f := labels10 u v p q r s a0 a1 b0 b1
  have e1 : mapTri f {0, 1, 5} = ({u, v, s} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f5]
  have e2 : mapTri f {0, 3, 4} = ({u, q, r} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f4]
  have e3 : mapTri f {0, 2, 7} = ({u, p, a1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f7]
  have e4 : mapTri f {1, 2, 3} = ({v, p, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f3]
  have e5 : mapTri f {1, 4, 9} = ({v, r, b1} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f9]
  simp only [packing10_48, packing48, image_insert, image_singleton, e1, e2, e3, e4, e5]

private lemma cover48_image_eq (u v p q r s a0 a1 b0 b1 : V) :
    cover10_48.image (Sym2.map (labels10 u v p q r s a0 a1 b0 b1)) =
      cover48 u v p q r s a0 a1 b0 b1 a1 b1 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := map_lab u v p q r s a0 a1 b0 b1
  set f := labels10 u v p q r s a0 a1 b0 b1
  have mk (i j : Fin 10) {x y : V} (hi : f i = x) (hj : f j = y) :
      Sym2.map f s(i, j) = s(x, y) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_48, cover48, image_insert, image_singleton,
    mk 0 1 f0 f1, mk 0 6 f0 f6, mk 0 7 f0 f7, mk 1 8 f1 f8, mk 1 9 f1 f9,
    mk 2 3 f2 f3, mk 3 4 f3 f4, mk 4 5 f4 f5, mk 2 7 f2 f7, mk 4 9 f4 f9]

lemma packing48_card (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    (packing48 u v p q r s a1 b1).card = 5 := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packing48_image_eq u v p q r s a0 a1 b0 b1,
    card_image_of_injective _ hinjT, packing10_48_card]

lemma packing48_disjoint (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    ∀ σ ∈ packing48 u v p q r s a1 b1,
      ∀ τ ∈ packing48 u v p q r s a1 b1,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  intro σ hs τ ht hst
  rw [← packing48_image_eq u v p q r s a0 a1 b0 b1] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  have hs0t0 : s0 ≠ t0 := fun h => by subst h; exact hst rfl
  have hinter := packing10_48_pairwise_inter_le_one s0 hs0 t0 ht0 hs0t0
  have hinter' : (mapTri f s0 ∩ mapTri f t0).card ≤ 1 := by
    have : mapTri f s0 ∩ mapTri f t0 = (s0 ∩ t0).image f := by
      simp only [mapTri]; exact (Finset.image_inter s0 t0 hinj).symm
    rw [this]; exact le_trans card_image_le hinter
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

lemma cover48_card (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1)) :
    (cover48 u v p q r s a0 a1 b0 b1 a1 b1).card = 10 := by
  let f := labels10 u v p q r s a0 a1 b0 b1
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← cover48_image_eq u v p q r s a0 a1 b0 b1,
    card_image_of_injective _ hinjE, cover10_48_card]

/-- External packing edges of Lemma 4.8 lie in the cover. -/
lemma external48 (u v p q r s a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v p q r s a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ packing48 u v p q r s a1 b1)
    {e : Sym2 V} (he : e ∈ triEdges t)
    (hZ : ∀ z ∈ ({u, v} : Finset V), z ∉ e) :
    e ∈ cover48 u v p q r s a0 a1 b0 b1 a1 b1 := by
  have hu : u ∉ e := hZ u (by simp)
  have hv : v ∉ e := hZ v (by simp)
  have t1 : ({u, v, s} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 1) (k := 5)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 : ({u, q, r} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 3) (k := 4)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 : ({u, p, a1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 0) (j := 2) (k := 7)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 : ({v, p, q} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 2) (k := 3)
      (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 : ({v, r, b1} : Finset V).card = 3 :=
    card3_of_inj hinj (i := 1) (j := 4) (k := 9)
      (by decide) (by decide) (by decide) rfl rfl rfl
  simp only [packing48, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · have : False := by
      have heq := triEdges_eq_of_card3 t1
      rw [heq] at he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hu (by simp)
      · exact hu (by simp)
      · exact hv (by simp)
    exact this.elim
  · have h := triEdges_omit_vertex t2 he hu; rw [h]; simp [cover48]
  · have h := triEdges_omit_vertex t3 he hu; rw [h]; simp [cover48]
  · have h := triEdges_omit_vertex t4 he hv; rw [h]; simp [cover48]
  · have h := triEdges_omit_vertex t5 he hv; rw [h]; simp [cover48]

/-- **Lemma 4.8**: P₄ with attachments `pa`, `rb` → five-triangle / ten-edge certificate. -/
theorem lemma48_certificate (H : HubConfig G)
    (p q r s a0 a1 b0 b1 : V)
    (hC : H.C = {p, q, r, s})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(q, r) ∨ s(x, y) = s(r, s))
    (hatt : G.Adj p a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v p q r s a0 a1 b0 b1 h10
  let S := packing48 H.u H.v p q r s a1 b1
  let X := cover48 H.u H.v p q r s a0 a1 b0 b1 a1 b1
  have uvs : G.Adj H.u H.v := H.huv
  have us : G.Adj H.u s := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have vs : G.Adj H.v s := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ur : G.Adj H.u r := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua0 : G.Adj H.u a0 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ua1 : G.Adj H.u a1 := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vr : G.Adj H.v r := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vb0 : G.Adj H.v b0 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vb1 : G.Adj H.v b1 := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have t1 := card3_of_inj hinj (i := 0) (j := 1) (k := 5)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t2 := card3_of_inj hinj (i := 0) (j := 3) (k := 4)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t3 := card3_of_inj hinj (i := 0) (j := 2) (k := 7)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t4 := card3_of_inj hinj (i := 1) (j := 2) (k := 3)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have t5 := card3_of_inj hinj (i := 1) (j := 4) (k := 9)
    (by decide) (by decide) (by decide) rfl rfl rfl
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packing48_disjoint H.u H.v p q r s a0 a1 b0 b1 hinj⟩
    intro t ht
    simp only [S, packing48, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uvs us vs t1
    · exact is3clique_of_adj G uq ur hqr t2
    · exact is3clique_of_adj G up ua1 hatt.1 t3
    · exact is3clique_of_adj G vp vq hpq t4
    · exact is3clique_of_adj G vr vb1 hatt.2 t5
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, cover48, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 uvs
    · subst h; exact (mem_edgeFinset).2 ua0
    · subst h; exact (mem_edgeFinset).2 ua1
    · subst h; exact (mem_edgeFinset).2 vb0
    · subst h; exact (mem_edgeFinset).2 vb1
    · subst h; exact (mem_edgeFinset).2 hpq
    · subst h; exact (mem_edgeFinset).2 hqr
    · subst h; exact (mem_edgeFinset).2 hrs
    · subst h; exact (mem_edgeFinset).2 hatt.1
    · subst h; exact (mem_edgeFinset).2 hatt.2
  have hcardS := packing48_card H.u H.v p q r s a0 a1 b0 b1 hinj
  have hcardX := cover48_card H.u H.v p q r s a0 a1 b0 b1 hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 5 := hcardS
    have hX : X.card = 10 := hcardX
    omega
  -- coversZ: every hub triangle meets X (A/B spokes + path edges pq,qr,rs)
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ z ∈ ({H.u, H.v} : Finset V), z ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
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
    · have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv; exact meet s(H.u, H.v) (by simp [X, cover48]) him_zx
      by_cases hyv : py = H.v
      · subst hyv; exact meet s(H.u, H.v) (by simp [X, cover48]) him_zy
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxAmem : px ∈ H.A
      · have hpa : px = a0 ∨ px = a1 := by simpa [hA] using hxAmem
        rcases hpa with hpa | hpa
        · exact meet s(H.u, a0) (by simp [X, cover48]) (hpa ▸ him_zx)
        · exact meet s(H.u, a1) (by simp [X, cover48]) (hpa ▸ him_zx)
      by_cases hyAmem : py ∈ H.A
      · have hpa : py = a0 ∨ py = a1 := by simpa [hA] using hyAmem
        rcases hpa with hpa | hpa
        · exact meet s(H.u, a0) (by simp [X, cover48]) (hpa ▸ him_zy)
        · exact meet s(H.u, a1) (by simp [X, cover48]) (hpa ▸ him_zy)
      have hxC : px ∈ H.C := by simpa [mem_union, hxAmem] using hxCA
      have hyC : py ∈ H.C := by simpa [mem_union, hyAmem] using hyCA
      rcases honly px hxC py hyC hxyAdj with hr | hr | hr
      · rw [hr] at him_rim; exact meet s(p, q) (by simp [X, cover48]) him_rim
      · rw [hr] at him_rim; exact meet s(q, r) (by simp [X, cover48]) him_rim
      · rw [hr] at him_rim; exact meet s(r, s) (by simp [X, cover48]) him_rim
    · have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zx
        exact meet s(H.u, H.v) (by simp [X, cover48]) heT
      by_cases hyu : py = H.u
      · subst hyu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zy
        exact meet s(H.u, H.v) (by simp [X, cover48]) heT
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxBmem : px ∈ H.B
      · have hpb : px = b0 ∨ px = b1 := by simpa [hB] using hxBmem
        rcases hpb with hpb | hpb
        · exact meet s(H.v, b0) (by simp [X, cover48]) (hpb ▸ him_zx)
        · exact meet s(H.v, b1) (by simp [X, cover48]) (hpb ▸ him_zx)
      by_cases hyBmem : py ∈ H.B
      · have hpb : py = b0 ∨ py = b1 := by simpa [hB] using hyBmem
        rcases hpb with hpb | hpb
        · exact meet s(H.v, b0) (by simp [X, cover48]) (hpb ▸ him_zy)
        · exact meet s(H.v, b1) (by simp [X, cover48]) (hpb ▸ him_zy)
      have hxC : px ∈ H.C := by simpa [mem_union, hxBmem] using hxCB
      have hyC : py ∈ H.C := by simpa [mem_union, hyBmem] using hyCB
      rcases honly px hxC py hyC hxyAdj with hr | hr | hr
      · rw [hr] at him_rim; exact meet s(p, q) (by simp [X, cover48]) him_rim
      · rw [hr] at him_rim; exact meet s(q, r) (by simp [X, cover48]) him_rim
      · rw [hr] at him_rim; exact meet s(r, s) (by simp [X, cover48]) him_rim
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t, (∀ z ∈ ({H.u, H.v} : Finset V), z ∉ e) →
      e ∈ X := by
    intro t ht e he hZ
    exact external48 H.u H.v p q r s a0 a1 b0 b1 hinj ht he hZ
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩


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
    (_hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
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



/-- Classify vertices outside Q={z,q,d0} in the u-link (Lemma 4.4(2) setup). -/
lemma path_lemma44_classify (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (d0 d1 : V) (hAeq : H.A = {d0, d1})
    {x : V} (hxN : x ∈ G.neighborFinset H.u)
    (hxQ : x ∉ ({H.v, q, d0} : Finset V)) :
    x = p ∨ x = r ∨ x = s ∨ x = d1 := by
  rw [H.hNu] at hxN
  simp only [mem_insert, mem_union, mem_singleton, not_or] at hxN hxQ
  rcases hxN with rfl | hCmem | hAmem
  · exact absurd rfl hxQ.1
  · have : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hCmem
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd rfl hxQ.2.1
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have : x ∈ ({d0, d1} : Finset V) := by rw [← hAeq]; exact hAmem
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact absurd rfl hxQ.2.2
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- Outside edges ⊆ {pr, s d1} under Lemma 4.4(2) hypotheses. -/
lemma path_outside_Q_lemma44 (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (d0 d1 : V) (hAeq : H.A = {d0, d1})
    (hre : G.neighborFinset r ∩ H.A = ∅)
    (hpd1 : ¬ G.Adj p d1)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ x ∈ e, x ∉ ({H.v, q, d0} : Finset V)) :
    e = s(p, r) ∨ e = s(s, d1) := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have haQ : a ∉ ({H.v, q, d0} : Finset V) := hOut a (by simp)
  have hbQ : b ∉ ({H.v, q, d0} : Finset V) := hOut b (by simp)
  have haCl := path_lemma44_classify G H p q r s hC d0 d1 hAeq hab.1 haQ
  have hbCl := path_lemma44_classify G H p q r s hC d0 d1 hAeq hab.2.1 hbQ
  have hdist := core4_distinct G H hC
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have not_rd1 : ¬ G.Adj r d1 := by
    intro h
    have : d1 ∈ G.neighborFinset r ∩ H.A :=
      mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 h, hd1A⟩
    simpa [hre] using this
  have core_ne_ps {x y : V} (hx : x ∈ H.C) (hy : y ∈ H.C) (hAdj : G.Adj x y)
      (hne_pq : ¬(s(x, y) = s(p, q))) (hne_pr : ¬(s(x, y) = s(p, r))) : False := by
    rcases honly x hx y hy hAdj with h | h <;> contradiction
  have not_ps : ¬ G.Adj p s := by
    intro h; exact core_ne_ps hpC hsC h
      (fun heq => by
        have : s = q := by
          have hs : s ∈ ({p, q} : Finset V) := by
            have : s ∈ s(p, q).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p q
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at hs
          rcases hs with h' | h'
          · exact (hdist.2.2.1 h'.symm).elim
          · exact h'
        exact hdist.2.2.2.2.1 this.symm)
      (fun heq => by
        have : s = r := by
          have hs : s ∈ ({p, r} : Finset V) := by
            have : s ∈ s(p, r).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p r
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at hs
          rcases hs with h' | h'
          · exact (hdist.2.2.1 h'.symm).elim
          · exact h'
        exact hdist.2.2.2.2.2 this.symm)
  have not_rs : ¬ G.Adj r s := by
    intro h; exact core_ne_ps hrC hsC h
      (fun heq => by
        -- {r,s}={p,q}
        have hr' : r = p ∨ r = q := by
          have : r ∈ ({p, q} : Finset V) := by
            have : r ∈ s(p, q).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p q
            simpa [Sym2.toFinset_mk_eq] using this
          simpa using this
        rcases hr' with hr' | hr'
        · exact hdist.2.1 hr'.symm
        · exact hdist.2.2.2.1 hr'.symm)
      (fun heq => by
        -- {r,s}={p,r} ⇒ s=p
        have hs' : s = p ∨ s = r := by
          have : s ∈ ({p, r} : Finset V) := by
            have : s ∈ s(p, r).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p r
            simpa [Sym2.toFinset_mk_eq] using this
          simpa using this
        rcases hs' with hs' | hs'
        · exact hdist.2.2.1 hs'.symm
        · exact hdist.2.2.2.2.2 hs'.symm)
  rcases haCl with ha | ha | ha | ha <;> rcases hbCl with hb | hb | hb | hb
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inl (by rw [ha, hb])
  · exact False.elim (not_ps (by rwa [ha, hb] at hG))
  · exact False.elim (hpd1 (by rwa [ha, hb] at hG))
  · exact Or.inl (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact False.elim (not_rs (by rwa [ha, hb] at hG))
  · exact False.elim (not_rd1 (by rwa [ha, hb] at hG))
  · exact False.elim (not_ps (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_rs (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inr (by rw [ha, hb])
  · exact False.elim (hpd1 (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_rd1 (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact Or.inr (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))

/-- Lemma 4.4(2): if `r` has no private neighbor and `p` misses a private, the link is WKE. -/
theorem path_center_both_privates (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hedges : G.Adj p q ∧ G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (d0 d1 : V) (hAeq : H.A = {d0, d1}) (hd01 : d0 ≠ d1)
    (hre : G.neighborFinset r ∩ H.A = ∅)
    (hpd1 : ¬ G.Adj p d1) :
    False := by
  classical
  have hdist := core4_distinct G H hC
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hqC : q ∈ H.C := by rw [hC]; simp
  have hrC : r ∈ H.C := by rw [hC]; simp
  have hsC : s ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hpN := core_mem_Nu G H hpC
  have hqN := core_mem_Nu G H hqC
  have hrN := core_mem_Nu G H hrC
  have hsN := core_mem_Nu G H hsC
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have hd0N : d0 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hd1N : d1 ∈ G.neighborFinset H.u := by rw [H.hNu, hAeq]; simp
  have hzq := z_adj_core G H hqC
  have hzs := z_adj_core G H hsC
  have hz_ne_q := ne_z_of_core G H hqC
  have hz_ne_p := ne_z_of_core G H hpC
  have hz_ne_s := ne_z_of_core G H hsC
  have hz_ne_r := ne_z_of_core G H hrC
  have hz_ne_d0 := ne_z_of_priv G H hd0A
  have hz_ne_d1 := ne_z_of_priv G H hd1A
  have hq_ne_d0 := ne_core_priv G H hqC hd0A
  have hp_ne_d1 := ne_core_priv G H hpC hd1A
  have hs_ne_d1 := ne_core_priv G H hsC hd1A
  have hr_ne_d1 := ne_core_priv G H hrC hd1A
  -- Q = {z, q, d0}
  let Q : Finset V := {H.v, q, d0}
  have hQcard : Q.card = 3 := by
    change ({H.v, q, d0} : Finset V).card = 3
    rw [card_insert_of_notMem (by simp [hz_ne_q, hz_ne_d0]),
      card_insert_of_notMem (by simp [hq_ne_d0]), card_singleton]
  by_cases hsd1 : G.Adj s d1
  · -- M = {pr, s d1, z q}
    let M : Finset (Sym2 V) := {s(p, r), s(s, d1), s(H.v, q)}
    have hM : IsEdgeMatching (linkGraph G H.u) M := by
      refine ⟨?_, ?_⟩
      · intro e he; simp only [M, mem_insert, mem_singleton] at he
        rcases he with h | h | h
        · subst h; exact Prop31.link_edge G H.u p r hpN hrN hedges.2
        · subst h; exact Prop31.link_edge G H.u s d1 hsN hd1N hsd1
        · subst h; exact Prop31.link_edge G H.u H.v q hzN hqN hzq
      · intro e he f hf hne
        simp only [M, mem_insert, mem_singleton] at he hf
        -- pairwise disjoint toFinsets
        have hdisj_pr_sd : Disjoint s(p, r).toFinset s(s, d1).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb
          simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact hdist.2.2.1
          · exact hp_ne_d1
          · exact hdist.2.2.2.2.2
          · exact hr_ne_d1
        have hdisj_pr_zq : Disjoint s(p, r).toFinset s(H.v, q).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb
          simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact hz_ne_p.symm
          · exact hdist.1
          · exact hz_ne_r.symm
          · exact hdist.2.2.2.1.symm
        have hdisj_sd_zq : Disjoint s(s, d1).toFinset s(H.v, q).toFinset := by
          rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
          refine Finset.disjoint_iff_ne.2 ?_
          intro a ha b hb
          simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact hz_ne_s.symm
          · exact hdist.2.2.2.2.1.symm
          · exact hz_ne_d1.symm
          · exact (ne_core_priv G H hqC hd1A).symm
        rcases he with he | he | he <;> rcases hf with hf | hf | hf
        · subst he; subst hf; exact absurd rfl hne
        · subst he; subst hf; exact hdisj_pr_sd
        · subst he; subst hf; exact hdisj_pr_zq
        · subst he; subst hf; exact hdisj_pr_sd.symm
        · subst he; subst hf; exact absurd rfl hne
        · subst he; subst hf; exact hdisj_sd_zq
        · subst he; subst hf; exact hdisj_pr_zq.symm
        · subst he; subst hf; exact hdisj_sd_zq.symm
        · subst he; subst hf; exact absurd rfl hne
    have hMcard : M.card = 3 := by
      change ({s(p, r), s(s, d1), s(H.v, q)} : Finset (Sym2 V)).card = 3
      have n1 : s(p, r) ≠ s(s, d1) := by
        intro heq
        have : p ∈ ({s, d1} : Finset V) := by
          have : p ∈ s(s, d1).toFinset := by
            simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
          simpa [Sym2.toFinset_mk_eq] using this
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact hdist.2.2.1 h'
        · exact hp_ne_d1 h'
      have n2 : s(p, r) ≠ s(H.v, q) := by
        intro heq
        have : p ∈ ({H.v, q} : Finset V) := by
          have : p ∈ s(H.v, q).toFinset := by
            simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
          simpa [Sym2.toFinset_mk_eq] using this
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact hz_ne_p.symm h'
        · exact hdist.1 h'
      have n3 : s(s, d1) ≠ s(H.v, q) := by
        intro heq
        have : s ∈ ({H.v, q} : Finset V) := by
          have : s ∈ s(H.v, q).toFinset := by
            simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left s d1
          simpa [Sym2.toFinset_mk_eq] using this
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact hz_ne_s h'.symm
        · exact hdist.2.2.2.2.1 h'.symm
      simp [card_insert_of_notMem, n1, n2, n3]
    have : IsWKE (linkGraph G H.u) :=
      isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
        rcases path_outside_Q_lemma44 G H p q r s hC honly d0 d1 hAeq hre hpd1 he hOut
          with h | h <;> simp [M, h]⟩
    exact hnot this
  · -- sd1 absent: connectedness ⇒ d1q or d1d0
    have hd1_force : G.Adj d1 q ∨ G.Adj d1 d0 := by
      by_contra hforce
      push Not at hforce
      obtain ⟨hnq, hnd0⟩ := hforce
      -- d1 has no link-neighbor ⇒ degree 0
      have hdeg0 : (linkGraph G H.u).degree d1 = 0 := by
        simp only [← card_neighborFinset_eq_degree]
        refine card_eq_zero.2 (eq_empty_iff_forall_notMem.2 ?_)
        intro x hx
        have hAdjL : (linkGraph G H.u).Adj d1 x := (mem_neighborFinset _ _ _).1 hx
        have hG : G.Adj d1 x := hAdjL.2.2
        have hxN := hAdjL.2.1
        rw [H.hNu] at hxN
        simp only [mem_insert, mem_union] at hxN
        rcases hxN with rfl | hxc | hxa
        · exact not_adj_hub_priv G H hd1A hG.symm
        · have : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hxc
          simp only [mem_insert, mem_singleton] at this
          rcases this with hxp | hxq | hxr | hxs
          · exact hpd1 (hxp ▸ hG.symm)
          · exact hnq (hxq ▸ hG)
          · have : d1 ∈ G.neighborFinset r ∩ H.A :=
              mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 (hxr ▸ hG.symm), hd1A⟩
            simpa [hre] using this
          · exact hsd1 (hxs ▸ hG.symm)
        · have : x = d0 ∨ x = d1 := by rw [hAeq] at hxa; simpa using hxa
          rcases this with rfl | rfl
          · exact hnd0 hG
          · exact G.irrefl hG
      have hyne : d1 ≠ H.v := hz_ne_d1.symm
      exact (not_reachable_of_left_degree_zero hyne hdeg0) (hconn d1 (by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hd1A)) H.v (by rw [H.hNu]; exact mem_insert_self _ _))
    rcases hd1_force with hd1q | hd1d0
    · -- M = {pr, d1 q, z s}
      let M : Finset (Sym2 V) := {s(p, r), s(d1, q), s(H.v, s)}
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u p r hpN hrN hedges.2
          · subst h; exact Prop31.link_edge G H.u d1 q hd1N hqN hd1q
          · subst h; exact Prop31.link_edge G H.u H.v s hzN hsN hzs
        · intro e he f hf hne
          simp only [M, mem_insert, mem_singleton] at he hf
          have hdisj1 : Disjoint s(p, r).toFinset s(d1, q).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hp_ne_d1
            · exact hdist.1
            · exact hr_ne_d1
            · exact hdist.2.2.2.1.symm
          have hdisj2 : Disjoint s(p, r).toFinset s(H.v, s).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hz_ne_p.symm
            · exact hdist.2.2.1
            · exact hz_ne_r.symm
            · exact hdist.2.2.2.2.2
          have hdisj3 : Disjoint s(d1, q).toFinset s(H.v, s).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hz_ne_d1.symm
            · exact hs_ne_d1.symm
            · exact hz_ne_q.symm
            · exact hdist.2.2.2.2.1
          rcases he with he | he | he <;> rcases hf with hf | hf | hf
          · subst he; subst hf; exact absurd rfl hne
          · subst he; subst hf; exact hdisj1
          · subst he; subst hf; exact hdisj2
          · subst he; subst hf; exact hdisj1.symm
          · subst he; subst hf; exact absurd rfl hne
          · subst he; subst hf; exact hdisj3
          · subst he; subst hf; exact hdisj2.symm
          · subst he; subst hf; exact hdisj3.symm
          · subst he; subst hf; exact absurd rfl hne
      have hMcard : M.card = 3 := by
        change ({s(p, r), s(d1, q), s(H.v, s)} : Finset (Sym2 V)).card = 3
        have n1 : s(p, r) ≠ s(d1, q) := by
          intro heq
          have : p ∈ ({d1, q} : Finset V) := by
            have : p ∈ s(d1, q).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hp_ne_d1 h'
          · exact hdist.1 h'
        have n2 : s(p, r) ≠ s(H.v, s) := by
          intro heq
          have : p ∈ ({H.v, s} : Finset V) := by
            have : p ∈ s(H.v, s).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hz_ne_p.symm h'
          · exact hdist.2.2.1 h'
        have n3 : s(d1, q) ≠ s(H.v, s) := by
          intro heq
          have : d1 ∈ ({H.v, s} : Finset V) := by
            have : d1 ∈ s(H.v, s).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left d1 q
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hz_ne_d1.symm h'
          · exact hs_ne_d1.symm h'
        simp [card_insert_of_notMem, n1, n2, n3]
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
          rcases path_outside_Q_lemma44 G H p q r s hC honly d0 d1 hAeq hre hpd1 he hOut
            with h | h
          · simp [M, h]
          · exact False.elim (hsd1 (by
              have : s(s, d1) ∈ (linkGraph G H.u).edgeFinset := by simpa [← h] using he
              exact (mem_edgeFinset (G := linkGraph G H.u)).1 this |>.2.2))⟩
      exact hnot this
    · -- M = {pr, d1 d0, z s}
      let M : Finset (Sym2 V) := {s(p, r), s(d1, d0), s(H.v, s)}
      have hM : IsEdgeMatching (linkGraph G H.u) M := by
        refine ⟨?_, ?_⟩
        · intro e he; simp only [M, mem_insert, mem_singleton] at he
          rcases he with h | h | h
          · subst h; exact Prop31.link_edge G H.u p r hpN hrN hedges.2
          · subst h; exact Prop31.link_edge G H.u d1 d0 hd1N hd0N hd1d0
          · subst h; exact Prop31.link_edge G H.u H.v s hzN hsN hzs
        · intro e he f hf hne
          simp only [M, mem_insert, mem_singleton] at he hf
          have hdisj1 : Disjoint s(p, r).toFinset s(d1, d0).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hp_ne_d1
            · exact (ne_core_priv G H hpC hd0A)
            · exact hr_ne_d1
            · exact (ne_core_priv G H hrC hd0A)
          have hdisj2 : Disjoint s(p, r).toFinset s(H.v, s).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hz_ne_p.symm
            · exact hdist.2.2.1
            · exact hz_ne_r.symm
            · exact hdist.2.2.2.2.2
          have hdisj3 : Disjoint s(d1, d0).toFinset s(H.v, s).toFinset := by
            rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
            refine Finset.disjoint_iff_ne.2 ?_
            intro a ha b hb
            simp only [mem_insert, mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact hz_ne_d1.symm
            · exact hs_ne_d1.symm
            · exact hz_ne_d0.symm
            · exact (ne_core_priv G H hsC hd0A).symm
          rcases he with he | he | he <;> rcases hf with hf | hf | hf
          · subst he; subst hf; exact absurd rfl hne
          · subst he; subst hf; exact hdisj1
          · subst he; subst hf; exact hdisj2
          · subst he; subst hf; exact hdisj1.symm
          · subst he; subst hf; exact absurd rfl hne
          · subst he; subst hf; exact hdisj3
          · subst he; subst hf; exact hdisj2.symm
          · subst he; subst hf; exact hdisj3.symm
          · subst he; subst hf; exact absurd rfl hne
      have hMcard : M.card = 3 := by
        change ({s(p, r), s(d1, d0), s(H.v, s)} : Finset (Sym2 V)).card = 3
        have n1 : s(p, r) ≠ s(d1, d0) := by
          intro heq
          have : p ∈ ({d1, d0} : Finset V) := by
            have : p ∈ s(d1, d0).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hp_ne_d1 h'
          · exact (ne_core_priv G H hpC hd0A) h'
        have n2 : s(p, r) ≠ s(H.v, s) := by
          intro heq
          have : p ∈ ({H.v, s} : Finset V) := by
            have : p ∈ s(H.v, s).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left p r
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hz_ne_p.symm h'
          · exact hdist.2.2.1 h'
        have n3 : s(d1, d0) ≠ s(H.v, s) := by
          intro heq
          have : d1 ∈ ({H.v, s} : Finset V) := by
            have : d1 ∈ s(H.v, s).toFinset := by
              simpa [← heq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_left d1 d0
            simpa [Sym2.toFinset_mk_eq] using this
          simp only [mem_insert, mem_singleton] at this
          rcases this with h' | h'
          · exact hz_ne_d1.symm h'
          · exact hs_ne_d1.symm h'
        simp [card_insert_of_notMem, n1, n2, n3]
      have : IsWKE (linkGraph G H.u) :=
        isWKE_of_witness _ ⟨hM, Nat.le_of_eq (hQcard.trans hMcard.symm), fun e he hOut => by
          rcases path_outside_Q_lemma44 G H p q r s hC honly d0 d1 hAeq hre hpd1 he hOut
            with h | h
          · simp [M, h]
          · exact False.elim (hsd1 (by
              have : s(s, d1) ∈ (linkGraph G H.u).edgeFinset := by simpa [← h] using he
              exact (mem_edgeFinset (G := linkGraph G H.u)).1 this |>.2.2))⟩
      exact hnot this


end PathCore


open MatchingCore
open StarCore
open PathCore

/-- Labelled star/path fragment with crossed attachments → Lemma 4.5. -/
theorem lemma45_reducible (H : HubConfig G)
    (p q r s a0 a1 b0 b1 : V)
    (hC : H.C = {p, q, r, s})
    (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (hpq : G.Adj p q) (hpr : G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (hatt : G.Adj q a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) :=
  lemma45_certificate G H p q r s a0 a1 b0 b1 hC hA hB hpq hpr honly hatt h10

/-- **Proposition 4.6** (labelled): star with leaf `q` A-attached and leaf `r` B-attached. -/
theorem star_core_of_labels (H : HubConfig G)
    (p q r s a0 a1 b0 b1 : V)
    (hC : H.C = {p, q, r, s})
    (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (hstar : G.Adj p q ∧ G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s))
    (hatt : G.Adj q a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) :=
  lemma45_reducible G H p q r s a0 a1 b0 b1 hC hA hB hstar.1 hstar.2.1 honly hatt h10

/-- Helper: third leaf of a 3-set. -/
lemma third_of_three {q r s q' r' : V}
    (hcard : ({q, r, s} : Finset V).card = 3)
    (hq' : q' ∈ ({q, r, s} : Finset V)) (hr' : r' ∈ ({q, r, s} : Finset V))
    (hne : q' ≠ r') :
    ∃ s', ({q', r', s'} : Finset V) = {q, r, s} := by
  have hsub2 : ({q', r'} : Finset V) ⊆ {q, r, s} := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h2 : ({q', r'} : Finset V).card = 2 := by
    rw [card_insert_of_notMem (by simp [hne]), card_singleton]
  have hrest : (({q, r, s} : Finset V) \ {q', r'}).card = 1 := by
    rw [card_sdiff]
    have hinter : ({q', r'} ∩ ({q, r, s} : Finset V)) = {q', r'} :=
      inter_eq_left.2 hsub2
    rw [hinter, h2, hcard]
  obtain ⟨s', hs'eq⟩ := card_eq_one.1 hrest
  refine ⟨s', ?_⟩
  have hu := union_sdiff_of_subset hsub2
  rw [hs'eq] at hu
  have hunion : ({q', r'} : Finset V) ∪ {s'} = {q', r', s'} := by
    ext x; simp [or_comm, or_left_comm, or_assoc]
  rw [← hunion, hu]

/-- Orient a neighbor in a 2-set as the second label. -/
lemma orient_second {D : Finset V} (hD : D.card = 2) {c d : V}
    (hd : d ∈ D) (hAdj : G.Adj c d) :
    ∃ d0 d1, D = {d0, d1} ∧ d0 ≠ d1 ∧ G.Adj c d1 := by
  obtain ⟨e0, e1, he01, hDeq⟩ := (card_eq_two (s := D)).1 hD
  have hd' : d = e0 ∨ d = e1 := by rw [hDeq] at hd; simpa using hd
  rcases hd' with heq | heq
  · refine ⟨e1, e0, ?_, he01.symm, heq ▸ hAdj⟩
    rw [hDeq]; subst heq; ext x; simp [or_comm]
  · exact ⟨e0, e1, hDeq, he01, heq ▸ hAdj⟩

/-- **Proposition 4.6**: star core with both links non-WKE ⇒ reducible. -/
theorem star_core_reducible (H : HubConfig G)
    (hnotu : ¬ IsWKE (linkGraph G H.u)) (hnotv : ¬ IsWKE (linkGraph G H.v))
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hstar : G.Adj p q ∧ G.Adj p r ∧ G.Adj p s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  have hA2 := star_two_leaf_attachments G H p q r s hC hstar honly hnotu
  let Hs := H.swap
  have honlys : ∀ x ∈ Hs.C, ∀ y ∈ Hs.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s) := by
    intro x hx y hy hAdj
    exact honly x (by change x ∈ H.C at hx; exact hx)
      y (by change y ∈ H.C at hy; exact hy) hAdj
  have hB2raw := star_two_leaf_attachments G Hs p q r s (by change H.C = _; exact hC)
    hstar honlys hnotv
  have hB2 : 2 ≤ (H.attachSupport H.B ∩ ({q, r, s} : Finset V)).card := by
    have heq : Hs.attachSupport Hs.A ∩ ({q, r, s} : Finset V) =
        H.attachSupport H.B ∩ {q, r, s} := by
      have hCs : Hs.C = H.C := rfl
      have hAs : Hs.A = H.B := rfl
      simp only [HubConfig.attachSupport, hCs, hAs]
    rwa [← heq]
  have hApos : (H.attachSupport H.A ∩ {q, r, s}).Nonempty :=
    card_pos.1 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hA2)
  obtain ⟨qA, hqA⟩ := hApos
  have hqA_leaf : qA ∈ ({q, r, s} : Finset V) := (mem_inter.1 hqA).2
  have hqA_att : (G.neighborFinset qA ∩ H.A).Nonempty :=
    (mem_filter.1 (mem_inter.1 hqA).1).2
  have exists_rB : ∃ rB ∈ ({q, r, s} : Finset V),
      rB ≠ qA ∧ (G.neighborFinset rB ∩ H.B).Nonempty := by
    by_contra h; push Not at h
    have hsub : H.attachSupport H.B ∩ {q, r, s} ⊆ ({qA} : Finset V) := by
      intro x hx
      have hxL : x ∈ ({q, r, s} : Finset V) := (mem_inter.1 hx).2
      have hxA : (G.neighborFinset x ∩ H.B).Nonempty :=
        (mem_filter.1 (mem_inter.1 hx).1).2
      have hxeq : x = qA := by
        by_contra hne
        have hempty : G.neighborFinset x ∩ H.B = ∅ := h x hxL hne
        exact Finset.nonempty_iff_ne_empty.1 hxA hempty
      simpa [hxeq]
    have : (H.attachSupport H.B ∩ {q, r, s}).card ≤ 1 :=
      (card_le_card hsub).trans (by simp)
    omega
  obtain ⟨rB, hrB_leaf, hrB_ne, hrB_att⟩ := exists_rB
  have hcard3 : ({q, r, s} : Finset V).card = 3 := by
    have d := core4_distinct G H hC
    simp [card_insert_of_notMem, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2]
  obtain ⟨sB, hsBeq⟩ := third_of_three hcard3 hqA_leaf hrB_leaf hrB_ne.symm
  -- Core equality after leaf relabelling
  have hC' : H.C = {p, qA, rB, sB} := by
    have d := core4_distinct G H hC
    have hu : ({p, q, r, s} : Finset V) = insert p ({q, r, s} : Finset V) := by
      ext x; simp [or_comm, or_left_comm, or_assoc]
    have hv : ({p, qA, rB, sB} : Finset V) = insert p ({qA, rB, sB} : Finset V) := by
      ext x; simp [or_comm, or_left_comm, or_assoc]
    rw [hC, hu, ← hsBeq, ← hv]
  have hp_on (x : V) (hx : x ∈ ({q, r, s} : Finset V)) : G.Adj p x := by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hstar.1
    · exact hstar.2.1
    · exact hstar.2.2
  have hsB_leaf : sB ∈ ({q, r, s} : Finset V) := by
    have : sB ∈ ({qA, rB, sB} : Finset V) := by simp
    rwa [hsBeq] at this
  have hstar' : G.Adj p qA ∧ G.Adj p rB ∧ G.Adj p sB :=
    ⟨hp_on qA hqA_leaf, hp_on rB hrB_leaf, hp_on sB hsB_leaf⟩
  -- honly for new labels: any core edge equals one of the three star edges from p
  have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, qA) ∨ s(x, y) = s(p, rB) ∨ s(x, y) = s(p, sB) := by
    intro x hx y hy hAdj
    -- Original honly: edge is one of pq, pr, ps
    rcases honly x hx y hy hAdj with h | h | h
    · -- = s(p,q). The non-p endpoint is q, which equals qA, rB, or sB
      have : q = qA ∨ q = rB ∨ q = sB := by
        have hq : q ∈ ({qA, rB, sB} : Finset V) := by
          have : q ∈ ({q, r, s} : Finset V) := by simp
          rwa [← hsBeq] at this
        simpa using hq
      rcases this with rfl | rfl | rfl <;> simp [h, Sym2.eq_swap]
    · have : r = qA ∨ r = rB ∨ r = sB := by
        have hr : r ∈ ({qA, rB, sB} : Finset V) := by
          have : r ∈ ({q, r, s} : Finset V) := by simp
          rwa [← hsBeq] at this
        simpa using hr
      rcases this with rfl | rfl | rfl <;> simp [h, Sym2.eq_swap]
    · have : s = qA ∨ s = rB ∨ s = sB := by
        have hs : s ∈ ({qA, rB, sB} : Finset V) := by
          have : s ∈ ({q, r, s} : Finset V) := by simp
          rwa [← hsBeq] at this
        simpa using hs
      rcases this with rfl | rfl | rfl <;> simp [h, Sym2.eq_swap]
  -- Orient A/B neighbors
  obtain ⟨da, ha⟩ := hqA_att
  have haA : da ∈ H.A := (mem_inter.1 ha).2
  have hAdjA : G.Adj qA da := (G.mem_neighborFinset _ _).1 (mem_inter.1 ha).1
  obtain ⟨a0, a1, hAeq, ha01, hqa⟩ := orient_second (G := G) (D := H.A) H.hA haA hAdjA
  obtain ⟨db, hb⟩ := hrB_att
  have hbB : db ∈ H.B := (mem_inter.1 hb).2
  have hAdjB : G.Adj rB db := (G.mem_neighborFinset _ _).1 (mem_inter.1 hb).1
  obtain ⟨b0, b1, hBeq, hb01, hrb⟩ := orient_second (G := G) (D := H.B) H.hB hbB hAdjB
  have h10 : ({H.u, H.v, p, qA, rB, sB, a0, a1, b0, b1} : Finset V).card = 10 := by
    have hC4 : ({p, qA, rB, sB} : Finset V).card = 4 := by rw [← hC']; exact H.hCcard
    exact labels10_of_hub G H hC' hAeq hBeq hC4 ha01 hb01
  exact star_core_of_labels G H p qA rB sB a0 a1 b0 b1 hC' hAeq hBeq hstar'
    honly' ⟨hqa, hrb⟩ h10

/-- Labelled P₄ with `pa`, `rb` → Lemma 4.8. -/
theorem path4_core_reducible (H : HubConfig G)
    (p q r s a0 a1 b0 b1 : V)
    (hC : H.C = {p, q, r, s})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hedges : G.Adj p q ∧ G.Adj q r ∧ G.Adj r s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(q, r) ∨ s(x, y) = s(r, s))
    (hatt : G.Adj p a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) :=
  lemma48_certificate G H p q r s a0 a1 b0 b1 hC hA hB hedges.1 hedges.2.1 hedges.2.2
    honly hatt h10

/-- **Proposition 4.7** (crossed case): path with distinct A/B leaf attachments. -/
theorem path_core_reducible_of_cross (H : HubConfig G)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hedges : G.Adj p q ∧ G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (a0 a1 b0 b1 : V) (hA : H.A = {a0, a1}) (hB : H.B = {b0, b1})
    (hatt : G.Adj q a1 ∧ G.Adj r b1)
    (h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) ∨ s(x, y) = s(p, s) := by
    intro x hx y hy hAdj
    rcases honly x hx y hy hAdj with h | h <;> simp [h]
  exact lemma45_reducible G H p q r s a0 a1 b0 b1 hC hA hB hedges.1 hedges.2
    honly' hatt h10

/-- Both private vertices attach to the path center when the other leaf has no private. -/
lemma path_p_adj_both_of_empty_leaf (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hedges : G.Adj p q ∧ G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (hre : G.neighborFinset r ∩ H.A = ∅) :
    (G.neighborFinset p ∩ H.A).card = 2 := by
  classical
  obtain ⟨d0, d1, hAeq, hd01, _, _⟩ := privates_of G H
  have hboth : G.Adj p d0 ∧ G.Adj p d1 := by
    by_contra h
    by_cases h0 : G.Adj p d0
    · have h1 : ¬ G.Adj p d1 := fun h1 => h ⟨h0, h1⟩
      exact path_center_both_privates G H hconn hnot p q r s hC hedges honly
        d0 d1 hAeq hd01 hre h1
    · have hAeq' : H.A = {d1, d0} := by rw [hAeq]; ext x; simp [or_comm]
      exact path_center_both_privates G H hconn hnot p q r s hC hedges honly
        d1 d0 hAeq' hd01.symm hre h0
  have hsub : ({d0, d1} : Finset V) ⊆ G.neighborFinset p ∩ H.A := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hboth.1, by rw [hAeq]; simp⟩
    · exact mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hboth.2, by rw [hAeq]; simp⟩
  have hle : 2 ≤ (G.neighborFinset p ∩ H.A).card := by
    have : ({d0, d1} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp [hd01]), card_singleton]
    exact this ▸ card_le_card hsub
  have hge : (G.neighborFinset p ∩ H.A).card ≤ 2 :=
    (card_le_card (inter_subset_right (s₁ := G.neighborFinset p) (s₂ := H.A))).trans
      (by rw [H.hA])
  omega

/-- **Proposition 4.7**: path core `P₃∪K₁` under (A1) and (A2) at the center. -/
theorem path_core_reducible (H : HubConfig G) (hA1 : H.A1)
    (p q r s : V) (hC : H.C = {p, q, r, s})
    (hedges : G.Adj p q ∧ G.Adj p r)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r))
    (hA2p : H.coreDeg p + (G.neighborFinset p ∩ H.A).card +
      (G.neighborFinset p ∩ H.B).card ≤ 5) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  have hLA := path_leaf_attachment G H hA1.1 hA1.2.1 p q r s hC hedges honly
  let Hs := H.swap
  have hCs : Hs.C = H.C := rfl
  have hAs : Hs.A = H.B := rfl
  have honlys : ∀ x ∈ Hs.C, ∀ y ∈ Hs.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(p, r) := by
    intro x hx y hy hAdj
    rw [hCs] at hx hy
    exact honly x hx y hy hAdj
  have hLB := path_leaf_attachment G Hs hA1.2.2.1 hA1.2.2.2 p q r s
    (hCs.trans hC) hedges honlys
  have hLB' : (G.neighborFinset q ∩ H.B).Nonempty ∨
      (G.neighborFinset r ∩ H.B).Nonempty := by
    rw [← hAs]; exact hLB
  by_cases hqArB : (G.neighborFinset q ∩ H.A).Nonempty ∧
      (G.neighborFinset r ∩ H.B).Nonempty
  · obtain ⟨hqA, hrB⟩ := hqArB
    obtain ⟨da, ha⟩ := hqA
    obtain ⟨db, hb⟩ := hrB
    have haA : da ∈ H.A := (mem_inter.1 ha).2
    have hbB : db ∈ H.B := (mem_inter.1 hb).2
    have hAdjA : G.Adj q da := (G.mem_neighborFinset _ _).1 (mem_inter.1 ha).1
    have hAdjB : G.Adj r db := (G.mem_neighborFinset _ _).1 (mem_inter.1 hb).1
    obtain ⟨a0, a1, hAeq, ha01, hqa⟩ :=
      orient_second (G := G) (D := H.A) H.hA haA hAdjA
    obtain ⟨b0, b1, hBeq, hb01, hrb⟩ :=
      orient_second (G := G) (D := H.B) H.hB hbB hAdjB
    have h10 : ({H.u, H.v, p, q, r, s, a0, a1, b0, b1} : Finset V).card = 10 := by
      have hC4 : ({p, q, r, s} : Finset V).card = 4 := by rw [← hC]; exact H.hCcard
      exact labels10_of_hub G H hC hAeq hBeq hC4 ha01 hb01
    exact path_core_reducible_of_cross G H p q r s hC hedges honly
      a0 a1 b0 b1 hAeq hBeq ⟨hqa, hrb⟩ h10
  by_cases hrAqB : (G.neighborFinset r ∩ H.A).Nonempty ∧
      (G.neighborFinset q ∩ H.B).Nonempty
  · obtain ⟨hrA, hqB⟩ := hrAqB
    obtain ⟨da, ha⟩ := hrA
    obtain ⟨db, hb⟩ := hqB
    have haA : da ∈ H.A := (mem_inter.1 ha).2
    have hbB : db ∈ H.B := (mem_inter.1 hb).2
    have hAdjA : G.Adj r da := (G.mem_neighborFinset _ _).1 (mem_inter.1 ha).1
    have hAdjB : G.Adj q db := (G.mem_neighborFinset _ _).1 (mem_inter.1 hb).1
    obtain ⟨a0, a1, hAeq, ha01, hra⟩ :=
      orient_second (G := G) (D := H.A) H.hA haA hAdjA
    obtain ⟨b0, b1, hBeq, hb01, hqb⟩ :=
      orient_second (G := G) (D := H.B) H.hB hbB hAdjB
    have hC' : H.C = {p, r, q, s} := by rw [hC]; ext x; simp [or_comm, or_left_comm]
    have hedges' : G.Adj p r ∧ G.Adj p q := ⟨hedges.2, hedges.1⟩
    have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, r) ∨ s(x, y) = s(p, q) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with h | h <;> simp [h, or_comm]
    have h10 : ({H.u, H.v, p, r, q, s, a0, a1, b0, b1} : Finset V).card = 10 := by
      have hC4 : ({p, r, q, s} : Finset V).card = 4 := by rw [← hC']; exact H.hCcard
      exact labels10_of_hub G H hC' hAeq hBeq hC4 ha01 hb01
    exact path_core_reducible_of_cross G H p r q s hC' hedges' honly'
      a0 a1 b0 b1 hAeq hBeq ⟨hra, hqb⟩ h10
  -- Same-singleton: neither crossed pair holds
  have hqAe_of : (G.neighborFinset q ∩ H.A).Nonempty →
      G.neighborFinset r ∩ H.B = ∅ := by
    intro hqA; by_contra hne
    exact hqArB ⟨hqA, Finset.nonempty_iff_ne_empty.2 hne⟩
  have hrAe_of : (G.neighborFinset r ∩ H.A).Nonempty →
      G.neighborFinset q ∩ H.B = ∅ := by
    intro hrA; by_contra hne
    exact hrAqB ⟨hrA, Finset.nonempty_iff_ne_empty.2 hne⟩
  have hpC : p ∈ H.C := by rw [hC]; simp
  have hdist := core4_distinct G H hC
  have hcoreDeg : H.coreDeg p = 2 := by
    unfold HubConfig.coreDeg
    have heq : (H.C.erase p).filter (G.Adj p) = ({q, r} : Finset V) := by
      ext x
      simp only [mem_filter, mem_erase, mem_insert, mem_singleton]
      constructor
      · intro ⟨⟨hne, hxC⟩, hAdj⟩
        have hx : x ∈ ({p, q, r, s} : Finset V) := by rw [← hC]; exact hxC
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with hxp | hxq | hxr | hxs
        · exact absurd hxp hne
        · exact Or.inl hxq
        · exact Or.inr hxr
        · -- ¬Adj p s under path-only edges
          have hsC : s ∈ H.C := by rw [hC]; simp
          have hAdj' : G.Adj p s := by rwa [hxs] at hAdj
          rcases honly p hpC s hsC hAdj' with hpq | hpr
          · have : s = q := by
              have hs : s ∈ ({p, q} : Finset V) := by
                have : s ∈ s(p, q).toFinset := by
                  simpa [← hpq, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p q
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at hs
              rcases hs with h' | h'
              · exact (hdist.2.2.1 h'.symm).elim
              · exact h'
            exact (hdist.2.2.2.2.1 this.symm).elim
          · have : s = r := by
              have hs : s ∈ ({p, r} : Finset V) := by
                have : s ∈ s(p, r).toFinset := by
                  simpa [← hpr, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right p r
                simpa [Sym2.toFinset_mk_eq] using this
              simp only [mem_insert, mem_singleton] at hs
              rcases hs with h' | h'
              · exact (hdist.2.2.1 h'.symm).elim
              · exact h'
            exact (hdist.2.2.2.2.2 this.symm).elim
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨⟨hdist.1.symm, by rw [hC]; simp⟩, hedges.1⟩
        · exact ⟨⟨hdist.2.1.symm, by rw [hC]; simp⟩, hedges.2⟩
    rw [heq, card_insert_of_notMem (by simp [hdist.2.2.2.1]), card_singleton]
  -- Dichotomy of same singleton
  rcases hLA with hqA | hrA
  · -- attachments include q on A-side; ¬crossed ⇒ ¬rB; with hLB' get qB and ¬rA
    have hrBe : G.neighborFinset r ∩ H.B = ∅ := hqAe_of hqA
    have hqB : (G.neighborFinset q ∩ H.B).Nonempty := by
      rcases hLB' with hqB | hrB
      · exact hqB
      · exact False.elim (Finset.nonempty_iff_ne_empty.1 hrB hrBe)
    have hrAe : G.neighborFinset r ∩ H.A = ∅ := by
      by_contra hne
      have hrA' : (G.neighborFinset r ∩ H.A).Nonempty :=
        Finset.nonempty_iff_ne_empty.2 hne
      have hqBe : G.neighborFinset q ∩ H.B = ∅ := hrAe_of hrA'
      exact Finset.nonempty_iff_ne_empty.1 hqB hqBe
    have hA2card := path_p_adj_both_of_empty_leaf G H hA1.1 hA1.2.1 p q r s hC hedges honly hrAe
    have hrBe' : G.neighborFinset r ∩ Hs.A = ∅ := by rw [hAs]; exact hrBe
    have hB2card := path_p_adj_both_of_empty_leaf G Hs hA1.2.2.1 hA1.2.2.2 p q r s
      (hCs.trans hC) hedges honlys hrBe'
    have hB2card' : (G.neighborFinset p ∩ H.B).card = 2 := by
      rw [← hAs]; exact hB2card
    have : H.coreDeg p + (G.neighborFinset p ∩ H.A).card +
        (G.neighborFinset p ∩ H.B).card = 6 := by
      rw [hcoreDeg, hA2card, hB2card']
    omega
  · -- attachments include r on A-side; symmetric
    have hqBe : G.neighborFinset q ∩ H.B = ∅ := hrAe_of hrA
    have hrB : (G.neighborFinset r ∩ H.B).Nonempty := by
      rcases hLB' with hqB | hrB
      · exact False.elim (Finset.nonempty_iff_ne_empty.1 hqB hqBe)
      · exact hrB
    have hqAe : G.neighborFinset q ∩ H.A = ∅ := by
      by_contra hne
      have hqA' : (G.neighborFinset q ∩ H.A).Nonempty :=
        Finset.nonempty_iff_ne_empty.2 hne
      have hrBe : G.neighborFinset r ∩ H.B = ∅ := hqAe_of hqA'
      exact Finset.nonempty_iff_ne_empty.1 hrB hrBe
    have hedges' : G.Adj p r ∧ G.Adj p q := ⟨hedges.2, hedges.1⟩
    have hC' : H.C = {p, r, q, s} := by rw [hC]; ext x; simp [or_comm, or_left_comm]
    have honly' : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
        s(x, y) = s(p, r) ∨ s(x, y) = s(p, q) := by
      intro x hx y hy hAdj
      rcases honly x hx y hy hAdj with h | h <;> simp [h, or_comm]
    have honlys' : ∀ x ∈ Hs.C, ∀ y ∈ Hs.C, G.Adj x y →
        s(x, y) = s(p, r) ∨ s(x, y) = s(p, q) := by
      intro x hx y hy hAdj
      rw [hCs] at hx hy
      exact honly' x hx y hy hAdj
    have hA2card := path_p_adj_both_of_empty_leaf G H hA1.1 hA1.2.1 p r q s hC' hedges' honly' hqAe
    have hqBe' : G.neighborFinset q ∩ Hs.A = ∅ := by rw [hAs]; exact hqBe
    have hB2card := path_p_adj_both_of_empty_leaf G Hs hA1.2.2.1 hA1.2.2.2 p r q s
      (hCs.trans hC') hedges' honlys' hqBe'
    have hB2card' : (G.neighborFinset p ∩ H.B).card = 2 := by
      rw [← hAs]; exact hB2card
    have : H.coreDeg p + (G.neighborFinset p ∩ H.A).card +
        (G.neighborFinset p ∩ H.B).card = 6 := by
      rw [hcoreDeg, hA2card, hB2card']
    omega

/-! ## Lemma 3.2 and Proposition 4.9 -/

lemma wke3 (F : SimpleGraph V) [DecidableRel F.Adj] {a b c d e f q1 q2 q3 : V}
    (h1 : F.Adj a b) (h2 : F.Adj c d) (h3 : F.Adj e f)
    (hnd : [a, b, c, d, e, f].Nodup)
    (hout : ∀ g ∈ F.edgeFinset, (∀ x ∈ g, x ∉ ({q1, q2, q3} : Finset V)) →
      g = s(a, b) ∨ g = s(c, d) ∨ g = s(e, f)) : IsWKE F := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩ := hnd
  refine isWKE_of_witness _ (M := {s(a, b), s(c, d), s(e, f)}) (Q := {q1, q2, q3})
    ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [mem_insert, mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> simpa
  · intro g hg g' hg' hne
    simp only [mem_insert, mem_singleton] at hg hg'
    rcases hg with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | (rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
         simp only [Finset.disjoint_left, mem_insert, mem_singleton]
         rintro x (rfl | rfl) (rfl | rfl) <;> simp_all)
  · have hM : ({s(a, b), s(c, d), s(e, f)} : Finset (Sym2 V)).card = 3 := by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [Sym2.eq_iff, hce, hcf, hde, hdf]
      · simp [Sym2.eq_iff, hac, had, hae, haf]
    rw [hM]; exact card_le_three
  · intro g hg hx
    rcases hout g hg hx with h | h | h <;> simp [h]

/-- In a connected link, every non-hub vertex `d ≠ w` has a link neighbour. -/
lemma link_nbr (hub : V) (hconn : LinkConnected G hub) {d w : V} (hdw : d ≠ w)
    (hd : d ∈ G.neighborFinset hub) (hw : w ∈ G.neighborFinset hub) :
    ∃ x, (linkGraph G hub).Adj d x := by
  by_contra h
  push Not at h
  have hdeg0 : (linkGraph G hub).degree d = 0 := by
    simp only [← card_neighborFinset_eq_degree]
    refine card_eq_zero.2 (eq_empty_iff_forall_notMem.2 ?_)
    intro x hx
    exact h x ((mem_neighborFinset _ _ _).1 hx)
  exact (not_reachable_of_left_degree_zero hdw hdeg0) (hconn d hd w hw)


/-- Outside `{z,x,y}` only `cd` and the private edge can occur (Lemma 3.2 setup). -/
lemma lemma32_outside (H : HubConfig G) {x y c d d0 d1 : V}
    (hC' : H.C = {x, y, c, d}) (hAeq : H.A = {d0, d1})
    (hnc : ∀ t ∈ H.A, ¬ G.Adj c t) (hnd : ∀ t ∈ H.A, ¬ G.Adj d t)
    {g : Sym2 V} (hg : g ∈ (linkGraph G H.u).edgeFinset)
    (hO : ∀ w ∈ g, w ∉ ({H.v, x, y} : Finset V)) :
    g = s(c, d) ∨ g = s(d0, d1) := by
  revert hg hO
  refine Sym2.inductionOn g fun a b hg hO => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 hg
  have hG : G.Adj a b := hab.2.2
  have cls (w : V) (hw : w ∈ G.neighborFinset H.u) (hwO : w ∉ ({H.v, x, y} : Finset V)) :
      w = c ∨ w = d ∨ w = d0 ∨ w = d1 := by
    rw [H.hNu] at hw
    simp only [mem_insert, mem_union, mem_singleton, not_or] at hw hwO
    rcases hw with h | h | h
    · exact absurd h hwO.1
    · rw [hC'] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h | h | h
      · exact absurd h hwO.2.1
      · exact absurd h hwO.2.2
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [hAeq] at h; simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have h0A : d0 ∈ H.A := by rw [hAeq]; simp
  have h1A : d1 ∈ H.A := by rw [hAeq]; simp
  rcases cls a hab.1 (hO a (by simp)) with rfl | rfl | rfl | rfl <;>
  rcases cls b hab.2.1 (hO b (by simp)) with rfl | rfl | rfl | rfl <;>
  first
  | exact (G.irrefl hG).elim
  | exact Or.inl rfl
  | exact Or.inl Sym2.eq_swap
  | exact Or.inr rfl
  | exact Or.inr Sym2.eq_swap
  | exact (hnc _ h0A hG).elim
  | exact (hnc _ h1A hG).elim
  | exact (hnd _ h0A hG).elim
  | exact (hnd _ h1A hG).elim
  | exact (hnc _ h0A hG.symm).elim
  | exact (hnc _ h1A hG.symm).elim
  | exact (hnd _ h0A hG.symm).elim
  | exact (hnd _ h1A hG.symm).elim

/-- **Lemma 3.2**: if the core has a perfect matching `{m0m1, m2m3}` and the link is
connected and not WKE, then no two core vertices `c, d` both lack private neighbours. -/
theorem lemma32 (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    {m0 m1 m2 m3 : V} (hC : H.C = {m0, m1, m2, m3})
    (hm01 : G.Adj m0 m1) (hm23 : G.Adj m2 m3)
    {x y c d : V} (hC' : H.C = {x, y, c, d})
    (hnc : ∀ t ∈ H.A, ¬ G.Adj c t) (hnd : ∀ t ∈ H.A, ¬ G.Adj d t) : False := by
  classical
  obtain ⟨d0, d1, hAeq, h01, hd0N, hd1N⟩ := privates_of G H
  have h0A : d0 ∈ H.A := by rw [hAeq]; simp
  have h1A : d1 ∈ H.A := by rw [hAeq]; simp
  have memC (w : V) (hw : w ∈ ({x, y, c, d} : Finset V)) : w ∈ H.C := hC' ▸ hw
  have memC' (w : V) (hw : w ∈ ({m0, m1, m2, m3} : Finset V)) : w ∈ H.C := hC ▸ hw
  have hxC := memC x (by simp)
  have hyC := memC y (by simp)
  have hcC := memC c (by simp)
  have hdC := memC d (by simp)
  have hm0C := memC' m0 (by simp)
  have hm1C := memC' m1 (by simp)
  have hm2C := memC' m2 (by simp)
  have hm3C := memC' m3 (by simp)
  obtain ⟨hxy, hxc, hxd, hyc, hyd, hcd'⟩ := core4_distinct G H hC'
  obtain ⟨m01, m02, m03, m12, m13, m23⟩ := core4_distinct G H hC
  have zx := ne_z_of_core G H hxC
  have zy := ne_z_of_core G H hyC
  have zc := ne_z_of_core G H hcC
  have zd := ne_z_of_core G H hdC
  have zm0 := ne_z_of_core G H hm0C
  have zm1 := ne_z_of_core G H hm1C
  have zm2 := ne_z_of_core G H hm2C
  have zm3 := ne_z_of_core G H hm3C
  have z0 := ne_z_of_priv G H h0A
  have z1 := ne_z_of_priv G H h1A
  have x0 := ne_core_priv G H hxC h0A
  have x1 := ne_core_priv G H hxC h1A
  have y0 := ne_core_priv G H hyC h0A
  have y1 := ne_core_priv G H hyC h1A
  have c0 := ne_core_priv G H hcC h0A
  have c1 := ne_core_priv G H hcC h1A
  have e0 := ne_core_priv G H hdC h0A
  have e1 := ne_core_priv G H hdC h1A
  have m00 := ne_core_priv G H hm0C h0A
  have m01' := ne_core_priv G H hm0C h1A
  have m10 := ne_core_priv G H hm1C h0A
  have m11 := ne_core_priv G H hm1C h1A
  have m20 := ne_core_priv G H hm2C h0A
  have m21 := ne_core_priv G H hm2C h1A
  have m30 := ne_core_priv G H hm3C h0A
  have m31 := ne_core_priv G H hm3C h1A
  have hzN := opposite_hub_mem G H
  have L {a b : V} (ha : a ∈ G.neighborFinset H.u) (hb : b ∈ G.neighborFinset H.u)
      (h : G.Adj a b) : (linkGraph G H.u).Adj a b := ⟨ha, hb, h⟩
  have NC (w : V) (hw : w ∈ H.C) : w ∈ G.neighborFinset H.u := core_mem_Nu G H hw
  have zA (w : V) (hw : w ∈ H.C) : G.Adj H.v w := z_adj_core G H hw
  have hout := fun {g : Sym2 V} hg hO =>
    lemma32_outside G H hC' hAeq hnc hnd (g := g) hg hO
  have edgeG {a b : V} (hg : s(a, b) ∈ (linkGraph G H.u).edgeFinset) : G.Adj a b :=
    ((mem_edgeFinset (G := linkGraph G H.u)).1 hg).2.2
  -- a private neighbour of d0 inside the core
  obtain ⟨w, hw⟩ := link_nbr G H.u hconn (w := H.v) z0.symm (by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ (by rw [hAeq]; simp))) (opposite_hub_mem G H)
  have hwG : G.Adj d0 w := hw.2.2
  by_cases hdd : G.Adj d0 d1
  · by_cases hcd : G.Adj c d
    · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
        (L (NC c hcC) (NC d hdC) hcd) (L hd0N hd1N hdd) (L hzN (NC x hxC) (zA x hxC))
        (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
        (fun g hg hO => by
          rcases hout hg hO with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)))
    · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
        (L (NC m0 hm0C) (NC m1 hm1C) hm01) (L (NC m2 hm2C) (NC m3 hm3C) hm23)
        (L hd0N hd1N hdd)
        (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
        (fun g hg hO => by
          rcases hout hg hO with h | h
          · subst h; exact (hcd (edgeG hg)).elim
          · exact Or.inr (Or.inr h)))
  · -- d0's neighbour lies in the core, at x or y
    have hwN : w ∈ G.neighborFinset H.u := hw.2.1
    rw [H.hNu] at hwN
    simp only [mem_insert, mem_union] at hwN
    rcases hwN with hwz | hwC | hwA
    · exact (not_adj_hub_priv G H h0A (hwz ▸ hwG).symm).elim
    · have hwC' := hwC
      rw [hC'] at hwC'
      simp only [mem_insert, mem_singleton] at hwC'
      by_cases hcd : G.Adj c d
      · rcases hwC' with h | h | h | h
        · rw [h] at hwG
          exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L (NC c hcC) (NC d hdC) hcd) (L hd0N (NC x hxC) hwG)
            (L hzN (NC y hyC) (zA y hyC))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => by
              rcases hout hg hO with h | h
              · exact Or.inl h
              · subst h; exact (hdd (edgeG hg)).elim))
        · rw [h] at hwG
          exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L (NC c hcC) (NC d hdC) hcd) (L hd0N (NC y hyC) hwG)
            (L hzN (NC x hxC) (zA x hxC))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => by
              rcases hout hg hO with h | h
              · exact Or.inl h
              · subst h; exact (hdd (edgeG hg)).elim))
        · exact (hnc d0 h0A (h ▸ hwG.symm)).elim
        · exact (hnd d0 h0A (h ▸ hwG.symm)).elim
      · -- neither cd nor d0d1: M = {d0 w, f, z t}
        have hwm : w = m0 ∨ w = m1 ∨ w = m2 ∨ w = m3 := by
          rw [hC] at hwC; simpa using hwC
        have fin : ∀ g ∈ (linkGraph G H.u).edgeFinset,
            (∀ v ∈ g, v ∉ ({H.v, x, y} : Finset V)) → False := fun g hg hO => by
          rcases hout hg hO with h | h
          · subst h; exact hcd (edgeG hg)
          · subst h; exact hdd (edgeG hg)
        rcases hwm with rfl | rfl | rfl | rfl
        · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L hd0N (NC w hwC) hwG) (L (NC m2 hm2C) (NC m3 hm3C) hm23)
            (L hzN (NC m1 hm1C) (zA m1 hm1C))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => (fin g hg hO).elim))
        · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L hd0N (NC w hwC) hwG) (L (NC m2 hm2C) (NC m3 hm3C) hm23)
            (L hzN (NC m0 hm0C) (zA m0 hm0C))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => (fin g hg hO).elim))
        · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L hd0N (NC w hwC) hwG) (L (NC m0 hm0C) (NC m1 hm1C) hm01)
            (L hzN (NC m3 hm3C) (zA m3 hm3C))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => (fin g hg hO).elim))
        · exact hnot (wke3 _ (q1 := H.v) (q2 := x) (q3 := y)
            (L hd0N (NC w hwC) hwG) (L (NC m0 hm0C) (NC m1 hm1C) hm01)
            (L hzN (NC m2 hm2C) (zA m2 hm2C))
            (by simp [List.nodup_cons, hxy, hxc, hxd, hyc, hyd, hcd', zx, zy, zc, zd, z0, z1, x0, x1, y0, y1, c0, c1, e0, e1, h01, m01, m02, m03, m12, m13, m23, zm0, zm1, zm2, zm3, m00, m01', m10, m11, m20, m21, m30, m31, hxy.symm, hxc.symm, hxd.symm, hyc.symm, hyd.symm, hcd'.symm, zx.symm, zy.symm, zc.symm, zd.symm, z0.symm, z1.symm, x0.symm, x1.symm, y0.symm, y1.symm, c0.symm, c1.symm, e0.symm, e1.symm, h01.symm, m01.symm, m02.symm, m03.symm, m12.symm, m13.symm, m23.symm, zm0.symm, zm1.symm, zm2.symm, zm3.symm, m00.symm, m01'.symm, m10.symm, m11.symm, m20.symm, m21.symm, m30.symm, m31.symm])
            (fun g hg hO => (fin g hg hO).elim))
    · have : w = d0 ∨ w = d1 := by rw [hAeq] at hwA; simpa using hwA
      rcases this with rfl | rfl
      · exact G.irrefl hwG
      · exact hdd hwG

/-- Lemma 4.8 after orienting the private pairs. -/
theorem p4_of_attach (H : HubConfig G) {p q r s : V} (hC : H.C = {p, q, r, s})
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(q, r) ∨ s(x, y) = s(r, s))
    (ha : ∃ t ∈ H.A, G.Adj p t) (hb : ∃ t ∈ H.B, G.Adj r t) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  obtain ⟨da, haA, hpa⟩ := ha
  obtain ⟨db, hbB, hrb⟩ := hb
  obtain ⟨a0, a1, hAeq, ha01, hpa1⟩ := orient_second (G := G) (D := H.A) H.hA haA hpa
  obtain ⟨b0, b1, hBeq, hb01, hrb1⟩ := orient_second (G := G) (D := H.B) H.hB hbB hrb
  have hC4 : ({p, q, r, s} : Finset V).card = 4 := by rw [← hC]; exact H.hCcard
  exact path4_core_reducible G H p q r s a0 a1 b0 b1 hC hAeq hBeq ⟨hpq, hqr, hrs⟩ honly
    ⟨hpa1, hrb1⟩ (labels10_of_hub G H hC hAeq hBeq hC4 ha01 hb01)


/-- Lemma 3.2 for the path `p-q-r-s` (matching `{pq, rs}`): at most one core vertex
misses the private side. -/
theorem p4_side (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    {p q r s : V} (hC : H.C = {p, q, r, s}) (hpq : G.Adj p q) (hrs : G.Adj r s) :
    let tA : V → Prop := fun c => ∃ t ∈ H.A, G.Adj c t
    ¬(¬ tA p ∧ ¬ tA q) ∧ ¬(¬ tA p ∧ ¬ tA r) ∧ ¬(¬ tA p ∧ ¬ tA s) ∧
    ¬(¬ tA q ∧ ¬ tA r) ∧ ¬(¬ tA q ∧ ¬ tA s) ∧ ¬(¬ tA r ∧ ¬ tA s) := by
  intro tA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := r) (y := s) hC hpq hrs
      (by rw [hC]; ext t; simp only [mem_insert, mem_singleton]; constructor <;> rintro (h|h|h|h) <;> simp [h])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := q) (y := s) hC hpq hrs
      (by rw [hC]; ext t; simp only [mem_insert, mem_singleton]; constructor <;> rintro (h|h|h|h) <;> simp [h])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := q) (y := r) hC hpq hrs
      (by rw [hC]; ext t; simp only [mem_insert, mem_singleton]; constructor <;> rintro (h|h|h|h) <;> simp [h])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := p) (y := s) hC hpq hrs
      (by rw [hC]; ext t; simp only [mem_insert, mem_singleton]; constructor <;> rintro (h|h|h|h) <;> simp [h])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := p) (y := r) hC hpq hrs
      (by rw [hC]; ext t; simp only [mem_insert, mem_singleton]; constructor <;> rintro (h|h|h|h) <;> simp [h])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)
  · rintro ⟨ha, hb⟩
    exact lemma32 G H hconn hnot (x := p) (y := q) hC hpq hrs
      (by rw [hC])
      (fun t ht h => ha ⟨t, ht, h⟩) (fun t ht h => hb ⟨t, ht, h⟩)

/-- **Proposition 4.9**: the four-vertex path core is reducible under (A1). -/
theorem p4_core_reducible (H : HubConfig G) (hA1 : H.A1) {p q r s : V}
    (hC : H.C = {p, q, r, s})
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (honly : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(p, q) ∨ s(x, y) = s(q, r) ∨ s(x, y) = s(r, s)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  let Hs := H.swap
  have hA1s : Hs.A1 := hA1.swap
  let tA : V → Prop := fun c => ∃ t ∈ H.A, G.Adj c t
  let tB : V → Prop := fun c => ∃ t ∈ H.B, G.Adj c t
  obtain ⟨nA_pq, nA_pr, nA_ps, nA_qr, nA_qs, nA_rs⟩ := p4_side G H hA1.1 hA1.2.1 hC hpq hrs
  obtain ⟨nB_pq, nB_pr, nB_ps, nB_qr, nB_qs, nB_rs⟩ :=
    p4_side G Hs hA1s.1 hA1s.2.1 (p := p) (q := q) (r := r) (s := s) hC hpq hrs
  have key : (tA p ∧ tB r) ∨ (tA r ∧ tB p) ∨ (tA q ∧ tB s) ∨ (tA s ∧ tB q) := by
    have nn {P : Prop} (h : ¬¬P) : P := Classical.not_not.1 h
    by_cases hp : tA p
    · by_cases hrB : tB r
      · exact Or.inl ⟨hp, hrB⟩
      have hpB : tB p := nn fun h => nB_pr ⟨h, hrB⟩
      have hsB : tB s := nn fun h => nB_rs ⟨hrB, h⟩
      by_cases hrA : tA r
      · exact Or.inr (Or.inl ⟨hrA, hpB⟩)
      have hqA : tA q := nn fun h => nA_qr ⟨h, hrA⟩
      exact Or.inr (Or.inr (Or.inl ⟨hqA, hsB⟩))
    · have hqA : tA q := nn fun h => nA_pq ⟨hp, h⟩
      have hsA : tA s := nn fun h => nA_ps ⟨hp, h⟩
      by_cases hsB : tB s
      · exact Or.inr (Or.inr (Or.inl ⟨hqA, hsB⟩))
      have hqB : tB q := nn fun h => nB_qs ⟨h, hsB⟩
      exact Or.inr (Or.inr (Or.inr ⟨hsA, hqB⟩))
  have hCr : H.C = {s, r, q, p} := by
    rw [hC]; ext t; simp only [mem_insert, mem_singleton]
    constructor <;> rintro (h|h|h|h) <;> simp [h]
  have honlyr : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(s, r) ∨ s(x, y) = s(r, q) ∨ s(x, y) = s(q, p) := by
    intro x hx y hy h
    rcases honly x hx y hy h with e | e | e
    · exact Or.inr (Or.inr (e.trans Sym2.eq_swap))
    · exact Or.inr (Or.inl (e.trans Sym2.eq_swap))
    · exact Or.inl (e.trans Sym2.eq_swap)
  have hswap : IsReducible G ({Hs.u, Hs.v} : Finset V) →
      IsReducible G ({H.u, H.v} : Finset V) := fun h => by
    have : ({Hs.u, Hs.v} : Finset V) = {H.u, H.v} := Finset.pair_comm _ _
    rwa [this] at h
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact p4_of_attach G H hC hpq hqr hrs honly ha hb
  · exact hswap (p4_of_attach G Hs hC hpq hqr hrs honly hb ha)
  · exact hswap (p4_of_attach G Hs hCr hrs.symm hqr.symm hpq.symm honlyr hb ha)
  · exact p4_of_attach G H hCr hrs.symm hqr.symm hpq.symm honlyr ha hb



/-! ## Complete core K₄ (Lemmas 5.1–5.2, Proposition 5.3) -/

/-- Outside `Q = C \ {c}` in a K₄ link: only `z c` and the private edge. -/
lemma k4_outside_Q (H : HubConfig G)
    (c x y w d0 d1 : V) (hC : H.C = {c, x, y, w}) (hAeq : H.A = {d0, d1})
    (hnc : ∀ t ∈ H.A, ¬ G.Adj c t)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ v ∈ e, v ∉ ({x, y, w} : Finset V)) :
    e = s(H.v, c) ∨ e = s(d0, d1) := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have cls (t : V) (htN : t ∈ G.neighborFinset H.u)
      (htO : t ∉ ({x, y, w} : Finset V)) :
      t = H.v ∨ t = c ∨ t = d0 ∨ t = d1 := by
    rw [H.hNu] at htN
    simp only [mem_insert, mem_union, mem_singleton, not_or] at htN htO
    rcases htN with rfl | hCmem | hAmem
    · exact Or.inl rfl
    · have : t ∈ ({c, x, y, w} : Finset V) := by rw [← hC]; exact hCmem
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl htO.1
      · exact absurd rfl htO.2.1
      · exact absurd rfl htO.2.2
    · have : t ∈ ({d0, d1} : Finset V) := by rw [← hAeq]; exact hAmem
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have ha := cls a hab.1 (hOut a (by simp))
  have hb := cls b hab.2.1 (hOut b (by simp))
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have hcC : c ∈ H.C := by rw [hC]; simp
  have not_zc_priv {d : V} (hd : d ∈ H.A) : ¬ G.Adj H.v d := not_adj_hub_priv G H hd
  have not_c_priv {d : V} (hd : d ∈ H.A) : ¬ G.Adj c d := hnc d hd
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inl (by rw [ha, hb])
  · exact False.elim (not_zc_priv hd0A (by rwa [ha, hb] at hG))
  · exact False.elim (not_zc_priv hd1A (by rwa [ha, hb] at hG))
  · exact Or.inl (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact False.elim (not_c_priv hd0A (by rwa [ha, hb] at hG))
  · exact False.elim (not_c_priv hd1A (by rwa [ha, hb] at hG))
  · exact False.elim (not_zc_priv hd0A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_c_priv hd0A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inr (by rw [ha, hb])
  · exact False.elim (not_zc_priv hd1A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_c_priv hd1A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact Or.inr (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))

/-- Lemma 5.1 (⇒): if some core vertex has no private neighbour, a K₄-link is WKE. -/
theorem lemma51_forward (H : HubConfig G)
    (hconn : LinkConnected G H.u)
    (c x y w : V) (hC : H.C = {c, x, y, w})
    (hK4 : G.Adj c x ∧ G.Adj c y ∧ G.Adj c w ∧ G.Adj x y ∧ G.Adj x w ∧ G.Adj y w)
    (hnc : ∀ t ∈ H.A, ¬ G.Adj c t) : IsWKE (linkGraph G H.u) := by
  classical
  obtain ⟨d0, d1, hAeq, hd01, hd0N, hd1N⟩ := privates_of G H
  obtain ⟨hcx, hcy, hcw, hxy, hxw, hyw⟩ := core4_distinct G H hC
  have hcC : c ∈ H.C := by rw [hC]; simp
  have hxC : x ∈ H.C := by rw [hC]; simp
  have hyC : y ∈ H.C := by rw [hC]; simp
  have hwC : w ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have hcN := core_mem_Nu G H hcC
  have hxN := core_mem_Nu G H hxC
  have hyN := core_mem_Nu G H hyC
  have hwN := core_mem_Nu G H hwC
  have hzc := z_adj_core G H hcC
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have zc := ne_z_of_core G H hcC
  have zx := ne_z_of_core G H hxC
  have zy := ne_z_of_core G H hyC
  have zw := ne_z_of_core G H hwC
  have z0 := ne_z_of_priv G H hd0A
  have z1 := ne_z_of_priv G H hd1A
  have c0 := ne_core_priv G H hcC hd0A
  have c1 := ne_core_priv G H hcC hd1A
  have x0 := ne_core_priv G H hxC hd0A
  have x1 := ne_core_priv G H hxC hd1A
  have y0 := ne_core_priv G H hyC hd0A
  have y1 := ne_core_priv G H hyC hd1A
  have w0 := ne_core_priv G H hwC hd0A
  have w1 := ne_core_priv G H hwC hd1A
  have L {a b : V} (ha : a ∈ G.neighborFinset H.u) (hb : b ∈ G.neighborFinset H.u)
      (h : G.Adj a b) : (linkGraph G H.u).Adj a b := ⟨ha, hb, h⟩
  have hout {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
      (hO : ∀ v ∈ e, v ∉ ({x, y, w} : Finset V)) :
      e = s(H.v, c) ∨ e = s(d0, d1) := k4_outside_Q G H c x y w d0 d1 hC hAeq hnc he hO
  by_cases hpriv : G.Adj d0 d1
  · refine wke3 (linkGraph G H.u) (q1 := x) (q2 := y) (q3 := w)
      (L hzN hcN hzc) (L hd0N hd1N hpriv) (L hxN hyN hK4.2.2.2.1)
      (by simp [List.nodup_cons, zc, z0, z1, zx, zy, zw, c0, c1, hcx, hcy, hcw,
            x0, x1, y0, y1, w0, w1, hxy, hxw, hyw, hd01,
            zc.symm, z0.symm, z1.symm, zx.symm, zy.symm, zw.symm,
            c0.symm, c1.symm, hcx.symm, hcy.symm, hcw.symm,
            x0.symm, x1.symm, y0.symm, y1.symm, w0.symm, w1.symm,
            hxy.symm, hxw.symm, hyw.symm, hd01.symm])
      (fun e he hO => by
        rcases hout he hO with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
  · obtain ⟨nbr, hnbr⟩ := link_nbr G H.u hconn (d := d0) (w := H.v) z0.symm (by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ (by rw [hAeq]; simp))) (opposite_hub_mem G H)
    have hG : G.Adj d0 nbr := hnbr.2.2
    have hnN : nbr ∈ G.neighborFinset H.u := hnbr.2.1
    rw [H.hNu] at hnN
    simp only [mem_insert, mem_union] at hnN
    have hx' : nbr = x ∨ nbr = y ∨ nbr = w := by
      rcases hnN with rfl | hCm | hAm
      · exact False.elim (not_adj_hub_priv G H hd0A hG.symm)
      · have : nbr ∈ ({c, x, y, w} : Finset V) := by rw [← hC]; exact hCm
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl | rfl
        · exact False.elim (hnc d0 hd0A hG.symm)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · have : nbr = d0 ∨ nbr = d1 := by rw [hAeq] at hAm; simpa using hAm
        rcases this with rfl | rfl
        · exact False.elim (G.irrefl hG)
        · exact False.elim (hpriv hG)
    have run (x' y' w' : V)
        (hx'C : x' ∈ H.C) (hy'C : y' ∈ H.C) (hw'C : w' ∈ H.C)
        (hatt : G.Adj d0 x') (hyw' : G.Adj y' w')
        (hQ : ({x, y, w} : Finset V) = {x', y', w'})
        (hne : [H.v, c, d0, x', y', w'].Nodup) :
        IsWKE (linkGraph G H.u) := by
      refine wke3 (linkGraph G H.u) (q1 := x') (q2 := y') (q3 := w')
        (L hzN hcN hzc) (L hd0N (core_mem_Nu G H hx'C) hatt)
        (L (core_mem_Nu G H hy'C) (core_mem_Nu G H hw'C) hyw') hne
        (fun e he hO => by
          have hO' : ∀ v ∈ e, v ∉ ({x, y, w} : Finset V) := by
            intro v hv; have := hO v hv; rwa [← hQ] at this
          rcases hout he hO' with h | h
          · exact Or.inl h
          · subst h
            exact False.elim (hpriv ((mem_edgeFinset (G := linkGraph G H.u)).1 he).2.2))
    rcases hx' with hnx | hny | hnw
    · exact run x y w hxC hyC hwC (hnx ▸ hG) hK4.2.2.2.2.2 rfl
        (by simp [List.nodup_cons, zc, z0, z1, zx, zy, zw, c0, c1, hcx, hcy, hcw,
            x0, x1, y0, y1, w0, w1, hxy, hxw, hyw, hd01,
            zc.symm, z0.symm, z1.symm, zx.symm, zy.symm, zw.symm,
            c0.symm, c1.symm, hcx.symm, hcy.symm, hcw.symm,
            x0.symm, x1.symm, y0.symm, y1.symm, w0.symm, w1.symm,
            hxy.symm, hxw.symm, hyw.symm, hd01.symm])
    · exact run y x w hyC hxC hwC (hny ▸ hG) hK4.2.2.2.2.1
        (by
          ext t; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h) <;> simp [h])
        (by simp [List.nodup_cons, zc, z0, z1, zx, zy, zw, c0, c1, hcx, hcy, hcw,
            x0, x1, y0, y1, w0, w1, hxy, hxw, hyw, hd01,
            zc.symm, z0.symm, z1.symm, zx.symm, zy.symm, zw.symm,
            c0.symm, c1.symm, hcx.symm, hcy.symm, hcw.symm,
            x0.symm, x1.symm, y0.symm, y1.symm, w0.symm, w1.symm,
            hxy.symm, hxw.symm, hyw.symm, hd01.symm])
    · exact run w x y hwC hxC hyC (hnw ▸ hG) hK4.2.2.2.1
        (by
          ext t; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h) <;> simp [h])
        (by simp [List.nodup_cons, zc, z0, z1, zx, zy, zw, c0, c1, hcx, hcy, hcw,
            x0, x1, y0, y1, w0, w1, hxy, hxw, hyw, hd01,
            zc.symm, z0.symm, z1.symm, zx.symm, zy.symm, zw.symm,
            c0.symm, c1.symm, hcx.symm, hcy.symm, hcw.symm,
            x0.symm, x1.symm, y0.symm, y1.symm, w0.symm, w1.symm,
            hxy.symm, hxw.symm, hyw.symm, hd01.symm])

/-- Lemma 5.1 (⇐ direction used by Prop 5.3): connected non-WKE K₄-link ⇒ full private support. -/
theorem lemma51 (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    (c0 c1 c2 c3 : V) (hC : H.C = {c0, c1, c2, c3})
    (hK4 : G.Adj c0 c1 ∧ G.Adj c0 c2 ∧ G.Adj c0 c3 ∧
      G.Adj c1 c2 ∧ G.Adj c1 c3 ∧ G.Adj c2 c3) :
    ∀ c ∈ H.C, (G.neighborFinset c ∩ H.A).Nonempty := by
  classical
  intro c hc
  by_contra hempty
  have hempty' : G.neighborFinset c ∩ H.A = ∅ :=
    Finset.not_nonempty_iff_eq_empty.1 hempty
  have hnc : ∀ t ∈ H.A, ¬ G.Adj c t := by
    intro t ht h
    have : t ∈ G.neighborFinset c ∩ H.A :=
      mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 h, ht⟩
    simpa [hempty'] using this
  -- Relabel so the empty vertex is first
  have : ∃ x y w, H.C = {c, x, y, w} ∧
      G.Adj c x ∧ G.Adj c y ∧ G.Adj c w ∧ G.Adj x y ∧ G.Adj x w ∧ G.Adj y w := by
    have hc' : c ∈ ({c0, c1, c2, c3} : Finset V) := by rw [← hC]; exact hc
    simp only [mem_insert, mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact ⟨c1, c2, c3, hC, hK4.1, hK4.2.1, hK4.2.2.1, hK4.2.2.2.1, hK4.2.2.2.2.1, hK4.2.2.2.2.2⟩
    · exact ⟨c0, c2, c3, by
        rw [hC]; ext t; simp only [mem_insert, mem_singleton]
        constructor <;> rintro (h | h | h | h) <;> simp [h],
        hK4.1.symm, hK4.2.2.2.1, hK4.2.2.2.2.1, hK4.2.1, hK4.2.2.1, hK4.2.2.2.2.2⟩
    · exact ⟨c0, c1, c3, by
        rw [hC]; ext t; simp only [mem_insert, mem_singleton]
        constructor <;> rintro (h | h | h | h) <;> simp [h],
        hK4.2.1.symm, hK4.2.2.2.1.symm, hK4.2.2.2.2.2, hK4.1, hK4.2.2.1, hK4.2.2.2.2.1⟩
    · exact ⟨c0, c1, c2, by
        rw [hC]; ext t; simp only [mem_insert, mem_singleton]
        constructor <;> rintro (h | h | h | h) <;> simp [h],
        hK4.2.2.1.symm, hK4.2.2.2.2.1.symm, hK4.2.2.2.2.2.symm, hK4.1, hK4.2.1, hK4.2.2.2.1⟩
  obtain ⟨x, y, w, hC', hedges⟩ := this
  exact hnot (lemma51_forward G H hconn c x y w hC' hedges hnc)


/-! ### Proposition 5.3 case (G): Fin-10 packing/cover (coversZ/external pending) -/

def packing10_53G : Finset (Finset (Fin 10)) :=
  {{2, 3, 4}, {0, 1, 2}, {0, 3, 5}, {1, 4, 5}, {0, 4, 6}, {1, 3, 8}}

def cover10_53G : Finset (Sym2 (Fin 10)) :=
  {s(2, 3), s(2, 4), s(3, 4), s(3, 5), s(4, 5), s(4, 6), s(3, 8),
   s(0, 1), s(0, 5), s(1, 5), s(0, 7), s(1, 9)}

lemma packing10_53G_card : packing10_53G.card = 6 := by native_decide
lemma cover10_53G_card : cover10_53G.card = 12 := by native_decide
lemma packing10_53G_pairwise :
    ∀ σ ∈ packing10_53G, ∀ τ ∈ packing10_53G, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- αz = aPlus (7), βy = b_ (8) -/
def packing10_53G_az : Finset (Finset (Fin 10)) :=
  {{2, 3, 4}, {0, 1, 2}, {0, 3, 5}, {1, 4, 5}, {0, 4, 7}, {1, 3, 8}}
def cover10_53G_az : Finset (Sym2 (Fin 10)) :=
  {s(2, 3), s(2, 4), s(3, 4), s(3, 5), s(4, 5), s(4, 7), s(3, 8),
   s(0, 1), s(0, 5), s(1, 5), s(0, 7), s(1, 9)}
/-- αz = a_ (6), βy = bPlus (9) -/
def packing10_53G_by : Finset (Finset (Fin 10)) :=
  {{2, 3, 4}, {0, 1, 2}, {0, 3, 5}, {1, 4, 5}, {0, 4, 6}, {1, 3, 9}}
def cover10_53G_by : Finset (Sym2 (Fin 10)) :=
  {s(2, 3), s(2, 4), s(3, 4), s(3, 5), s(4, 5), s(4, 6), s(3, 9),
   s(0, 1), s(0, 5), s(1, 5), s(0, 7), s(1, 9)}
/-- αz = aPlus, βy = bPlus -/
def packing10_53G_azby : Finset (Finset (Fin 10)) :=
  {{2, 3, 4}, {0, 1, 2}, {0, 3, 5}, {1, 4, 5}, {0, 4, 7}, {1, 3, 9}}
def cover10_53G_azby : Finset (Sym2 (Fin 10)) :=
  {s(2, 3), s(2, 4), s(3, 4), s(3, 5), s(4, 5), s(4, 7), s(3, 9),
   s(0, 1), s(0, 5), s(1, 5), s(0, 7), s(1, 9)}

lemma packing10_53G_az_card : packing10_53G_az.card = 6 := by native_decide
lemma packing10_53G_by_card : packing10_53G_by.card = 6 := by native_decide
lemma packing10_53G_azby_card : packing10_53G_azby.card = 6 := by native_decide
lemma cover10_53G_az_card : cover10_53G_az.card = 12 := by native_decide
lemma cover10_53G_by_card : cover10_53G_by.card = 12 := by native_decide
lemma cover10_53G_azby_card : cover10_53G_azby.card = 12 := by native_decide
lemma packing10_53G_az_pairwise :
    ∀ σ ∈ packing10_53G_az, ∀ τ ∈ packing10_53G_az, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide
lemma packing10_53G_by_pairwise :
    ∀ σ ∈ packing10_53G_by, ∀ τ ∈ packing10_53G_by, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide
lemma packing10_53G_azby_pairwise :
    ∀ σ ∈ packing10_53G_azby, ∀ τ ∈ packing10_53G_azby, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

def packing53G (u v x y z w αz βy : V) : Finset (Finset V) :=
  {{x, y, z}, {u, v, x}, {u, y, w}, {v, z, w}, {u, z, αz}, {v, y, βy}}

def cover53G (u v x y z w αz aPlus βy bPlus : V) : Finset (Sym2 V) :=
  {s(x, y), s(x, z), s(y, z), s(y, w), s(z, w), s(z, αz), s(y, βy),
   s(u, v), s(u, w), s(v, w), s(u, aPlus), s(v, bPlus)}

private lemma packing53G_image_eq (u v x y z w a_ aPlus b_ bPlus : V) :
    packing10_53G.image (mapTri (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      packing53G u v x y z w a_ b_ := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, _, f8, _⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have e1 : mapTri f {2, 3, 4} = ({x, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f2, f3, f4]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 5} = ({u, y, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e4 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  have e5 : mapTri f {0, 4, 6} = ({u, z, a_} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f6]
  have e6 : mapTri f {1, 3, 8} = ({v, y, b_} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  simp only [packing10_53G, packing53G, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma packing53G_image_eq_az (u v x y z w a_ aPlus b_ bPlus : V) :
    packing10_53G_az.image (mapTri (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      packing53G u v x y z w aPlus b_ := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, f8, _⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have e1 : mapTri f {2, 3, 4} = ({x, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f2, f3, f4]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 5} = ({u, y, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e4 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  have e5 : mapTri f {0, 4, 7} = ({u, z, aPlus} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f7]
  have e6 : mapTri f {1, 3, 8} = ({v, y, b_} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  simp only [packing10_53G_az, packing53G, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma packing53G_image_eq_by (u v x y z w a_ aPlus b_ bPlus : V) :
    packing10_53G_by.image (mapTri (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      packing53G u v x y z w a_ bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, _, _, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have e1 : mapTri f {2, 3, 4} = ({x, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f2, f3, f4]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 5} = ({u, y, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e4 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  have e5 : mapTri f {0, 4, 6} = ({u, z, a_} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f6]
  have e6 : mapTri f {1, 3, 9} = ({v, y, bPlus} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f9]
  simp only [packing10_53G_by, packing53G, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma packing53G_image_eq_azby (u v x y z w a_ aPlus b_ bPlus : V) :
    packing10_53G_azby.image (mapTri (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      packing53G u v x y z w aPlus bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, _, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have e1 : mapTri f {2, 3, 4} = ({x, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f2, f3, f4]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 5} = ({u, y, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e4 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  have e5 : mapTri f {0, 4, 7} = ({u, z, aPlus} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f7]
  have e6 : mapTri f {1, 3, 9} = ({v, y, bPlus} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f9]
  simp only [packing10_53G_azby, packing53G, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma cover53G_image_eq (u v x y z w a_ aPlus b_ bPlus : V) :
    cover10_53G.image (Sym2.map (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      cover53G u v x y z w a_ aPlus b_ bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53G, cover53G, image_insert, image_singleton,
    mk 2 3 f2 f3, mk 2 4 f2 f4, mk 3 4 f3 f4, mk 3 5 f3 f5, mk 4 5 f4 f5,
    mk 4 6 f4 f6, mk 3 8 f3 f8, mk 0 1 f0 f1, mk 0 5 f0 f5, mk 1 5 f1 f5,
    mk 0 7 f0 f7, mk 1 9 f1 f9]

private lemma cover53G_image_eq_az (u v x y z w a_ aPlus b_ bPlus : V) :
    cover10_53G_az.image (Sym2.map (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      cover53G u v x y z w aPlus aPlus b_ bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, f8, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53G_az, cover53G, image_insert, image_singleton,
    mk 2 3 f2 f3, mk 2 4 f2 f4, mk 3 4 f3 f4, mk 3 5 f3 f5, mk 4 5 f4 f5,
    mk 4 7 f4 f7, mk 3 8 f3 f8, mk 0 1 f0 f1, mk 0 5 f0 f5, mk 1 5 f1 f5,
    mk 0 7 f0 f7, mk 1 9 f1 f9]

private lemma cover53G_image_eq_by (u v x y z w a_ aPlus b_ bPlus : V) :
    cover10_53G_by.image (Sym2.map (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      cover53G u v x y z w a_ aPlus bPlus bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, _, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53G_by, cover53G, image_insert, image_singleton,
    mk 2 3 f2 f3, mk 2 4 f2 f4, mk 3 4 f3 f4, mk 3 5 f3 f5, mk 4 5 f4 f5,
    mk 4 6 f4 f6, mk 3 9 f3 f9, mk 0 1 f0 f1, mk 0 5 f0 f5, mk 1 5 f1 f5,
    mk 0 7 f0 f7, mk 1 9 f1 f9]

private lemma cover53G_image_eq_azby (u v x y z w a_ aPlus b_ bPlus : V) :
    cover10_53G_azby.image (Sym2.map (labels10 u v x y z w a_ aPlus b_ bPlus)) =
      cover53G u v x y z w aPlus aPlus bPlus bPlus := by
  obtain ⟨f0, f1, f2, f3, f4, f5, _, f7, _, f9⟩ :=
    map_lab u v x y z w a_ aPlus b_ bPlus
  set f := labels10 u v x y z w a_ aPlus b_ bPlus
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53G_azby, cover53G, image_insert, image_singleton,
    mk 2 3 f2 f3, mk 2 4 f2 f4, mk 3 4 f3 f4, mk 3 5 f3 f5, mk 4 5 f4 f5,
    mk 4 7 f4 f7, mk 3 9 f3 f9, mk 0 1 f0 f1, mk 0 5 f0 f5, mk 1 5 f1 f5,
    mk 0 7 f0 f7, mk 1 9 f1 f9]

private lemma packing53G_disjoint_of_pairwise
    (u v x y z w a_ aPlus b_ bPlus : V)
    (hinj : Function.Injective (labels10 u v x y z w a_ aPlus b_ bPlus))
    (P : Finset (Finset (Fin 10)))
    (hpair : ∀ σ ∈ P, ∀ τ ∈ P, σ ≠ τ → (σ ∩ τ).card ≤ 1)
    (σ τ : Finset V) (s0 t0 : Finset (Fin 10))
    (hs0 : s0 ∈ P) (ht0 : t0 ∈ P) (hne : s0 ≠ t0)
    (hσ : mapTri (labels10 u v x y z w a_ aPlus b_ bPlus) s0 = σ)
    (hτ : mapTri (labels10 u v x y z w a_ aPlus b_ bPlus) t0 = τ) :
    Disjoint (triEdges σ) (triEdges τ) := by
  let f := labels10 u v x y z w a_ aPlus b_ bPlus
  have hinter := hpair s0 hs0 t0 ht0 hne
  have hinter' : (mapTri f s0 ∩ mapTri f t0).card ≤ 1 := by
    have : mapTri f s0 ∩ mapTri f t0 = (s0 ∩ t0).image f := by
      simp only [mapTri]; exact (Finset.image_inter s0 t0 hinj).symm
    rw [this]; exact le_trans card_image_le hinter
  rw [← hσ, ← hτ, Finset.disjoint_left]
  intro e heA heB
  have hA := mem_filter.1 heA
  have hB := mem_filter.1 heB
  revert hA hB
  refine Sym2.inductionOn e fun a b hA hB => ?_
  have haA : a ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 a (Sym2.mem_mk_left a b)
  have hbA : b ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 b (Sym2.mem_mk_right a b)
  have haB : a ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 a (Sym2.mem_mk_left a b)
  have hbB : b ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 b (Sym2.mem_mk_right a b)
  have hab : a ≠ b := fun eq => hA.2 (by simpa [Sym2.mk_isDiag_iff] using eq)
  have hsub : ({a, b} : Finset V) ⊆ mapTri f s0 ∩ mapTri f t0 := by
    intro t ht; simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [haA, hbA, haB, hbB]
  have : 2 ≤ (mapTri f s0 ∩ mapTri f t0).card :=
    (card_le_card hsub).trans' (by simp [card_insert_of_notMem, hab])
  omega

lemma packing53G_card (u v x y z w a_ aPlus b_ bPlus αz βy : V)
    (hinj : Function.Injective (labels10 u v x y z w a_ aPlus b_ bPlus))
    (hαz : αz = a_ ∨ αz = aPlus) (hβy : βy = b_ ∨ βy = bPlus) :
    (packing53G u v x y z w αz βy).card = 6 := by
  let f := labels10 u v x y z w a_ aPlus b_ bPlus
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rcases hαz with hαz | hαz <;> rcases hβy with hβy | hβy <;> subst αz βy
  · rw [← packing53G_image_eq u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjT, packing10_53G_card]
  · rw [← packing53G_image_eq_by u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjT, packing10_53G_by_card]
  · rw [← packing53G_image_eq_az u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjT, packing10_53G_az_card]
  · rw [← packing53G_image_eq_azby u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjT, packing10_53G_azby_card]

lemma packing53G_disjoint (u v x y z w a_ aPlus b_ bPlus αz βy : V)
    (hinj : Function.Injective (labels10 u v x y z w a_ aPlus b_ bPlus))
    (hαz : αz = a_ ∨ αz = aPlus) (hβy : βy = b_ ∨ βy = bPlus) :
    ∀ σ ∈ packing53G u v x y z w αz βy,
      ∀ τ ∈ packing53G u v x y z w αz βy,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rcases hαz with hαz | hαz <;> rcases hβy with hβy | hβy
  · subst αz βy
    rw [← packing53G_image_eq u v x y z w a_ aPlus b_ bPlus] at hs ht
    obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
    obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
    exact packing53G_disjoint_of_pairwise u v x y z w a_ aPlus b_ bPlus hinj
      packing10_53G packing10_53G_pairwise _ _ s0 t0 hs0 ht0
      (fun h => by subst h; exact hst rfl) rfl rfl
  · subst αz βy
    rw [← packing53G_image_eq_by u v x y z w a_ aPlus b_ bPlus] at hs ht
    obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
    obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
    exact packing53G_disjoint_of_pairwise u v x y z w a_ aPlus b_ bPlus hinj
      packing10_53G_by packing10_53G_by_pairwise _ _ s0 t0 hs0 ht0
      (fun h => by subst h; exact hst rfl) rfl rfl
  · subst αz βy
    rw [← packing53G_image_eq_az u v x y z w a_ aPlus b_ bPlus] at hs ht
    obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
    obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
    exact packing53G_disjoint_of_pairwise u v x y z w a_ aPlus b_ bPlus hinj
      packing10_53G_az packing10_53G_az_pairwise _ _ s0 t0 hs0 ht0
      (fun h => by subst h; exact hst rfl) rfl rfl
  · subst αz βy
    rw [← packing53G_image_eq_azby u v x y z w a_ aPlus b_ bPlus] at hs ht
    obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
    obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
    exact packing53G_disjoint_of_pairwise u v x y z w a_ aPlus b_ bPlus hinj
      packing10_53G_azby packing10_53G_azby_pairwise _ _ s0 t0 hs0 ht0
      (fun h => by subst h; exact hst rfl) rfl rfl

lemma cover53G_card (u v x y z w a_ aPlus b_ bPlus αz βy : V)
    (hinj : Function.Injective (labels10 u v x y z w a_ aPlus b_ bPlus))
    (hαz : αz = a_ ∨ αz = aPlus) (hβy : βy = b_ ∨ βy = bPlus) :
    (cover53G u v x y z w αz aPlus βy bPlus).card = 12 := by
  let f := labels10 u v x y z w a_ aPlus b_ bPlus
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rcases hαz with hαz | hαz <;> rcases hβy with hβy | hβy <;> subst αz βy
  · rw [← cover53G_image_eq u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjE, cover10_53G_card]
  · rw [← cover53G_image_eq_by u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjE, cover10_53G_by_card]
  · rw [← cover53G_image_eq_az u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjE, cover10_53G_az_card]
  · rw [← cover53G_image_eq_azby u v x y z w a_ aPlus b_ bPlus,
      card_image_of_injective _ hinjE, cover10_53G_azby_card]


/-- **Proposition 5.3 (G)**, labelled: K₄ with fiber inclusions of Lemma 5.2(G).
Packing uses attachments αz = α(z) and βy = β(y), which may be a_/aPlus and b_/bPlus. -/
theorem k4_certificate_G (H : HubConfig G)
    (x y z w a_ aPlus b_ bPlus αz βy : V)
    (hC : H.C = {x, y, z, w})
    (hA : H.A = {a_, aPlus}) (hB : H.B = {b_, bPlus})
    (hK4 : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w)
    (hαz : αz = a_ ∨ αz = aPlus) (hβy : βy = b_ ∨ βy = bPlus)
    (hzα : G.Adj z αz) (hyβ : G.Adj y βy)
    (hαz_of : G.Adj z a_ → αz = a_) (hβy_of : G.Adj y b_ → βy = b_)
    (hα : ∀ c ∈ H.C, G.Adj c a_ → c = w ∨ c = z)
    (hβ : ∀ c ∈ H.C, G.Adj c b_ → c = w ∨ c = y)
    (h10 : ({H.u, H.v, x, y, z, w, a_, aPlus, b_, bPlus} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y z w a_ aPlus b_ bPlus h10
  let S := packing53G H.u H.v x y z w αz βy
  let X := cover53G H.u H.v x y z w αz aPlus βy bPlus
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uz : G.Adj H.u z := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uw : G.Adj H.u w := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua_adj : G.Adj H.u a_ := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have uaP : G.Adj H.u aPlus := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vz : G.Adj H.v z := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vw : G.Adj H.v w := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vb_adj : G.Adj H.v b_ := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vbP : G.Adj H.v bPlus := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have uαz : G.Adj H.u αz := by rcases hαz with rfl | rfl; exact ua_adj; exact uaP
  have vβy : G.Adj H.v βy := by rcases hβy with rfl | rfl; exact vb_adj; exact vbP
  have hdist := core4_distinct G H hC
  have ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := hdist
  have not_u_C : H.u ∉ H.C := H.huB.2
  have not_u_A : H.u ∉ H.A := by
    intro h
    have : H.u ∈ G.neighborFinset H.u := by
      rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ h)
    exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
  have c3 {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      ({a, b, c} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  have c_xyz : ({x, y, z} : Finset V).card = 3 := c3 hxy hxz hyz
  have c_uvx : ({H.u, H.v, x} : Finset V).card = 3 :=
    c3 (fun eq => G.irrefl (eq ▸ H.huv))
      (fun eq => not_u_C (by rw [hC, eq]; simp))
      (ne_z_of_core G H (by rw [hC]; simp))
  have c_uyw : ({H.u, y, w} : Finset V).card = 3 :=
    c3 (fun eq => not_u_C (by rw [hC, eq]; simp))
      (fun eq => not_u_C (by rw [hC, eq]; simp)) hyw
  have c_vzw : ({H.v, z, w} : Finset V).card = 3 :=
    c3 (ne_z_of_core G H (by rw [hC]; simp))
      (ne_z_of_core G H (by rw [hC]; simp)) hzw
  have memA_αz : αz ∈ H.A := by rcases hαz with rfl | rfl <;> simp [hA]
  have memB_βy : βy ∈ H.B := by rcases hβy with rfl | rfl <;> simp [hB]
  have c_uza : ({H.u, z, αz} : Finset V).card = 3 :=
    c3 (fun eq => not_u_C (by rw [hC, eq]; simp))
      (fun eq => not_u_A (by rwa [← eq] at memA_αz))
      (ne_core_priv G H (by rw [hC]; simp) memA_αz)
  have c_vyb : ({H.v, y, βy} : Finset V).card = 3 :=
    c3 (ne_z_of_core G H (by rw [hC]; simp))
      (fun eq => by
        have : H.v ∈ G.neighborFinset H.v := by
          rw [H.hNv]; exact mem_insert_of_mem (mem_union_right _ (eq ▸ memB_βy))
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this))
      (fun h => Finset.disjoint_left.1 H.hBdisj memB_βy (by subst h; simp [hC]))

  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packing53G_disjoint H.u H.v x y z w a_ aPlus b_ bPlus αz βy hinj hαz hβy⟩
    intro t ht
    simp only [S, packing53G, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G hK4.1 hK4.2.1 hK4.2.2.2.1 c_xyz
    · exact is3clique_of_adj G uvs ux vx c_uvx
    · exact is3clique_of_adj G uy uw hK4.2.2.2.2.1 c_uyw
    · exact is3clique_of_adj G vz vw hK4.2.2.2.2.2 c_vzw
    · exact is3clique_of_adj G uz uαz hzα c_uza
    · exact is3clique_of_adj G vy vβy hyβ c_vyb
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, cover53G, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hK4.1
    · subst h; exact (mem_edgeFinset).2 hK4.2.1
    · subst h; exact (mem_edgeFinset).2 hK4.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 hK4.2.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 hK4.2.2.2.2.2
    · subst h; exact (mem_edgeFinset).2 hzα
    · subst h; exact (mem_edgeFinset).2 hyβ
    · subst h; exact (mem_edgeFinset).2 uvs
    · subst h; exact (mem_edgeFinset).2 uw
    · subst h; exact (mem_edgeFinset).2 vw
    · subst h; exact (mem_edgeFinset).2 uaP
    · subst h; exact (mem_edgeFinset).2 vbP
  have hcardS := packing53G_card H.u H.v x y z w a_ aPlus b_ bPlus αz βy hinj hαz hβy
  have hcardX := cover53G_card H.u H.v x y z w a_ aPlus b_ bPlus αz βy hinj hαz hβy
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 6 := hcardS
    have hX : X.card = 12 := hcardX
    omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packing53G, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have heq := triEdges_eq_of_card3 c_xyz
      rw [heq] at he
      simp only [mem_insert, mem_singleton] at he
      rcases he with h | h | h <;> simp [X, cover53G, h]
    · have : False := by
        have heq := triEdges_eq_of_card3 c_uvx
        rw [heq] at he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hu (by simp)
        · exact hu (by simp)
        · exact hv (by simp)
      exact this.elim
    · have h := triEdges_omit_vertex c_uyw he hu; rw [h]; simp [X, cover53G]
    · have h := triEdges_omit_vertex c_vzw he hv; rw [h]; simp [X, cover53G]
    · have h := triEdges_omit_vertex c_uza he hu; rw [h]; simp [X, cover53G]
    · have h := triEdges_omit_vertex c_vyb he hv; rw [h]; simp [X, cover53G]
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core_edge (p q : V) (hpC : p ∈ H.C) (hqC : q ∈ H.C) (hne : p ≠ q) :
        s(p, q) = s(x, y) ∨ s(p, q) = s(x, z) ∨ s(p, q) = s(x, w) ∨
        s(p, q) = s(y, z) ∨ s(p, q) = s(y, w) ∨ s(p, q) = s(z, w) := by
      have hp' : p ∈ ({x, y, z, w} : Finset V) := by rw [← hC]; exact hpC
      have hq' : q ∈ ({x, y, z, w} : Finset V) := by rw [← hC]; exact hqC
      simp only [mem_insert, mem_singleton] at hp' hq'
      rcases hp' with rfl | rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl Sym2.eq_swap
      · exact absurd rfl hne
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inl Sym2.eq_swap)
      · exact Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))
      · exact absurd rfl hne
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr Sym2.eq_swap))))
      · exact absurd rfl hne
    rcases hhub with rfl | rfl
    · have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv; exact meet s(H.u, H.v) (by simp [X, cover53G]) him_zx
      by_cases hyv : py = H.v
      · subst hyv; exact meet s(H.u, H.v) (by simp [X, cover53G]) him_zy
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxA : px ∈ H.A
      · have hpa : px = a_ ∨ px = aPlus := by simpa [hA] using hxA
        rcases hpa with hpxa | hpxa
        · by_cases hyA : py ∈ H.A
          · have hpya' : py = a_ ∨ py = aPlus := by simpa [hA] using hyA
            rcases hpya' with hpya | hpya
            · exact absurd (hpxa.trans hpya.symm) hpxy
            · exact meet s(H.u, aPlus) (by simp [X, cover53G]) (hpya ▸ him_zy)
          · have hyC : py ∈ H.C := (mem_union.1 hyCA).resolve_right hyA
            have hadj' : G.Adj a_ py := by rwa [hpxa] at hxyAdj
            have hywz : py = w ∨ py = z := hα py hyC hadj'.symm
            rcases hywz with hpy | hpy
            · exact meet s(H.u, w) (by simp [X, cover53G]) (hpy ▸ him_zy)
            · have hrim' : s(z, a_) ∈ triEdges t := by
                simpa [hpxa, hpy, Sym2.eq_swap] using him_rim
              have hαeq : αz = a_ := hαz_of (by simpa [hpy] using hadj'.symm)
              exact meet s(z, αz) (by simp [X, cover53G]) (by simpa [hαeq] using hrim')
        · exact meet s(H.u, aPlus) (by simp [X, cover53G]) (hpxa ▸ him_zx)
      by_cases hyA : py ∈ H.A
      · have hpa : py = a_ ∨ py = aPlus := by simpa [hA] using hyA
        rcases hpa with hpya | hpya
        · have hxC : px ∈ H.C := (mem_union.1 hxCA).resolve_right hxA
          have hadj' : G.Adj px a_ := by rwa [hpya] at hxyAdj
          have hxwz : px = w ∨ px = z := hα px hxC hadj'
          rcases hxwz with hpx | hpx
          · exact meet s(H.u, w) (by simp [X, cover53G]) (hpx ▸ him_zx)
          · have hrim' : s(z, a_) ∈ triEdges t := by simpa [hpx, hpya] using him_rim
            have hαeq : αz = a_ := hαz_of (by simpa [hpx] using hadj')
            exact meet s(z, αz) (by simp [X, cover53G]) (by simpa [hαeq] using hrim')
        · exact meet s(H.u, aPlus) (by simp [X, cover53G]) (hpya ▸ him_zy)
      · have hxC : px ∈ H.C := (mem_union.1 hxCA).resolve_right hxA
        have hyC : py ∈ H.C := (mem_union.1 hyCA).resolve_right hyA
        rcases core_edge px py hxC hyC hpxy with hr | hr | hr | hr | hr | hr
        · rw [hr] at him_rim; exact meet s(x, y) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(x, z) (by simp [X, cover53G]) him_rim
        · have hwmem : w = px ∨ w = py := by
            have : w ∈ s(px, py).toFinset := by
              simpa [← hr, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right x w
            simpa [Sym2.toFinset_mk_eq, mem_insert, mem_singleton, eq_comm] using this
          rcases hwmem with hw | hw
          · exact meet s(H.u, w) (by simp [X, cover53G]) (hw ▸ him_zx)
          · exact meet s(H.u, w) (by simp [X, cover53G]) (hw ▸ him_zy)
        · rw [hr] at him_rim; exact meet s(y, z) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(y, w) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(z, w) (by simp [X, cover53G]) him_rim
    · have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zx
        exact meet s(H.u, H.v) (by simp [X, cover53G]) heT
      by_cases hyu : py = H.u
      · subst hyu
        have heT : s(H.u, H.v) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_zy
        exact meet s(H.u, H.v) (by simp [X, cover53G]) heT
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxB : px ∈ H.B
      · have hpb : px = b_ ∨ px = bPlus := by simpa [hB] using hxB
        rcases hpb with hpxb | hpxb
        · by_cases hyB : py ∈ H.B
          · have hpyb' : py = b_ ∨ py = bPlus := by simpa [hB] using hyB
            rcases hpyb' with hpyb | hpyb
            · exact absurd (hpxb.trans hpyb.symm) hpxy
            · exact meet s(H.v, bPlus) (by simp [X, cover53G]) (hpyb ▸ him_zy)
          · have hyC : py ∈ H.C := (mem_union.1 hyCB).resolve_right hyB
            have hadj' : G.Adj b_ py := by rwa [hpxb] at hxyAdj
            have hywy : py = w ∨ py = y := hβ py hyC hadj'.symm
            rcases hywy with hpy | hpy
            · exact meet s(H.v, w) (by simp [X, cover53G]) (hpy ▸ him_zy)
            · have hrim' : s(y, b_) ∈ triEdges t := by
                simpa [hpxb, hpy, Sym2.eq_swap] using him_rim
              have hβeq : βy = b_ := hβy_of (by simpa [hpy] using hadj'.symm)
              exact meet s(y, βy) (by simp [X, cover53G]) (by simpa [hβeq] using hrim')
        · exact meet s(H.v, bPlus) (by simp [X, cover53G]) (hpxb ▸ him_zx)
      by_cases hyB : py ∈ H.B
      · have hpb : py = b_ ∨ py = bPlus := by simpa [hB] using hyB
        rcases hpb with hpyb | hpyb
        · have hxC : px ∈ H.C := (mem_union.1 hxCB).resolve_right hxB
          have hadj' : G.Adj px b_ := by rwa [hpyb] at hxyAdj
          have hxwy : px = w ∨ px = y := hβ px hxC hadj'
          rcases hxwy with hpx | hpx
          · exact meet s(H.v, w) (by simp [X, cover53G]) (hpx ▸ him_zx)
          · have hrim' : s(y, b_) ∈ triEdges t := by simpa [hpx, hpyb] using him_rim
            have hβeq : βy = b_ := hβy_of (by simpa [hpx] using hadj')
            exact meet s(y, βy) (by simp [X, cover53G]) (by simpa [hβeq] using hrim')
        · exact meet s(H.v, bPlus) (by simp [X, cover53G]) (hpyb ▸ him_zy)
      · have hxC : px ∈ H.C := (mem_union.1 hxCB).resolve_right hxB
        have hyC : py ∈ H.C := (mem_union.1 hyCB).resolve_right hyB
        rcases core_edge px py hxC hyC hpxy with hr | hr | hr | hr | hr | hr
        · rw [hr] at him_rim; exact meet s(x, y) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(x, z) (by simp [X, cover53G]) him_rim
        · have hwmem : w = px ∨ w = py := by
            have : w ∈ s(px, py).toFinset := by
              simpa [← hr, Sym2.toFinset_mk_eq] using Sym2.mem_mk_right x w
            simpa [Sym2.toFinset_mk_eq, mem_insert, mem_singleton, eq_comm] using this
          rcases hwmem with hw | hw
          · exact meet s(H.v, w) (by simp [X, cover53G]) (hw ▸ him_zx)
          · exact meet s(H.v, w) (by simp [X, cover53G]) (hw ▸ him_zy)
        · rw [hr] at him_rim; exact meet s(y, z) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(y, w) (by simp [X, cover53G]) him_rim
        · rw [hr] at him_rim; exact meet s(z, w) (by simp [X, cover53G]) him_rim
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩



/-! ### Lemma 5.2 (Fin 4 → Fin 2 enumeration) -/

/-- Encode `Fin 4 → Fin 2` as a 4-bit number. -/
def decode42 (n : Fin 16) : Fin 4 → Fin 2 := fun i =>
  ⟨(n.val >>> i.val) % 2, by omega⟩

lemma decode42_surj (f : Fin 4 → Fin 2) : ∃ n : Fin 16, decode42 n = f := by
  let n : ℕ := (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val
  have hn : n < 16 := by
    have h0 : (f 0).val ≤ 1 := Nat.le_of_lt_succ (f 0).isLt
    have h1 : (f 1).val ≤ 1 := Nat.le_of_lt_succ (f 1).isLt
    have h2 : (f 2).val ≤ 1 := Nat.le_of_lt_succ (f 2).isLt
    have h3 : (f 3).val ≤ 1 := Nat.le_of_lt_succ (f 3).isLt
    omega
  refine ⟨⟨n, hn⟩, funext fun i => ?_⟩
  -- Check the four bit extractions by cases on i and on each f-value.
  have bit (k : ℕ) (hk : k < 4) :
      ((n >>> k) % 2) = (f ⟨k, hk⟩).val := by
    have h0 : (f 0).val ≤ 1 := Nat.le_of_lt_succ (f 0).isLt
    have h1 : (f 1).val ≤ 1 := Nat.le_of_lt_succ (f 1).isLt
    have h2 : (f 2).val ≤ 1 := Nat.le_of_lt_succ (f 2).isLt
    have h3 : (f 3).val ≤ 1 := Nat.le_of_lt_succ (f 3).isLt
    interval_cases k <;> simp [n] <;> omega
  apply Fin.ext
  simpa [decode42] using bit i.val i.isLt

def fiber42 (f : Fin 4 → Fin 2) (a : Fin 2) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => f i = a)

def isE42 (α β : Fin 4 → Fin 2) : Bool :=
  decide ((fiber42 α 0).card = 2 ∧ (fiber42 β 0).card = 2 ∧
    (fiber42 α 0 = fiber42 β 0 ∨ fiber42 α 0 = fiber42 β 1))

def isG42 (α β : Fin 4 → Fin 2) : Bool :=
  decide (∃ (p : Equiv.Perm (Fin 4)) (ia ib : Fin 2),
    (∀ i : Fin 4, α (p i) ≠ ia ∨ i = 2 ∨ i = 3) ∧
    (∀ i : Fin 4, β (p i) ≠ ib ∨ i = 1 ∨ i = 3))

private lemma lemma52_fin : ∀ n m : Fin 16,
    isG42 (decode42 n) (decode42 m) = true ∨
    isE42 (decode42 n) (decode42 m) = true := by
  native_decide

/-- **Lemma 5.2**: maps `C → A`, `C → B` fall into alternative (G) or (E). -/
theorem lemma52 {C A B : Finset V}
    (hC4 : C.card = 4) (hA : A.card = 2) (hB : B.card = 2)
    (α β : V → V)
    (hα : ∀ c ∈ C, α c ∈ A) (hβ : ∀ c ∈ C, β c ∈ B) :
    (∃ x y z w a_ b_,
      C = {x, y, z, w} ∧ a_ ∈ A ∧ b_ ∈ B ∧
        (∀ c ∈ C, α c = a_ → c = w ∨ c = z) ∧
        (∀ c ∈ C, β c = b_ → c = w ∨ c = y))
    ∨
    (∃ x y z w a a' b b',
      C = {x, y, z, w} ∧ A = {a, a'} ∧ B = {b, b'} ∧
        a ≠ a' ∧ b ≠ b' ∧
        α x = a ∧ α y = a ∧ α z = a' ∧ α w = a' ∧
        β x = b ∧ β y = b ∧ β z = b' ∧ β w = b') := by
  classical
  have hCfin : Fintype.card {x // x ∈ C} = 4 := by simp [Fintype.card_coe, hC4]
  have hAfin : Fintype.card {x // x ∈ A} = 2 := by simp [Fintype.card_coe, hA]
  have hBfin : Fintype.card {x // x ∈ B} = 2 := by simp [Fintype.card_coe, hB]
  let eC : Fin 4 ≃ {x // x ∈ C} := Fintype.equivOfCardEq hCfin.symm
  let eA : Fin 2 ≃ {x // x ∈ A} := Fintype.equivOfCardEq hAfin.symm
  let eB : Fin 2 ≃ {x // x ∈ B} := Fintype.equivOfCardEq hBfin.symm
  let ℓ : Fin 4 → V := fun i => (eC i).1
  have hℓC : ∀ i, ℓ i ∈ C := fun i => (eC i).2
  have hℓsurj : ∀ c ∈ C, ∃ i, ℓ i = c := by
    intro c hc; exact ⟨eC.symm ⟨c, hc⟩, by simp [ℓ]⟩
  let αf : Fin 4 → Fin 2 := fun i => eA.symm ⟨α (ℓ i), hα (ℓ i) (hℓC i)⟩
  let βf : Fin 4 → Fin 2 := fun i => eB.symm ⟨β (ℓ i), hβ (ℓ i) (hℓC i)⟩
  have hα_val : ∀ i, (eA (αf i)).1 = α (ℓ i) := fun i => by simp [αf]
  have hβ_val : ∀ i, (eB (βf i)).1 = β (ℓ i) := fun i => by simp [βf]
  have hα_eq (i : Fin 4) (ia : Fin 2) :
      α (ℓ i) = (eA ia).1 ↔ αf i = ia := by
    constructor
    · intro h
      exact eA.injective (Subtype.ext (by rw [hα_val, h]))
    · intro h; rw [← hα_val, h]
  have hβ_eq (i : Fin 4) (ib : Fin 2) :
      β (ℓ i) = (eB ib).1 ↔ βf i = ib := by
    constructor
    · intro h
      exact eB.injective (Subtype.ext (by rw [hβ_val, h]))
    · intro h; rw [← hβ_val, h]
  obtain ⟨n, hn⟩ := decode42_surj αf
  obtain ⟨m, hm⟩ := decode42_surj βf
  have fin01 (k : Fin 2) : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  have fiber_union (f : Fin 4 → Fin 2) :
      fiber42 f 0 ∪ fiber42 f 1 = (univ : Finset (Fin 4)) := by
    ext i; constructor
    · intro; exact mem_univ _
    · intro; simp [fiber42, mem_filter]; exact fin01 (f i)
  have fiber_disj (f : Fin 4 → Fin 2) :
      Disjoint (fiber42 f 0) (fiber42 f 1) :=
    Finset.disjoint_left.2 fun i hi hj => by
      simp only [fiber42, mem_filter] at hi hj
      exact absurd hi.2 (by rw [hj.2]; decide)
  rcases lemma52_fin n m with hG | hE
  · have hG' : isG42 αf βf = true := by simpa [hn, hm] using hG
    have hEx : ∃ (p : Equiv.Perm (Fin 4)) (ia ib : Fin 2),
        (∀ i : Fin 4, αf (p i) ≠ ia ∨ i = 2 ∨ i = 3) ∧
        (∀ i : Fin 4, βf (p i) ≠ ib ∨ i = 1 ∨ i = 3) :=
      of_decide_eq_true hG'
    obtain ⟨p, ia, ib, hαcond, hβcond⟩ := hEx
    let x := ℓ (p 0); let y := ℓ (p 1); let z := ℓ (p 2); let w := ℓ (p 3)
    let a_ := (eA ia).1; let b_ := (eB ib).1
    have hCeq : C = {x, y, z, w} := by
      ext c; constructor
      · intro hc
        obtain ⟨i0, rfl⟩ := hℓsurj c hc
        obtain ⟨j, rfl⟩ : ∃ j, p j = i0 := ⟨p.symm i0, Equiv.apply_symm_apply _ _⟩
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
        rcases this with h | h | h | h <;> simp [x, y, z, w, h]
      · intro hc
        simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact hℓC _
    refine Or.inl ⟨x, y, z, w, a_, b_, hCeq, Subtype.property _, Subtype.property _, ?_, ?_⟩
    · intro c hc hαc
      obtain ⟨i0, rfl⟩ := hℓsurj c hc
      obtain ⟨j, rfl⟩ : ∃ j, p j = i0 := ⟨p.symm i0, Equiv.apply_symm_apply _ _⟩
      have hia : αf (p j) = ia := (hα_eq _ _).1 hαc
      have hj : j = 2 ∨ j = 3 := by have := hαcond j; simp [hia] at this; exact this
      rcases hj with rfl | rfl <;> simp [z, w]
    · intro c hc hβc
      obtain ⟨i0, rfl⟩ := hℓsurj c hc
      obtain ⟨j, rfl⟩ : ∃ j, p j = i0 := ⟨p.symm i0, Equiv.apply_symm_apply _ _⟩
      have hib : βf (p j) = ib := (hβ_eq _ _).1 hβc
      have hj : j = 1 ∨ j = 3 := by have := hβcond j; simp [hib] at this; exact this
      rcases hj with rfl | rfl <;> simp [y, w]
  · have hE' : isE42 αf βf = true := by simpa [hn, hm] using hE
    have hP : (fiber42 αf 0).card = 2 ∧ (fiber42 βf 0).card = 2 ∧
        (fiber42 αf 0 = fiber42 βf 0 ∨ fiber42 αf 0 = fiber42 βf 1) :=
      of_decide_eq_true hE'
    obtain ⟨hα2, hβ2, hpart⟩ := hP
    have hα1 : (fiber42 αf 1).card = 2 := by
      have hsum : (fiber42 αf 0).card + (fiber42 αf 1).card =
          (fiber42 αf 0 ∪ fiber42 αf 1).card :=
        (card_union_of_disjoint (fiber_disj αf)).symm
      have : (fiber42 αf 0 ∪ fiber42 αf 1).card = 4 := by
        rw [fiber_union αf]; simp
      omega
    obtain ⟨i0, i1, hi01, hPa0⟩ := (card_eq_two (s := fiber42 αf 0)).1 hα2
    obtain ⟨i2, i3, hi23, hPa1⟩ := (card_eq_two (s := fiber42 αf 1)).1 hα1
    let x := ℓ i0; let y := ℓ i1; let z := ℓ i2; let w := ℓ i3
    let a := (eA 0).1; let a' := (eA 1).1
    have ha_ne : a ≠ a' := fun h =>
      absurd (eA.injective (Subtype.ext h)) (by decide : (0 : Fin 2) ≠ 1)
    have hAeq : A = {a, a'} := by
      ext t; constructor
      · intro ht
        obtain ⟨k, hk⟩ : ∃ k : Fin 2, (eA k).1 = t :=
          ⟨eA.symm ⟨t, ht⟩, by simp⟩
        rw [← hk]; fin_cases k <;> simp [a, a']
      · intro ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl <;> exact Subtype.property _
    have hCeq : C = {x, y, z, w} := by
      ext c; constructor
      · intro hc
        obtain ⟨i, rfl⟩ := hℓsurj c hc
        have hiU : i ∈ fiber42 αf 0 ∪ fiber42 αf 1 := by rw [fiber_union]; exact mem_univ _
        rw [hPa0, hPa1] at hiU
        simp only [mem_union, mem_insert, mem_singleton] at hiU
        rcases hiU with (rfl | rfl) | (rfl | rfl) <;> simp [x, y, z, w]
      · intro hc
        simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> exact hℓC _
    have mem0 {i} (h : i ∈ fiber42 αf 0) : αf i = 0 := (mem_filter.1 h).2
    have mem1 {i} (h : i ∈ fiber42 αf 1) : αf i = 1 := (mem_filter.1 h).2
    have hαx : α x = a := (hα_eq i0 0).2 (mem0 (by rw [hPa0]; simp))
    have hαy : α y = a := (hα_eq i1 0).2 (mem0 (by rw [hPa0]; simp))
    have hαz : α z = a' := (hα_eq i2 1).2 (mem1 (by rw [hPa1]; simp))
    have hαw : α w = a' := (hα_eq i3 1).2 (mem1 (by rw [hPa1]; simp))
    -- Helper: if i ∉ fiber β 0 then βf i = 1
    have βf_one {i : Fin 4} (hne : i ∉ fiber42 βf 0) : βf i = 1 := by
      have : βf i = 0 ∨ βf i = 1 := fin01 _
      exact this.resolve_left fun h => hne (by simp [fiber42, mem_filter, h])
    have βf_zero {i : Fin 4} (h : i ∈ fiber42 βf 0) : βf i = 0 := (mem_filter.1 h).2
    have βf_one' {i : Fin 4} (h : i ∈ fiber42 βf 1) : βf i = 1 := (mem_filter.1 h).2
    have notPa0_of_Pa1 {i} (h : i ∈ fiber42 αf 1) : i ∉ fiber42 αf 0 :=
      fun hi => Finset.disjoint_left.1 (fiber_disj αf) hi h
    rcases hpart with hsame | hswap
    · let b := (eB 0).1; let b' := (eB 1).1
      have hb_ne : b ≠ b' := fun h =>
        absurd (eB.injective (Subtype.ext h)) (by decide : (0 : Fin 2) ≠ 1)
      have hBeq : B = {b, b'} := by
        ext t; constructor
        · intro ht
          obtain ⟨k, hk⟩ : ∃ k : Fin 2, (eB k).1 = t :=
            ⟨eB.symm ⟨t, ht⟩, by simp⟩
          rw [← hk]; fin_cases k <;> simp [b, b']
        · intro ht
          simp only [mem_insert, mem_singleton] at ht
          rcases ht with rfl | rfl <;> exact Subtype.property _
      refine Or.inr ⟨x, y, z, w, a, a', b, b', hCeq, hAeq, hBeq, ha_ne, hb_ne,
        hαx, hαy, hαz, hαw, ?_, ?_, ?_, ?_⟩
      · exact (hβ_eq i0 0).2 (βf_zero (by rw [← hsame, hPa0]; simp))
      · exact (hβ_eq i1 0).2 (βf_zero (by rw [← hsame, hPa0]; simp))
      · exact (hβ_eq i2 1).2 (βf_one (by
          rw [← hsame]; exact notPa0_of_Pa1 (by rw [hPa1]; simp)))
      · exact (hβ_eq i3 1).2 (βf_one (by
          rw [← hsame]; exact notPa0_of_Pa1 (by rw [hPa1]; simp)))
    · -- Pa0 = Pb1, so β on Pa0 is 1, on Pa1 is 0
      let b := (eB 1).1; let b' := (eB 0).1
      have hb_ne : b ≠ b' := fun h =>
        absurd (eB.injective (Subtype.ext h)) (by decide : (1 : Fin 2) ≠ 0)
      have hBeq : B = {b, b'} := by
        ext t; constructor
        · intro ht
          obtain ⟨k, hk⟩ : ∃ k : Fin 2, (eB k).1 = t :=
            ⟨eB.symm ⟨t, ht⟩, by simp⟩
          rw [← hk]; fin_cases k <;> simp [b, b', Finset.pair_comm]
        · intro ht
          simp only [mem_insert, mem_singleton] at ht
          rcases ht with rfl | rfl <;> exact Subtype.property _
      refine Or.inr ⟨x, y, z, w, a, a', b, b', hCeq, hAeq, hBeq, ha_ne, hb_ne,
        hαx, hαy, hαz, hαw, ?_, ?_, ?_, ?_⟩
      · exact (hβ_eq i0 1).2 (βf_one' (by rw [← hswap, hPa0]; simp))
      · exact (hβ_eq i1 1).2 (βf_one' (by rw [← hswap, hPa0]; simp))
      · -- i2 in Pa1 ⇒ not in Pa0 = not in Pb1 ⇒ in Pb0
        have hi2 : i2 ∉ fiber42 βf 1 := by
          rw [← hswap]; exact notPa0_of_Pa1 (by rw [hPa1]; simp)
        have : βf i2 = 0 := by
          have : βf i2 = 0 ∨ βf i2 = 1 := fin01 _
          exact this.resolve_right fun h => hi2 (by simp [fiber42, mem_filter, h])
        exact (hβ_eq i2 0).2 this
      · have hi3 : i3 ∉ fiber42 βf 1 := by
          rw [← hswap]; exact notPa0_of_Pa1 (by rw [hPa1]; simp)
        have : βf i3 = 0 := by
          have : βf i3 = 0 ∨ βf i3 = 1 := fin01 _
          exact this.resolve_right fun h => hi3 (by simp [fiber42, mem_filter, h])
        exact (hβ_eq i3 0).2 this


/-! ### Prop 5.3(E) -/

/-- Fin-10 packing for case `d = a` (aa′ present). Labels: 0=u,1=v,2=x,3=y,4=z,5=w,6=a,7=a′,8=b,9=b′. -/
def packing10_53E_aa : Finset (Finset (Fin 10)) :=
  {{6, 2, 3}, {0, 1, 2}, {0, 3, 4}, {0, 7, 6}, {1, 3, 8}, {1, 4, 5}}

def packing10_53E_aw : Finset (Finset (Fin 10)) :=
  {{6, 2, 3}, {0, 1, 2}, {0, 3, 4}, {0, 7, 5}, {1, 3, 8}, {1, 4, 5}}

def cover10_53E_aa : Finset (Sym2 (Fin 10)) :=
  {s(6, 2), s(6, 3), s(2, 3), s(3, 4), s(7, 6), s(3, 8), s(4, 5),
   s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(1, 9)}

def cover10_53E_aw : Finset (Sym2 (Fin 10)) :=
  {s(6, 2), s(6, 3), s(2, 3), s(3, 4), s(7, 5), s(3, 8), s(4, 5),
   s(0, 4), s(0, 5), s(1, 2), s(1, 3), s(1, 9)}

lemma packing10_53E_aa_card : packing10_53E_aa.card = 6 := by native_decide
lemma packing10_53E_aw_card : packing10_53E_aw.card = 6 := by native_decide
lemma cover10_53E_aa_card : cover10_53E_aa.card = 12 := by native_decide
lemma cover10_53E_aw_card : cover10_53E_aw.card = 12 := by native_decide
lemma packing10_53E_aa_pairwise :
    ∀ σ ∈ packing10_53E_aa, ∀ τ ∈ packing10_53E_aa, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide
lemma packing10_53E_aw_pairwise :
    ∀ σ ∈ packing10_53E_aw, ∀ τ ∈ packing10_53E_aw, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

def packing53E (u v x y z w a a' d b : V) : Finset (Finset V) :=
  {{a, x, y}, {u, v, x}, {u, y, z}, {u, a', d}, {v, y, b}, {v, z, w}}

def cover53E (u v x y z w a a' d b b' : V) : Finset (Sym2 V) :=
  {s(a, x), s(a, y), s(x, y), s(y, z), s(a', d), s(y, b), s(z, w),
   s(u, z), s(u, w), s(v, x), s(v, y), s(v, b')}

private lemma packing53E_aa_image (u v x y z w a a' b b' : V) :
    packing10_53E_aa.image (mapTri (labels10 u v x y z w a a' b b')) =
      packing53E u v x y z w a a' a b := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, _⟩ :=
    map_lab u v x y z w a a' b b'
  set f := labels10 u v x y z w a a' b b'
  have e1 : mapTri f {6, 2, 3} = ({a, x, y} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f6, f2, f3]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 4} = ({u, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f4]
  have e4 : mapTri f {0, 7, 6} = ({u, a', a} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f7, f6]
  have e5 : mapTri f {1, 3, 8} = ({v, y, b} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  have e6 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  simp only [packing10_53E_aa, packing53E, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma packing53E_aw_image (u v x y z w a a' b b' : V) :
    packing10_53E_aw.image (mapTri (labels10 u v x y z w a a' b b')) =
      packing53E u v x y z w a a' w b := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, _⟩ :=
    map_lab u v x y z w a a' b b'
  set f := labels10 u v x y z w a a' b b'
  have e1 : mapTri f {6, 2, 3} = ({a, x, y} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f6, f2, f3]
  have e2 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e3 : mapTri f {0, 3, 4} = ({u, y, z} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f4]
  have e4 : mapTri f {0, 7, 5} = ({u, a', w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f7, f5]
  have e5 : mapTri f {1, 3, 8} = ({v, y, b} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  have e6 : mapTri f {1, 4, 5} = ({v, z, w} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f4, f5]
  simp only [packing10_53E_aw, packing53E, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma cover53E_aa_image (u v x y z w a a' b b' : V) :
    cover10_53E_aa.image (Sym2.map (labels10 u v x y z w a a' b b')) =
      cover53E u v x y z w a a' a b b' := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y z w a a' b b'
  set f := labels10 u v x y z w a a' b b'
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53E_aa, cover53E, image_insert, image_singleton,
    mk 6 2 f6 f2, mk 6 3 f6 f3, mk 2 3 f2 f3, mk 3 4 f3 f4, mk 7 6 f7 f6,
    mk 3 8 f3 f8, mk 4 5 f4 f5, mk 0 4 f0 f4, mk 0 5 f0 f5, mk 1 2 f1 f2,
    mk 1 3 f1 f3, mk 1 9 f1 f9]

private lemma cover53E_aw_image (u v x y z w a a' b b' : V) :
    cover10_53E_aw.image (Sym2.map (labels10 u v x y z w a a' b b')) =
      cover53E u v x y z w a a' w b b' := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y z w a a' b b'
  set f := labels10 u v x y z w a a' b b'
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_53E_aw, cover53E, image_insert, image_singleton,
    mk 6 2 f6 f2, mk 6 3 f6 f3, mk 2 3 f2 f3, mk 3 4 f3 f4, mk 7 5 f7 f5,
    mk 3 8 f3 f8, mk 4 5 f4 f5, mk 0 4 f0 f4, mk 0 5 f0 f5, mk 1 2 f1 f2,
    mk 1 3 f1 f3, mk 1 9 f1 f9]

lemma packing53E_aa_card (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    (packing53E u v x y z w a a' a b).card = 6 := by
  have hinjT : Function.Injective (mapTri (labels10 u v x y z w a a' b b')) :=
    Finset.image_injective hinj
  rw [← packing53E_aa_image, card_image_of_injective _ hinjT, packing10_53E_aa_card]

lemma packing53E_aw_card (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    (packing53E u v x y z w a a' w b).card = 6 := by
  have hinjT : Function.Injective (mapTri (labels10 u v x y z w a a' b b')) :=
    Finset.image_injective hinj
  rw [← packing53E_aw_image, card_image_of_injective _ hinjT, packing10_53E_aw_card]

lemma cover53E_aa_card (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    (cover53E u v x y z w a a' a b b').card = 12 := by
  have hinjE : Function.Injective (Sym2.map (labels10 u v x y z w a a' b b')) :=
    Sym2.map.injective hinj
  rw [← cover53E_aa_image, card_image_of_injective _ hinjE, cover10_53E_aa_card]

lemma cover53E_aw_card (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    (cover53E u v x y z w a a' w b b').card = 12 := by
  have hinjE : Function.Injective (Sym2.map (labels10 u v x y z w a a' b b')) :=
    Sym2.map.injective hinj
  rw [← cover53E_aw_image, card_image_of_injective _ hinjE, cover10_53E_aw_card]

lemma packing53E_aa_disjoint (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    ∀ σ ∈ packing53E u v x y z w a a' a b,
      ∀ τ ∈ packing53E u v x y z w a a' a b,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  let f := labels10 u v x y z w a a' b b'
  intro σ hs τ ht hst
  rw [← packing53E_aa_image u v x y z w a a' b b'] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  have hs0t0 : s0 ≠ t0 := fun h => by subst h; exact hst rfl
  have hinter := packing10_53E_aa_pairwise s0 hs0 t0 ht0 hs0t0
  have hinter' : (mapTri f s0 ∩ mapTri f t0).card ≤ 1 := by
    have : mapTri f s0 ∩ mapTri f t0 = (s0 ∩ t0).image f := by
      simp only [mapTri]; exact (Finset.image_inter s0 t0 hinj).symm
    rw [this]; exact le_trans card_image_le hinter
  rw [Finset.disjoint_left]
  intro e heA heB
  have hA := mem_filter.1 heA
  have hB := mem_filter.1 heB
  revert hA hB
  refine Sym2.inductionOn e fun xa xb hA hB => ?_
  have haA : xa ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 xa (Sym2.mem_mk_left xa xb)
  have hbA : xb ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 xb (Sym2.mem_mk_right xa xb)
  have haB : xa ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 xa (Sym2.mem_mk_left xa xb)
  have hbB : xb ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 xb (Sym2.mem_mk_right xa xb)
  have hab : xa ≠ xb := fun eq => hA.2 (by simpa [Sym2.mk_isDiag_iff] using eq)
  have hsub : ({xa, xb} : Finset V) ⊆ mapTri f s0 ∩ mapTri f t0 := by
    intro t ht; simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [haA, hbA, haB, hbB]
  have : 2 ≤ (mapTri f s0 ∩ mapTri f t0).card :=
    (card_le_card hsub).trans' (by simp [card_insert_of_notMem, hab])
  omega

lemma packing53E_aw_disjoint (u v x y z w a a' b b' : V)
    (hinj : Function.Injective (labels10 u v x y z w a a' b b')) :
    ∀ σ ∈ packing53E u v x y z w a a' w b,
      ∀ τ ∈ packing53E u v x y z w a a' w b,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  let f := labels10 u v x y z w a a' b b'
  intro σ hs τ ht hst
  rw [← packing53E_aw_image u v x y z w a a' b b'] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  have hs0t0 : s0 ≠ t0 := fun h => by subst h; exact hst rfl
  have hinter := packing10_53E_aw_pairwise s0 hs0 t0 ht0 hs0t0
  have hinter' : (mapTri f s0 ∩ mapTri f t0).card ≤ 1 := by
    have : mapTri f s0 ∩ mapTri f t0 = (s0 ∩ t0).image f := by
      simp only [mapTri]; exact (Finset.image_inter s0 t0 hinj).symm
    rw [this]; exact le_trans card_image_le hinter
  rw [Finset.disjoint_left]
  intro e heA heB
  have hA := mem_filter.1 heA
  have hB := mem_filter.1 heB
  revert hA hB
  refine Sym2.inductionOn e fun xa xb hA hB => ?_
  have haA : xa ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 xa (Sym2.mem_mk_left xa xb)
  have hbA : xb ∈ mapTri f s0 := Finset.mem_sym2_iff.1 hA.1 xb (Sym2.mem_mk_right xa xb)
  have haB : xa ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 xa (Sym2.mem_mk_left xa xb)
  have hbB : xb ∈ mapTri f t0 := Finset.mem_sym2_iff.1 hB.1 xb (Sym2.mem_mk_right xa xb)
  have hab : xa ≠ xb := fun eq => hA.2 (by simpa [Sym2.mk_isDiag_iff] using eq)
  have hsub : ({xa, xb} : Finset V) ⊆ mapTri f s0 ∩ mapTri f t0 := by
    intro t ht; simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [haA, hbA, haB, hbB]
  have : 2 ≤ (mapTri f s0 ∩ mapTri f t0).card :=
    (card_le_card hsub).trans' (by simp [card_insert_of_notMem, hab])
  omega

/-- **Proposition 5.3 (E)**, labelled. -/
theorem k4_certificate_E (H : HubConfig G)
    (x y z w a a' b b' : V)
    (hC : H.C = {x, y, z, w})
    (hA : H.A = {a, a'}) (hB : H.B = {b, b'})
    (hneA : a ≠ a') (hneB : b ≠ b')
    (hK4 : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w)
    (hax : G.Adj x a) (hay : G.Adj y a)
    (haz : G.Adj z a') (haw : G.Adj w a')
    (hbx : G.Adj x b) (hby : G.Adj y b)
    (hbz : G.Adj z b') (hbw : G.Adj w b')
    (hαfib : ∀ c ∈ H.C, G.Adj c a → c = x ∨ c = y)
    (hαfib' : ∀ c ∈ H.C, G.Adj c a' → c = z ∨ c = w)
    (hβfib : ∀ c ∈ H.C, G.Adj c b → c = x ∨ c = y)
    (hβfib' : ∀ c ∈ H.C, G.Adj c b' → c = z ∨ c = w)
    (h10 : ({H.u, H.v, x, y, z, w, a, a', b, b'} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y z w a a' b b' h10
  let d : V := if G.Adj a a' then a else w
  have had : G.Adj a' d := by
    by_cases h : G.Adj a a'
    · simpa [d, h] using h.symm
    · simpa [d, h] using haw.symm
  let S := packing53E H.u H.v x y z w a a' d b
  let X := cover53E H.u H.v x y z w a a' d b b'
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uz : G.Adj H.u z := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uw : G.Adj H.u w := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ua' : G.Adj H.u a' := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vz : G.Adj H.v z := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vw : G.Adj H.v w := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vb : G.Adj H.v b := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vb' : G.Adj H.v b' := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have hdist := core4_distinct G H hC
  have ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := hdist
  have not_u_C : H.u ∉ H.C := H.huB.2
  have not_u_A : H.u ∉ H.A := by
    intro h
    have : H.u ∈ G.neighborFinset H.u := by
      rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ h)
    exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
  have c3 {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
      ({p, q, r} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hpq, hpr]),
      card_insert_of_notMem (by simp [hqr]), card_singleton]
  have c_axy : ({a, x, y} : Finset V).card = 3 :=
    c3 (ne_core_priv G H (by rw [hC]; simp) (by rw [hA]; simp)).symm
      (ne_core_priv G H (by rw [hC]; simp) (by rw [hA]; simp)).symm hxy
  have c_uvx : ({H.u, H.v, x} : Finset V).card = 3 :=
    c3 (fun eq => G.irrefl (eq ▸ H.huv))
      (fun eq => not_u_C (by rw [hC, eq]; simp))
      (ne_z_of_core G H (by rw [hC]; simp))
  have c_uyz : ({H.u, y, z} : Finset V).card = 3 :=
    c3 (fun eq => not_u_C (by rw [hC, eq]; simp))
      (fun eq => not_u_C (by rw [hC, eq]; simp)) hyz
  have c_vyb : ({H.v, y, b} : Finset V).card = 3 :=
    c3 (ne_z_of_core G H (by rw [hC]; simp))
      (fun eq => by
        have : H.v ∈ G.neighborFinset H.v := by rw [H.hNv, hB, eq]; simp
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this))
      (fun h => Finset.disjoint_left.1 H.hBdisj (by simp [hB] : b ∈ H.B)
        (by rw [← h]; simp [hC] : b ∈ H.C))
  have c_vzw : ({H.v, z, w} : Finset V).card = 3 :=
    c3 (ne_z_of_core G H (by rw [hC]; simp))
      (ne_z_of_core G H (by rw [hC]; simp)) hzw
  -- d-dependent card for {u,a',d}
  have c_uad : ({H.u, a', d} : Finset V).card = 3 := by
    by_cases h : G.Adj a a'
    · have hd : d = a := by simp [d, h]
      rw [hd]
      exact c3 (fun eq => not_u_A (by rw [hA, eq]; simp))
        (fun eq => not_u_A (by rw [hA, eq]; simp)) hneA.symm
    · have hd : d = w := by simp [d, h]
      rw [hd]
      exact c3 (fun eq => not_u_A (by rw [hA, eq]; simp))
        (fun eq => not_u_C (by rw [hC, eq]; simp))
        (ne_core_priv G H (by rw [hC]; simp) (by rw [hA]; simp)).symm
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [S, packing53E, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact is3clique_of_adj G hax.symm hay.symm hK4.1 c_axy
      · exact is3clique_of_adj G uvs ux vx c_uvx
      · exact is3clique_of_adj G uy uz hK4.2.2.2.1 c_uyz
      · -- {u,a',d}
        have had' : G.Adj H.u d := by
          by_cases h : G.Adj a a'
          · have hd : d = a := by simp [d, h]
            simpa [hd] using ua
          · have hd : d = w := by simp [d, h]
            simpa [hd] using uw
        exact is3clique_of_adj G ua' had' had c_uad
      · exact is3clique_of_adj G vy vb hby c_vyb
      · exact is3clique_of_adj G vz vw hK4.2.2.2.2.2 c_vzw
    · -- disjoint
      by_cases h : G.Adj a a'
      · have hd : d = a := by simp [d, h]
        simp only [S, hd]
        exact packing53E_aa_disjoint H.u H.v x y z w a a' b b' hinj
      · have hd : d = w := by simp [d, h]
        simp only [S, hd]
        exact packing53E_aw_disjoint H.u H.v x y z w a a' b b' hinj
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, cover53E, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hax.symm
    · subst h; exact (mem_edgeFinset).2 hay.symm
    · subst h; exact (mem_edgeFinset).2 hK4.1
    · subst h; exact (mem_edgeFinset).2 hK4.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 had
    · subst h; exact (mem_edgeFinset).2 hby
    · subst h; exact (mem_edgeFinset).2 hK4.2.2.2.2.2
    · subst h; exact (mem_edgeFinset).2 uz
    · subst h; exact (mem_edgeFinset).2 uw
    · subst h; exact (mem_edgeFinset).2 vx
    · subst h; exact (mem_edgeFinset).2 vy
    · subst h; exact (mem_edgeFinset).2 vb'
  have hsize : X.card ≤ 2 * S.card := by
    by_cases h : G.Adj a a'
    · have hd : d = a := by simp [d, h]
      have hS : S.card = 6 := by simp [S, hd]; exact packing53E_aa_card _ _ _ _ _ _ _ _ _ _ hinj
      have hX : X.card = 12 := by simp [X, hd]; exact cover53E_aa_card _ _ _ _ _ _ _ _ _ _ hinj
      omega
    · have hd : d = w := by simp [d, h]
      have hS : S.card = 6 := by simp [S, hd]; exact packing53E_aw_card _ _ _ _ _ _ _ _ _ _ hinj
      have hX : X.card = 12 := by simp [X, hd]; exact cover53E_aw_card _ _ _ _ _ _ _ _ _ _ hinj
      omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packing53E, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have heq := triEdges_eq_of_card3 c_axy
      rw [heq] at he
      simp only [mem_insert, mem_singleton] at he
      rcases he with h | h | h <;> simp [X, cover53E, h]
    · have : False := by
        have heq := triEdges_eq_of_card3 c_uvx
        rw [heq] at he
        simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hu (by simp)
        · exact hu (by simp)
        · exact hv (by simp)
      exact this.elim
    · have h := triEdges_omit_vertex c_uyz he hu; rw [h]; simp [X, cover53E]
    · have h := triEdges_omit_vertex c_uad he hu; rw [h]; simp [X, cover53E]
    · have h := triEdges_omit_vertex c_vyb he hv; rw [h]; simp [X, cover53E]
    · have h := triEdges_omit_vertex c_vzw he hv; rw [h]; simp [X, cover53E]
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core4 (p : V) (hp : p ∈ H.C) : p = x ∨ p = y ∨ p = z ∨ p = w := by
      simpa [hC] using hp
    have not_A_adj_v (p : V) (hpA : p ∈ H.A) (hvadj : G.Adj H.v p) : False := by
      have hpN : p ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hvadj
      have hin : p ∈ insert H.u (H.C ∪ H.B) := by rwa [H.hNv] at hpN
      have huA : H.u ∉ H.A := by
        intro h
        have : H.u ∈ G.neighborFinset H.u := by
          rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ h)
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
      have hpCB : p ∈ H.C ∪ H.B := (mem_insert.1 hin).resolve_left (fun eq => huA (eq ▸ hpA))
      rcases mem_union.1 hpCB with hpC | hpB
      · exact Finset.disjoint_left.1 H.hAdisj hpA hpC
      · exact Finset.disjoint_left.1 H.hABdisj hpA hpB
    have not_B_adj_u (p : V) (hpB : p ∈ H.B) (huadj : G.Adj H.u p) : False := by
      have hpN : p ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 huadj
      have : p ∈ insert H.v (H.C ∪ H.A) := by rwa [H.hNu] at hpN
      have hvA : H.v ∉ H.B := by
        intro h
        have : H.v ∈ G.neighborFinset H.v := by
          rw [H.hNv]; exact mem_insert_of_mem (mem_union_right _ h)
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
      have hpne : p ≠ H.v := fun eq => hvA (eq ▸ hpB)
      have hpCA : p ∈ H.C ∪ H.A := (mem_insert.1 this).resolve_left hpne
      rcases mem_union.1 hpCA with hpC | hpA
      · exact Finset.disjoint_left.1 H.hBdisj hpB hpC
      · exact Finset.disjoint_left.1 H.hABdisj hpA hpB
    rcases hhub with rfl | rfl
    · -- hub = u
      have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv
        have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hpxy.symm
        rcases mem_union.1 hyCA with hyC | hyA
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (by simp [X, cover53E]) (hpy ▸ him_rim)
          · exact meet s(H.v, y) (by simp [X, cover53E]) (hpy ▸ him_rim)
          · exact meet s(H.u, z) (by simp [X, cover53E]) (hpy ▸ him_zy)
          · exact meet s(H.u, w) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact False.elim (not_A_adj_v py hyA hxyAdj)
      by_cases hyv : py = H.v
      · subst hyv
        have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hpxy
        have hrim' : s(H.v, px) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_rim
        rcases mem_union.1 hxCA with hxC | hxA
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (by simp [X, cover53E]) (hpx ▸ hrim')
          · exact meet s(H.v, y) (by simp [X, cover53E]) (hpx ▸ hrim')
          · exact meet s(H.u, z) (by simp [X, cover53E]) (hpx ▸ him_zx)
          · exact meet s(H.u, w) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact False.elim (not_A_adj_v px hxA hxyAdj.symm)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxA : px ∈ H.A
      · have hpa : px = a ∨ px = a' := by simpa [hA] using hxA
        rcases hpa with hpxa | hpxa
        · by_cases hyA : py ∈ H.A
          · have : py = a ∨ py = a' := by simpa [hA] using hyA
            rcases this with hpya | hpya
            · exact absurd (hpxa.trans hpya.symm) hpxy
            · by_cases haa : G.Adj a a'
              · have hd : d = a := by simp [d, haa]
                have hr : s(a, a') ∈ triEdges t := by simpa [hpxa, hpya] using him_rim
                exact meet s(a', d) (by simp [X, cover53E]) (by
                  simpa [hd, Sym2.eq_swap] using hr)
              · exact absurd (by simpa [hpxa, hpya] using hxyAdj) haa
          · have hyC : py ∈ H.C := (mem_union.1 hyCA).resolve_right hyA
            have hadj' : G.Adj a py := by rwa [hpxa] at hxyAdj
            rcases hαfib py hyC hadj'.symm with hpy | hpy
            · have hr : s(a, x) ∈ triEdges t := by
                simpa [hpxa, hpy, Sym2.eq_swap] using him_rim
              exact meet s(a, x) (by simp [X, cover53E]) hr
            · have hr : s(a, y) ∈ triEdges t := by
                simpa [hpxa, hpy, Sym2.eq_swap] using him_rim
              exact meet s(a, y) (by simp [X, cover53E]) hr
        · -- px = a'
          by_cases hyA : py ∈ H.A
          · have : py = a ∨ py = a' := by simpa [hA] using hyA
            rcases this with hpya | hpya
            · by_cases haa : G.Adj a a'
              · have hd : d = a := by simp [d, haa]
                have hr : s(a', a) ∈ triEdges t := by simpa [hpxa, hpya] using him_rim
                exact meet s(a', d) (by simp [X, cover53E]) (by simpa [hd] using hr)
              · exact absurd (by simpa [hpxa, hpya] using hxyAdj.symm) haa
            · exact absurd (hpxa.trans hpya.symm) hpxy
          · have hyC : py ∈ H.C := (mem_union.1 hyCA).resolve_right hyA
            have hadj' : G.Adj a' py := by rwa [hpxa] at hxyAdj
            rcases hαfib' py hyC hadj'.symm with hpy | hpy
            · exact meet s(H.u, z) (by simp [X, cover53E]) (hpy ▸ him_zy)
            · exact meet s(H.u, w) (by simp [X, cover53E]) (hpy ▸ him_zy)
      by_cases hyA : py ∈ H.A
      · have hpa : py = a ∨ py = a' := by simpa [hA] using hyA
        rcases hpa with hpya | hpya
        · have hxC : px ∈ H.C := (mem_union.1 hxCA).resolve_right hxA
          have hadj' : G.Adj px a := by rwa [hpya] at hxyAdj
          rcases hαfib px hxC hadj' with hpx | hpx
          · have hr : s(a, x) ∈ triEdges t := by simpa [hpx, hpya, Sym2.eq_swap] using him_rim
            exact meet s(a, x) (by simp [X, cover53E]) hr
          · have hr : s(a, y) ∈ triEdges t := by simpa [hpx, hpya, Sym2.eq_swap] using him_rim
            exact meet s(a, y) (by simp [X, cover53E]) hr
        · have hxC : px ∈ H.C := (mem_union.1 hxCA).resolve_right hxA
          have hadj' : G.Adj px a' := by rwa [hpya] at hxyAdj
          rcases hαfib' px hxC hadj' with hpx | hpx
          · exact meet s(H.u, z) (by simp [X, cover53E]) (hpx ▸ him_zx)
          · exact meet s(H.u, w) (by simp [X, cover53E]) (hpx ▸ him_zx)
      · have hxC : px ∈ H.C := (mem_union.1 hxCA).resolve_right hxA
        have hyC : py ∈ H.C := (mem_union.1 hyCA).resolve_right hyA
        rcases core4 px hxC with hpx | hpx | hpx | hpx <;>
          rcases core4 py hyC with hpy | hpy | hpy | hpy
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(x, y) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.u, z) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(H.u, w) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(x, y) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(y, z) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.u, w) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(H.u, z) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(y, z) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(z, w) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.u, w) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(H.u, w) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(z, w) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
    · -- hub = v
      have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hpxy.symm
        have hrim' : s(H.u, py) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_rim
        rcases mem_union.1 hyCB with hyC | hyB
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (by simp [X, cover53E]) (hpy ▸ him_zy)
          · exact meet s(H.v, y) (by simp [X, cover53E]) (hpy ▸ him_zy)
          · exact meet s(H.u, z) (by simp [X, cover53E]) (hpy ▸ hrim')
          · exact meet s(H.u, w) (by simp [X, cover53E]) (hpy ▸ hrim')
        · exact False.elim (not_B_adj_u py hyB hxyAdj)
      by_cases hyu : py = H.u
      · subst hyu
        have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hpxy
        have hrim' : s(H.u, px) ∈ triEdges t := by simpa [Sym2.eq_swap] using him_rim
        rcases mem_union.1 hxCB with hxC | hxB
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (by simp [X, cover53E]) (hpx ▸ him_zx)
          · exact meet s(H.v, y) (by simp [X, cover53E]) (hpx ▸ him_zx)
          · exact meet s(H.u, z) (by simp [X, cover53E]) (hpx ▸ hrim')
          · exact meet s(H.u, w) (by simp [X, cover53E]) (hpx ▸ hrim')
        · exact False.elim (not_B_adj_u px hxB hxyAdj.symm)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxB : px ∈ H.B
      · have hpb : px = b ∨ px = b' := by simpa [hB] using hxB
        rcases hpb with hpxb | hpxb
        · by_cases hyB : py ∈ H.B
          · have : py = b ∨ py = b' := by simpa [hB] using hyB
            rcases this with hpyb | hpyb
            · exact absurd (hpxb.trans hpyb.symm) hpxy
            · exact meet s(H.v, b') (by simp [X, cover53E]) (hpyb ▸ him_zy)
          · have hyC : py ∈ H.C := (mem_union.1 hyCB).resolve_right hyB
            have hadj' : G.Adj b py := by rwa [hpxb] at hxyAdj
            rcases hβfib py hyC hadj'.symm with hpy | hpy
            · exact meet s(H.v, x) (by simp [X, cover53E]) (hpy ▸ him_zy)
            · have hr : s(y, b) ∈ triEdges t := by
                simpa [hpxb, hpy, Sym2.eq_swap] using him_rim
              exact meet s(y, b) (by simp [X, cover53E]) hr
        · by_cases hyB : py ∈ H.B
          · have : py = b ∨ py = b' := by simpa [hB] using hyB
            rcases this with hpyb | hpyb
            · exact meet s(H.v, b') (by simp [X, cover53E]) (hpxb ▸ him_zx)
            · exact absurd (hpxb.trans hpyb.symm) hpxy
          · exact meet s(H.v, b') (by simp [X, cover53E]) (hpxb ▸ him_zx)
      by_cases hyB : py ∈ H.B
      · have hpb : py = b ∨ py = b' := by simpa [hB] using hyB
        rcases hpb with hpyb | hpyb
        · have hxC : px ∈ H.C := (mem_union.1 hxCB).resolve_right hxB
          have hadj' : G.Adj px b := by rwa [hpyb] at hxyAdj
          rcases hβfib px hxC hadj' with hpx | hpx
          · exact meet s(H.v, x) (by simp [X, cover53E]) (hpx ▸ him_zx)
          · have hr : s(y, b) ∈ triEdges t := by simpa [hpx, hpyb, Sym2.eq_swap] using him_rim
            exact meet s(y, b) (by simp [X, cover53E]) hr
        · exact meet s(H.v, b') (by simp [X, cover53E]) (hpyb ▸ him_zy)
      · have hxC : px ∈ H.C := (mem_union.1 hxCB).resolve_right hxB
        have hyC : py ∈ H.C := (mem_union.1 hyCB).resolve_right hyB
        rcases core4 px hxC with hpx | hpx | hpx | hpx <;>
          rcases core4 py hyC with hpy | hpy | hpy | hpy
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(x, y) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.v, x) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(H.v, x) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(x, y) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(y, z) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.v, y) (by simp [X, cover53E]) (hpx ▸ him_zx)
        · exact meet s(H.v, x) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(y, z) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
        · exact meet s(z, w) (by simp [X, cover53E]) (by simpa [hpx, hpy] using him_rim)
        · exact meet s(H.v, x) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(H.v, y) (by simp [X, cover53E]) (hpy ▸ him_zy)
        · exact meet s(z, w) (by simp [X, cover53E]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (hpx.trans hpy.symm) hpxy
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩

/-- From Lemma 5.1 + (A2): each core vertex has unique A- and B-neighbors. -/
theorem k4_unique_attach (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y z w : V} (hC : H.C = {x, y, z, w})
    (hK4 : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w) :
    (∀ c ∈ H.C, ∃! a, a ∈ H.A ∧ G.Adj c a) ∧
    (∀ c ∈ H.C, ∃! b, b ∈ H.B ∧ G.Adj c b) := by
  classical
  have hfwd := lemma51 G H hA1.1 hA1.2.1 x y z w hC hK4
  have hbwd := lemma51 G (H.swap) hA1.2.2.1 hA1.2.2.2 x y z w
    (by simpa [HubConfig.swap] using hC) hK4
  have coreDeg3 : ∀ c ∈ H.C, H.coreDeg c = 3 := by
    intro c hc
    unfold HubConfig.coreDeg
    have hc' : c ∈ ({x, y, z, w} : Finset V) := by rwa [← hC]
    have hadj_all : ∀ t ∈ H.C.erase c, G.Adj c t := by
      intro t ht
      have htC : t ∈ H.C := (mem_erase.1 ht).2
      have hne : t ≠ c := (mem_erase.1 ht).1
      have ht' : t ∈ ({x, y, z, w} : Finset V) := by rwa [← hC]
      simp only [mem_insert, mem_singleton] at hc' ht'
      -- all six K4 edges
      rcases hc' with rfl | rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl | rfl
      · exact absurd rfl hne.symm
      · exact hK4.1
      · exact hK4.2.1
      · exact hK4.2.2.1
      · exact hK4.1.symm
      · exact absurd rfl hne.symm
      · exact hK4.2.2.2.1
      · exact hK4.2.2.2.2.1
      · exact hK4.2.1.symm
      · exact hK4.2.2.2.1.symm
      · exact absurd rfl hne.symm
      · exact hK4.2.2.2.2.2
      · exact hK4.2.2.1.symm
      · exact hK4.2.2.2.2.1.symm
      · exact hK4.2.2.2.2.2.symm
      · exact absurd rfl hne.symm
    have hfilter : (H.C.erase c).filter (G.Adj c) = H.C.erase c := by
      ext t; simp only [mem_filter]; constructor
      · exact And.left
      · intro ht; exact ⟨ht, hadj_all t ht⟩
    rw [hfilter, card_erase_of_mem hc, H.hCcard]
  have uniqA : ∀ c ∈ H.C, ∃! a, a ∈ H.A ∧ G.Adj c a := by
    intro c hc
    have hne : (G.neighborFinset c ∩ H.A).Nonempty := hfwd c hc
    have hneB : (G.neighborFinset c ∩ H.B).Nonempty := by
      -- swap.A = B
      simpa [HubConfig.swap] using hbwd c hc
    have hA2c := hA2 c hc
    have hde := coreDeg3 c hc
    have hAcard : (G.neighborFinset c ∩ H.A).card = 1 := by
      have hApos : 1 ≤ (G.neighborFinset c ∩ H.A).card := Finset.card_pos.2 hne
      have hBpos : 1 ≤ (G.neighborFinset c ∩ H.B).card := Finset.card_pos.2 hneB
      omega
    obtain ⟨a, ha⟩ := (card_eq_one (s := G.neighborFinset c ∩ H.A)).1 hAcard
    refine ⟨a, ?_, ?_⟩
    · have : a ∈ G.neighborFinset c ∩ H.A := by simp [ha]
      exact ⟨(mem_inter.1 this).2, (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1⟩
    · intro a' ⟨ha'A, hadj⟩
      have : a' ∈ G.neighborFinset c ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, ha'A⟩
      simpa [ha] using this
  have uniqB : ∀ c ∈ H.C, ∃! b, b ∈ H.B ∧ G.Adj c b := by
    intro c hc
    have hne : (G.neighborFinset c ∩ H.B).Nonempty := by
      simpa [HubConfig.swap] using hbwd c hc
    have hneA : (G.neighborFinset c ∩ H.A).Nonempty := hfwd c hc
    have hA2c := hA2 c hc
    have hde := coreDeg3 c hc
    have hBcard : (G.neighborFinset c ∩ H.B).card = 1 := by
      have hApos : 1 ≤ (G.neighborFinset c ∩ H.A).card := Finset.card_pos.2 hneA
      have hBpos : 1 ≤ (G.neighborFinset c ∩ H.B).card := Finset.card_pos.2 hne
      omega
    obtain ⟨b, hb⟩ := (card_eq_one (s := G.neighborFinset c ∩ H.B)).1 hBcard
    refine ⟨b, ?_, ?_⟩
    · have : b ∈ G.neighborFinset c ∩ H.B := by simp [hb]
      exact ⟨(mem_inter.1 this).2, (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1⟩
    · intro b' ⟨hb'B, hadj⟩
      have : b' ∈ G.neighborFinset c ∩ H.B :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hb'B⟩
      simpa [hb] using this
  exact ⟨uniqA, uniqB⟩

/-- K₄ core reducible under (A1)–(A2). -/
theorem k4_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y z w : V} (hC : H.C = {x, y, z, w})
    (hK4 : G.Adj x y ∧ G.Adj x z ∧ G.Adj x w ∧ G.Adj y z ∧ G.Adj y w ∧ G.Adj z w) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨uniqA, uniqB⟩ := k4_unique_attach G H hA1 hA2 hC hK4
  let α : V → V := fun c => if hc : c ∈ H.C then Classical.choose (ExistsUnique.exists (uniqA c hc)) else c
  let β : V → V := fun c => if hc : c ∈ H.C then Classical.choose (ExistsUnique.exists (uniqB c hc)) else c
  have hα : ∀ c ∈ H.C, α c ∈ H.A ∧ G.Adj c (α c) := by
    intro c hc
    simpa [α, hc] using Classical.choose_spec (ExistsUnique.exists (uniqA c hc))
  have hβ : ∀ c ∈ H.C, β c ∈ H.B ∧ G.Adj c (β c) := by
    intro c hc
    simpa [β, hc] using Classical.choose_spec (ExistsUnique.exists (uniqB c hc))
  have hαA : ∀ c ∈ H.C, α c ∈ H.A := fun c hc => (hα c hc).1
  have hβB : ∀ c ∈ H.C, β c ∈ H.B := fun c hc => (hβ c hc).1
  have k4_of {x' y' z' w' : V} (hC' : H.C = {x', y', z', w'}) :
      G.Adj x' y' ∧ G.Adj x' z' ∧ G.Adj x' w' ∧
        G.Adj y' z' ∧ G.Adj y' w' ∧ G.Adj z' w' := by
    have d := core4_distinct G H hC'
    have adj (p q : V) (hp : p ∈ ({x, y, z, w} : Finset V))
        (hq : q ∈ ({x, y, z, w} : Finset V)) (hne : p ≠ q) : G.Adj p q := by
      simp only [mem_insert, mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
      · exact absurd rfl hne
      · exact hK4.1
      · exact hK4.2.1
      · exact hK4.2.2.1
      · exact hK4.1.symm
      · exact absurd rfl hne
      · exact hK4.2.2.2.1
      · exact hK4.2.2.2.2.1
      · exact hK4.2.1.symm
      · exact hK4.2.2.2.1.symm
      · exact absurd rfl hne
      · exact hK4.2.2.2.2.2
      · exact hK4.2.2.1.symm
      · exact hK4.2.2.2.2.1.symm
      · exact hK4.2.2.2.2.2.symm
      · exact absurd rfl hne
    refine ⟨adj x' y' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.1,
      adj x' z' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.2.1,
      adj x' w' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.2.2.1,
      adj y' z' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.2.2.2.1,
      adj y' w' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.2.2.2.2.1,
      adj z' w' (by rw [← hC, hC']; simp) (by rw [← hC, hC']; simp) d.2.2.2.2.2⟩
  have α_eq (c : V) (hc : c ∈ H.C) {a0 : V}
      (ha0 : a0 ∈ H.A) (hadj : G.Adj c a0) : α c = a0 :=
    (ExistsUnique.unique (uniqA c hc) (hα c hc) ⟨ha0, hadj⟩)
  have β_eq (c : V) (hc : c ∈ H.C) {b0 : V}
      (hb0 : b0 ∈ H.B) (hadj : G.Adj c b0) : β c = b0 :=
    (ExistsUnique.unique (uniqB c hc) (hβ c hc) ⟨hb0, hadj⟩)
  rcases lemma52 (C := H.C) (A := H.A) (B := H.B) H.hCcard H.hA H.hB α β hαA hβB with hG | hE
  · obtain ⟨x', y', z', w', a_, b_, hC', ha_, hb_, hαG, hβG⟩ := hG
    obtain ⟨aPlus, haP, hneA⟩ : ∃ aPlus, H.A = {a_, aPlus} ∧ a_ ≠ aPlus := by
      obtain ⟨p, q, hpq, hAeq⟩ := (card_eq_two (s := H.A)).1 H.hA
      rcases (by simpa [hAeq] using ha_ : a_ = p ∨ a_ = q) with rfl | rfl
      · exact ⟨q, hAeq, hpq⟩
      · exact ⟨p, by simpa [Finset.pair_comm] using hAeq, hpq.symm⟩
    obtain ⟨bPlus, hbP, hneB⟩ : ∃ bPlus, H.B = {b_, bPlus} ∧ b_ ≠ bPlus := by
      obtain ⟨p, q, hpq, hBeq⟩ := (card_eq_two (s := H.B)).1 H.hB
      rcases (by simpa [hBeq] using hb_ : b_ = p ∨ b_ = q) with rfl | rfl
      · exact ⟨q, hBeq, hpq⟩
      · exact ⟨p, by simpa [Finset.pair_comm] using hBeq, hpq.symm⟩
    have hC4' : ({x', y', z', w'} : Finset V).card = 4 := by rw [← hC']; exact H.hCcard
    have h10 := labels10_of_hub G H hC' haP hbP hC4' hneA hneB
    have hK4' := k4_of hC'
    have hzC : z' ∈ H.C := by rw [hC']; simp
    have hyC : y' ∈ H.C := by rw [hC']; simp
    have ha_A : a_ ∈ H.A := by simp [haP]
    have hb_B : b_ ∈ H.B := by simp [hbP]
    let αz := α z'
    let βy := β y'
    have hαz : αz = a_ ∨ αz = aPlus := by
      have : αz ∈ H.A := hαA z' hzC
      simpa [haP, αz] using this
    have hβy : βy = b_ ∨ βy = bPlus := by
      have : βy ∈ H.B := hβB y' hyC
      simpa [hbP, βy] using this
    have hzα : G.Adj z' αz := (hα z' hzC).2
    have hyβ : G.Adj y' βy := (hβ y' hyC).2
    have hαz_of : G.Adj z' a_ → αz = a_ := fun hadj =>
      α_eq z' hzC ha_A hadj
    have hβy_of : G.Adj y' b_ → βy = b_ := fun hadj =>
      β_eq y' hyC hb_B hadj
    exact k4_certificate_G G H x' y' z' w' a_ aPlus b_ bPlus αz βy
      hC' haP hbP hK4' hαz hβy hzα hyβ hαz_of hβy_of
      (fun c hc hadj => hαG c hc (α_eq c hc ha_A hadj))
      (fun c hc hadj => hβG c hc (β_eq c hc hb_B hadj)) h10
  · obtain ⟨x', y', z', w', a, a', b, b', hC', hA', hB', hneA, hneB,
        hαx, hαy, hαz, hαw, hβx, hβy, hβz, hβw⟩ := hE
    have hC4E : ({x', y', z', w'} : Finset V).card = 4 := by rw [← hC']; exact H.hCcard
    have h10 := labels10_of_hub G H hC' hA' hB' hC4E hneA hneB
    have hK4' := k4_of hC'
    have memA_a : a ∈ H.A := by simp [hA']
    have memA_a' : a' ∈ H.A := by simp [hA']
    have memB_b : b ∈ H.B := by simp [hB']
    have memB_b' : b' ∈ H.B := by simp [hB']
    have hxC : x' ∈ H.C := by rw [hC']; simp
    have hyC : y' ∈ H.C := by rw [hC']; simp
    have hzC : z' ∈ H.C := by rw [hC']; simp
    have hwC : w' ∈ H.C := by rw [hC']; simp
    exact k4_certificate_E G H x' y' z' w' a a' b b' hC' hA' hB' hneA hneB hK4'
      (by have := (hα x' hxC).2; rwa [hαx] at this)
      (by have := (hα y' hyC).2; rwa [hαy] at this)
      (by have := (hα z' hzC).2; rwa [hαz] at this)
      (by have := (hα w' hwC).2; rwa [hαw] at this)
      (by have := (hβ x' hxC).2; rwa [hβx] at this)
      (by have := (hβ y' hyC).2; rwa [hβy] at this)
      (by have := (hβ z' hzC).2; rwa [hβz] at this)
      (by have := (hβ w' hwC).2; rwa [hβw] at this)
      (fun c hc hadj => by
        have hαc := α_eq c hc memA_a hadj
        have : c = x' ∨ c = y' ∨ c = z' ∨ c = w' := by simpa [hC'] using hc
        rcases this with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hneA.symm (hαz.symm.trans hαc))
        · exact False.elim (hneA.symm (hαw.symm.trans hαc)))
      (fun c hc hadj => by
        have hαc := α_eq c hc memA_a' hadj
        have : c = x' ∨ c = y' ∨ c = z' ∨ c = w' := by simpa [hC'] using hc
        rcases this with rfl | rfl | rfl | rfl
        · exact False.elim (hneA (hαx.symm.trans hαc))
        · exact False.elim (hneA (hαy.symm.trans hαc))
        · exact Or.inl rfl
        · exact Or.inr rfl)
      (fun c hc hadj => by
        have hβc := β_eq c hc memB_b hadj
        have : c = x' ∨ c = y' ∨ c = z' ∨ c = w' := by simpa [hC'] using hc
        rcases this with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hneB.symm (hβz.symm.trans hβc))
        · exact False.elim (hneB.symm (hβw.symm.trans hβc)))
      (fun c hc hadj => by
        have hβc := β_eq c hc memB_b' hadj
        have : c = x' ∨ c = y' ∨ c = z' ∨ c = w' := by simpa [hC'] using hc
        rcases this with rfl | rfl | rfl | rfl
        · exact False.elim (hneB (hβx.symm.trans hβc))
        · exact False.elim (hneB (hβy.symm.trans hβc))
        · exact Or.inl rfl
        · exact Or.inr rfl)
      h10



/-! ### §6 denser cores: diamond, C₄, paw, K₃+K₁ -/

/-- Edges with both ends outside `Q = {q1,q2,q3}` in a matching-core link are
`s(v,t)` or the private edge (Lemma 6.1 setup). -/
lemma lemma61_outside (H : HubConfig G)
    (t q1 q2 q3 d0 d1 : V) (hC : H.C = {t, q1, q2, q3}) (hAeq : H.A = {d0, d1})
    (hnt : ∀ a ∈ H.A, ¬ G.Adj t a)
    {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
    (hOut : ∀ v ∈ e, v ∉ ({q1, q2, q3} : Finset V)) :
    e = s(H.v, t) ∨ e = s(d0, d1) := by
  classical
  revert he hOut
  refine Sym2.inductionOn e fun a b he hOut => ?_
  have hab : (linkGraph G H.u).Adj a b := (mem_edgeFinset (G := linkGraph G H.u)).1 he
  have hG : G.Adj a b := hab.2.2
  have cls (w : V) (htN : w ∈ G.neighborFinset H.u)
      (htO : w ∉ ({q1, q2, q3} : Finset V)) :
      w = H.v ∨ w = t ∨ w = d0 ∨ w = d1 := by
    rw [H.hNu] at htN
    simp only [mem_insert, mem_union, mem_singleton, not_or] at htN htO
    rcases htN with rfl | hCmem | hAmem
    · exact Or.inl rfl
    · have : w ∈ ({t, q1, q2, q3} : Finset V) := by rw [← hC]; exact hCmem
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl htO.1
      · exact absurd rfl htO.2.1
      · exact absurd rfl htO.2.2
    · have : w ∈ ({d0, d1} : Finset V) := by rw [← hAeq]; exact hAmem
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have ha := cls a hab.1 (hOut a (by simp))
  have hb := cls b hab.2.1 (hOut b (by simp))
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have not_v_priv {d : V} (hd : d ∈ H.A) : ¬ G.Adj H.v d := not_adj_hub_priv G H hd
  have not_t_priv {d : V} (hd : d ∈ H.A) : ¬ G.Adj t d := hnt d hd
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inl (by rw [ha, hb])
  · exact False.elim (not_v_priv hd0A (by rwa [ha, hb] at hG))
  · exact False.elim (not_v_priv hd1A (by rwa [ha, hb] at hG))
  · exact Or.inl (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact False.elim (not_t_priv hd0A (by rwa [ha, hb] at hG))
  · exact False.elim (not_t_priv hd1A (by rwa [ha, hb] at hG))
  · exact False.elim (not_v_priv hd0A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_t_priv hd0A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (hG.ne (ha.trans hb.symm))
  · exact Or.inr (by rw [ha, hb])
  · exact False.elim (not_v_priv hd1A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact False.elim (not_t_priv hd1A (by have h' := hG.symm; rwa [hb, ha] at h'))
  · exact Or.inr (by rw [ha, hb]; exact Sym2.eq_swap)
  · exact False.elim (hG.ne (ha.trans hb.symm))

/-- Core-neighbourhood of a private in `Q` is nonempty when `ab` is absent. -/
lemma lemma61_priv_N_in_Q (H : HubConfig G)
    (hconn : LinkConnected G H.u)
    {t q1 q2 q3 d0 d1 : V} (hC : H.C = {t, q1, q2, q3}) (hAeq : H.A = {d0, d1})
    (hnt : ∀ a ∈ H.A, ¬ G.Adj t a) (hpriv : ¬ G.Adj d0 d1)
    {d : V} (hdA : d ∈ H.A) :
    (G.neighborFinset d ∩ ({q1, q2, q3} : Finset V)).Nonempty := by
  classical
  have zd := ne_z_of_priv G H hdA
  obtain ⟨n, hn⟩ := link_nbr G H.u hconn (d := d) (w := H.v) zd.symm (by rw [H.hNu]; exact mem_insert_of_mem (mem_union_right _ hdA)) (opposite_hub_mem G H)
  have hGn : G.Adj d n := hn.2.2
  have hnN : n ∈ G.neighborFinset H.u := hn.2.1
  rw [H.hNu] at hnN
  simp only [mem_insert, mem_union] at hnN
  have hnQ : n ∈ ({q1, q2, q3} : Finset V) := by
    rcases hnN with rfl | hCm | hAm
    · exact False.elim (not_adj_hub_priv G H hdA hGn.symm)
    · have : n ∈ ({t, q1, q2, q3} : Finset V) := by rw [← hC]; exact hCm
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl
      · exact False.elim (hnt d hdA hGn.symm)
      · simp
      · simp
      · simp
    · have : n = d0 ∨ n = d1 := by rw [hAeq] at hAm; simpa using hAm
      have hd01' : d = d0 ∨ d = d1 := by simpa [hAeq] using hdA
      rcases this with rfl | rfl <;> rcases hd01' with rfl | rfl
      · exact False.elim (G.irrefl hGn)
      · exact False.elim (hpriv hGn.symm)
      · exact False.elim (hpriv hGn)
      · exact False.elim (G.irrefl hGn)
  exact ⟨n, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hGn, hnQ⟩⟩

/-- WKE witness when `t` misses `A`, given a matching edge in `Q` and the complementary
matching edge `t—q3` (Lemma 6.1). -/
theorem lemma61_wke (H : HubConfig G)
    (hconn : LinkConnected G H.u)
    {t q1 q2 q3 : V} (hC : H.C = {t, q1, q2, q3})
    (heQ : G.Adj q1 q2) (hmatch : G.Adj t q3)
    (hnt : ∀ a ∈ H.A, ¬ G.Adj t a)
    (hnot : ¬ IsWKE (linkGraph G H.u)) : False := by
  classical
  obtain ⟨d0, d1, hAeq, hd01, hd0N, hd1N⟩ := privates_of G H
  obtain ⟨htq1, htq2, htq3, hq12, hq13, hq23⟩ := core4_distinct G H hC
  have htC : t ∈ H.C := by rw [hC]; simp
  have hq1C : q1 ∈ H.C := by rw [hC]; simp
  have hq2C : q2 ∈ H.C := by rw [hC]; simp
  have hq3C : q3 ∈ H.C := by rw [hC]; simp
  have hzN := opposite_hub_mem G H
  have htN := core_mem_Nu G H htC
  have hq1N := core_mem_Nu G H hq1C
  have hq2N := core_mem_Nu G H hq2C
  have hq3N := core_mem_Nu G H hq3C
  have hzt := z_adj_core G H htC
  have hd0A : d0 ∈ H.A := by rw [hAeq]; simp
  have hd1A : d1 ∈ H.A := by rw [hAeq]; simp
  have zt := ne_z_of_core G H htC
  have z1 := ne_z_of_core G H hq1C
  have z2 := ne_z_of_core G H hq2C
  have z3 := ne_z_of_core G H hq3C
  have z0 := ne_z_of_priv G H hd0A
  have z1p := ne_z_of_priv G H hd1A
  have t0 := ne_core_priv G H htC hd0A
  have t1 := ne_core_priv G H htC hd1A
  have q10 := ne_core_priv G H hq1C hd0A
  have q11 := ne_core_priv G H hq1C hd1A
  have q20 := ne_core_priv G H hq2C hd0A
  have q21 := ne_core_priv G H hq2C hd1A
  have q30 := ne_core_priv G H hq3C hd0A
  have q31 := ne_core_priv G H hq3C hd1A
  have L {a b : V} (ha : a ∈ G.neighborFinset H.u) (hb : b ∈ G.neighborFinset H.u)
      (h : G.Adj a b) : (linkGraph G H.u).Adj a b := ⟨ha, hb, h⟩
  have hout {e : Sym2 V} (he : e ∈ (linkGraph G H.u).edgeFinset)
      (hO : ∀ v ∈ e, v ∉ ({q1, q2, q3} : Finset V)) :
      e = s(H.v, t) ∨ e = s(d0, d1) :=
    lemma61_outside G H t q1 q2 q3 d0 d1 hC hAeq hnt he hO
  by_cases hpriv : G.Adj d0 d1
  · exact hnot (wke3 (linkGraph G H.u) (q1 := q1) (q2 := q2) (q3 := q3)
      (L hzN htN hzt) (L hd0N hd1N hpriv) (L hq1N hq2N heQ)
      (by simp [List.nodup_cons, zt, z0, z1p, z1, z2, z3, t0, t1, htq1, htq2, htq3,
          q10, q11, q20, q21, q30, q31, hq12, hq13, hq23, hd01,
          zt.symm, z0.symm, z1p.symm, z1.symm, z2.symm, z3.symm,
          t0.symm, t1.symm, htq1.symm, htq2.symm, htq3.symm,
          q10.symm, q11.symm, q20.symm, q21.symm, q30.symm, q31.symm,
          hq12.symm, hq13.symm, hq23.symm, hd01.symm])
      (fun e he hO => by
        rcases hout he hO with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)))
  · let N0 := G.neighborFinset d0 ∩ ({q1, q2, q3} : Finset V)
    let N1 := G.neighborFinset d1 ∩ ({q1, q2, q3} : Finset V)
    have hN0 := lemma61_priv_N_in_Q G H hconn hC hAeq hnt hpriv hd0A
    have hN1 := lemma61_priv_N_in_Q G H hconn hC hAeq hnt hpriv hd1A
    -- Distinct representatives from N0, N1
    have hdist : ∃ n0 ∈ N0, ∃ n1 ∈ N1, n0 ≠ n1 := by
      obtain ⟨a0, ha0⟩ := hN0
      obtain ⟨a1, ha1⟩ := hN1
      by_cases hne : a0 ≠ a1
      · exact ⟨a0, ha0, a1, ha1, hne⟩
      · push_neg at hne; subst hne
        by_cases hex0 : ∃ m ∈ N0, m ≠ a0
        · obtain ⟨m, hm, hne⟩ := hex0
          exact ⟨m, hm, a0, ha1, hne⟩
        · by_cases hex1 : ∃ m ∈ N1, m ≠ a0
          · obtain ⟨m, hm, hne⟩ := hex1
            exact ⟨a0, ha0, m, hm, hne.symm⟩
          · -- same singleton {a0}: the other two verts in Q miss A → lemma32
            have N0eq : N0 = {a0} :=
              eq_singleton_iff_unique_mem.2 ⟨ha0, fun m hm => by
                by_contra hne; exact hex0 ⟨m, hm, hne⟩⟩
            have N1eq : N1 = {a0} :=
              eq_singleton_iff_unique_mem.2 ⟨ha1, fun m hm => by
                by_contra hne; exact hex1 ⟨m, hm, hne⟩⟩
            have ha0Q : a0 ∈ ({q1, q2, q3} : Finset V) := (mem_inter.1 ha0).2
            have hQ3 : ({q1, q2, q3} : Finset V).card = 3 := by
              rw [card_insert_of_notMem (by simp [hq12, hq13]),
                card_insert_of_notMem (by simp [hq23]), card_singleton]
            have hrest : (({q1, q2, q3} : Finset V).erase a0).card = 2 := by
              rw [card_erase_of_mem ha0Q, hQ3]
            obtain ⟨u1, u2, hu12, hU⟩ :=
              (card_eq_two (s := ({q1, q2, q3} : Finset V).erase a0)).1 hrest
            have hu1mem : u1 ∈ ({q1, q2, q3} : Finset V).erase a0 := by
              rw [hU]; exact mem_insert_self _ _
            have hu2mem : u2 ∈ ({q1, q2, q3} : Finset V).erase a0 := by
              rw [hU]; simp
            have hu1Q := (mem_erase.1 hu1mem).2
            have hu2Q := (mem_erase.1 hu2mem).2
            have hu1ne := (mem_erase.1 hu1mem).1
            have hu2ne := (mem_erase.1 hu2mem).1
            have miss (u : V) (huQ : u ∈ ({q1, q2, q3} : Finset V)) (hune : u ≠ a0) :
                ∀ a ∈ H.A, ¬ G.Adj u a := by
              intro a ha hadj
              have ha01 : a = d0 ∨ a = d1 := by simpa [hAeq] using ha
              have huIn : u ∈ G.neighborFinset a ∩ ({q1, q2, q3} : Finset V) :=
                mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj.symm, huQ⟩
              rcases ha01 with rfl | rfl
              · exact hune (by simpa [N0eq] using (show u ∈ N0 from huIn))
              · exact hune (by simpa [N1eq] using (show u ∈ N1 from huIn))
            have hQeq : ({q1, q2, q3} : Finset V) = {a0, u1, u2} := by
              ext w; constructor
              · intro hw
                by_cases hw0 : w = a0
                · simp [hw0]
                · have : w ∈ ({q1, q2, q3} : Finset V).erase a0 :=
                    mem_erase.2 ⟨hw0, hw⟩
                  rw [hU] at this
                  exact mem_insert_of_mem this
              · intro hw
                simp only [mem_insert, mem_singleton] at hw
                rcases hw with rfl | rfl | rfl
                · exact ha0Q
                · exact hu1Q
                · exact hu2Q
            have hC' : H.C = {t, a0, u1, u2} := by
              rw [hC, hQeq]
            have hCm : H.C = {q1, q2, t, q3} := by
              rw [hC]
              ext w
              simp only [mem_insert, mem_singleton]
              constructor
              · rintro (h | h | h | h) <;> simp [h]
              · rintro (h | h | h | h) <;> simp [h]
            exact (lemma32 G H hconn hnot
              (m0 := q1) (m1 := q2) (m2 := t) (m3 := q3) hCm heQ hmatch
              (x := t) (y := a0) (c := u1) (d := u2) hC'
              (miss u1 hu1Q hu1ne) (miss u2 hu2Q hu2ne)).elim
    obtain ⟨n0, hn0, n1, hn1, hne01⟩ := hdist
    have hn0Q : n0 ∈ ({q1, q2, q3} : Finset V) := (mem_inter.1 hn0).2
    have hn1Q : n1 ∈ ({q1, q2, q3} : Finset V) := (mem_inter.1 hn1).2
    have hG0 : G.Adj d0 n0 := (G.mem_neighborFinset _ _).1 (mem_inter.1 hn0).1
    have hG1 : G.Adj d1 n1 := (G.mem_neighborFinset _ _).1 (mem_inter.1 hn1).1
    have memQN (n : V) (hn : n ∈ ({q1, q2, q3} : Finset V)) :
        n ∈ G.neighborFinset H.u := by
      rcases (by simpa using hn : n = q1 ∨ n = q2 ∨ n = q3) with rfl | rfl | rfl
      · exact hq1N
      · exact hq2N
      · exact hq3N
    have necs (n : V) (hn : n ∈ ({q1, q2, q3} : Finset V)) :
        n ≠ H.v ∧ n ≠ t ∧ n ≠ d0 ∧ n ≠ d1 := by
      rcases (by simpa using hn : n = q1 ∨ n = q2 ∨ n = q3) with rfl | rfl | rfl
      · exact ⟨z1.symm, htq1.symm, q10, q11⟩
      · exact ⟨z2.symm, htq2.symm, q20, q21⟩
      · exact ⟨z3.symm, htq3.symm, q30, q31⟩
    have n0c := necs n0 hn0Q
    have n1c := necs n1 hn1Q
    exact hnot (wke3 (linkGraph G H.u) (q1 := q1) (q2 := q2) (q3 := q3)
      (L hzN htN hzt) (L hd0N (memQN n0 hn0Q) hG0) (L hd1N (memQN n1 hn1Q) hG1)
      (by
        simp [List.nodup_cons, zt, z0, z1p, t0, t1, hd01, hne01,
          n0c.1, n0c.2.1, n0c.2.2.1, n0c.2.2.2,
          n1c.1, n1c.2.1, n1c.2.2.1, n1c.2.2.2,
          zt.symm, z0.symm, z1p.symm, t0.symm, t1.symm, hd01.symm,
          n0c.1.symm, n0c.2.1.symm, n0c.2.2.1.symm, n0c.2.2.2.symm,
          n1c.1.symm, n1c.2.1.symm, n1c.2.2.1.symm, n1c.2.2.2.symm,
          hne01.symm])
      (fun e he hO => by
        rcases hout he hO with h | h
        · exact Or.inl h
        · subst h
          exact False.elim (hpriv
            ((mem_edgeFinset (G := linkGraph G H.u)).1 he).2.2)))

/-- **Lemma 6.1**: perfect-matching core + connected non-WKE link ⇒ every core
vertex has a private neighbour. -/
theorem lemma61 (H : HubConfig G)
    (hconn : LinkConnected G H.u) (hnot : ¬ IsWKE (linkGraph G H.u))
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hyq : G.Adj y q) :
    ∀ c ∈ H.C, ∃ a ∈ H.A, G.Adj c a := by
  intro c hc
  by_contra hnone
  push_neg at hnone
  have : c = x ∨ c = y ∨ c = p ∨ c = q := by simpa [hC] using hc
  -- Orient so the missed vertex is `t` and the in-Q matching edge is named.
  rcases this with hcx | hcy | hcp | hcq
  · -- miss x; Q={y,q,p}, heQ=yq, hmatch=xp
    subst hcx
    have hC' : H.C = {c, y, q, p} := by
      rw [hC]; ext w; simp only [mem_insert, mem_singleton]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro (h | h | h | h) <;> simp [h]
    exact lemma61_wke G H hconn hC' hyq hxp hnone hnot
  · subst hcy
    have hC' : H.C = {c, x, p, q} := by
      rw [hC]; ext w; simp only [mem_insert, mem_singleton]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro (h | h | h | h) <;> simp [h]
    exact lemma61_wke G H hconn hC' hxp hyq hnone hnot
  · subst hcp
    have hC' : H.C = {c, y, q, x} := by
      rw [hC]; ext w; simp only [mem_insert, mem_singleton]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro (h | h | h | h) <;> simp [h]
    exact lemma61_wke G H hconn hC' hyq hxp.symm hnone hnot
  · subst hcq
    have hC' : H.C = {c, x, p, y} := by
      rw [hC]; ext w; simp only [mem_insert, mem_singleton]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro (h | h | h | h) <;> simp [h]
    exact lemma61_wke G H hconn hC' hxp hyq.symm hnone hnot

/-! ### Proposition 6.2 certificate D1 (asymmetric leaf attachment) -/

def packing10_D1 : Finset (Finset (Fin 10)) :=
  {{0, 1, 5}, {0, 3, 4}, {0, 2, 6}, {1, 3, 8}, {1, 2, 4}}

def cover10_D1 : Finset (Sym2 (Fin 10)) :=
  {s(3, 4), s(2, 6), s(3, 8), s(2, 4),
   s(0, 1), s(0, 5), s(0, 7), s(1, 5), s(1, 8), s(1, 9)}

lemma packing10_D1_card : packing10_D1.card = 5 := by native_decide
lemma cover10_D1_card : cover10_D1.card = 10 := by native_decide
lemma packing10_D1_pairwise :
    ∀ σ ∈ packing10_D1, ∀ τ ∈ packing10_D1, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- D1 packing: `{uvq, uyp, uxa, vyc, vpx}`. -/
def packingD1 (u v x y p q a c : V) : Finset (Finset V) :=
  {{u, v, q}, {u, y, p}, {u, x, a}, {v, y, c}, {v, x, p}}

/-- D1 cover: R ∪ {uv, uq, ub, vq, vc, vd}. -/
def coverD1 (u v x y p q a b c d : V) : Finset (Sym2 V) :=
  {s(y, p), s(x, a), s(y, c), s(x, p),
   s(u, v), s(u, q), s(u, b), s(v, q), s(v, c), s(v, d)}

private lemma packingD1_image_eq (u v x y p q a b c d : V) :
    packing10_D1.image (mapTri (labels10 u v x y p q a b c d)) =
      packingD1 u v x y p q a c := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, _, f8, _⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have e1 : mapTri f {0, 1, 5} = ({u, v, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f5]
  have e2 : mapTri f {0, 3, 4} = ({u, y, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f4]
  have e3 : mapTri f {0, 2, 6} = ({u, x, a} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f6]
  have e4 : mapTri f {1, 3, 8} = ({v, y, c} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  have e5 : mapTri f {1, 2, 4} = ({v, x, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f4]
  simp only [packing10_D1, packingD1, image_insert, image_singleton,
    e1, e2, e3, e4, e5]

private lemma coverD1_image_eq (u v x y p q a b c d : V) :
    cover10_D1.image (Sym2.map (labels10 u v x y p q a b c d)) =
      coverD1 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_D1, coverD1, image_insert, image_singleton,
    mk 3 4 f3 f4, mk 2 6 f2 f6, mk 3 8 f3 f8, mk 2 4 f2 f4,
    mk 0 1 f0 f1, mk 0 5 f0 f5, mk 0 7 f0 f7, mk 1 5 f1 f5, mk 1 8 f1 f8, mk 1 9 f1 f9]

lemma packingD1_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (packingD1 u v x y p q a c).card = 5 := by
  let f := labels10 u v x y p q a b c d
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packingD1_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjT, packing10_D1_card]

lemma coverD1_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (coverD1 u v x y p q a b c d).card = 10 := by
  let f := labels10 u v x y p q a b c d
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← coverD1_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjE, cover10_D1_card]

lemma packingD1_disjoint (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    ∀ σ ∈ packingD1 u v x y p q a c,
      ∀ τ ∈ packingD1 u v x y p q a c,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rw [← packingD1_image_eq u v x y p q a b c d] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  exact packing53G_disjoint_of_pairwise u v x y p q a b c d hinj
    packing10_D1 packing10_D1_pairwise _ _ s0 t0 hs0 ht0
    (fun h => by subst h; exact hst rfl) rfl rfl

/-- **Prop 6.2 certificate D1**: asymmetric leaf attachment `xa, yc` with `ya, pa` absent. -/
theorem diamond_certificate_D1 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hxa : G.Adj x a) (hyc : G.Adj y c)
    (hnya : ¬ G.Adj y a) (hnpa : ¬ G.Adj p a)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y p q a b c d h10
  let f := labels10 H.u H.v x y p q a b c d
  let S := packingD1 H.u H.v x y p q a c
  let X := coverD1 H.u H.v x y p q a b c d
  have inj_ne {i j : Fin 10} (hij : i ≠ j) : f i ≠ f j := fun h => hij (hinj h)
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ub : G.Adj H.u b := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc : G.Adj H.v c := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vd : G.Adj H.v d := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  obtain ⟨hxy, hxp', hxq', hyp', hyq', hpq'⟩ := core4_distinct G H hC
  have c3 {a0 b0 c0 : V} (hab : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
      ({a0, b0, c0} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  -- labels10: 0=u,1=v,2=x,3=y,4=p,5=q,6=a,7=b,8=c,9=d
  have c_uvq : ({H.u, H.v, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 1)) (inj_ne (by decide : (0:Fin 10) ≠ 5))
      (inj_ne (by decide : (1:Fin 10) ≠ 5))
  have c_uyp : ({H.u, y, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 3)) (inj_ne (by decide : (0:Fin 10) ≠ 4)) hyp'
  have c_uxa : ({H.u, x, a} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 2)) (inj_ne (by decide : (0:Fin 10) ≠ 6))
      (inj_ne (by decide : (2:Fin 10) ≠ 6))
  have c_vyc : ({H.v, y, c} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 3)) (inj_ne (by decide : (1:Fin 10) ≠ 8))
      (inj_ne (by decide : (3:Fin 10) ≠ 8))
  have c_vxp : ({H.v, x, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 2)) (inj_ne (by decide : (1:Fin 10) ≠ 4)) hxp'
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packingD1_disjoint H.u H.v x y p q a b c d hinj⟩
    intro t ht
    simp only [S, packingD1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uvs uq vq c_uvq
    · exact is3clique_of_adj G uy up hK.2.2.1 c_uyp
    · exact is3clique_of_adj G ux ua hxa c_uxa
    · exact is3clique_of_adj G vy vc hyc c_vyc
    · exact is3clique_of_adj G vx vp hK.1 c_vxp
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, coverD1, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hK.2.2.1
    · subst h; exact (mem_edgeFinset).2 hxa
    · subst h; exact (mem_edgeFinset).2 hyc
    · subst h; exact (mem_edgeFinset).2 hK.1
    · subst h; exact (mem_edgeFinset).2 uvs
    · subst h; exact (mem_edgeFinset).2 uq
    · subst h; exact (mem_edgeFinset).2 ub
    · subst h; exact (mem_edgeFinset).2 vq
    · subst h; exact (mem_edgeFinset).2 vc
    · subst h; exact (mem_edgeFinset).2 vd
  have hcardS := packingD1_card H.u H.v x y p q a b c d hinj
  have hcardX := coverD1_card H.u H.v x y p q a b c d hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 5 := hcardS
    have hX : X.card = 10 := hcardX
    omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packingD1, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have h := triEdges_omit_vertex c_uvq he hu; rw [h]; simp [X, coverD1]
    · have h := triEdges_omit_vertex c_uyp he hu; rw [h]; simp [X, coverD1]
    · have h := triEdges_omit_vertex c_uxa he hu; rw [h]; simp [X, coverD1]
    · have h := triEdges_omit_vertex c_vyc he hv; rw [h]; simp [X, coverD1]
    · have h := triEdges_omit_vertex c_vxp he hv; rw [h]; simp [X, coverD1]
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core4 (w : V) (hw : w ∈ H.C) : w = x ∨ w = y ∨ w = p ∨ w = q := by
      simpa [hC] using hw
    have nxy_of (hA : G.Adj x y) : False := hnxy hA
    have nya_of (hA : G.Adj y a) : False := hnya hA
    have npa_of (hA : G.Adj p a) : False := hnpa hA
    rcases hhub with rfl | rfl
    · -- hub = u
      have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · -- triangle {u,v,py}; meet uv via spoke s(u,v)
        exact meet s(H.u, H.v) (by simp [X, coverD1]) (hxv ▸ him_zx)
      by_cases hyv : py = H.v
      · exact meet s(H.u, H.v) (by simp [X, coverD1]) (hyv ▸ him_zy)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxq : px = q
      · exact meet s(H.u, q) (by simp [X, coverD1]) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.u, q) (by simp [X, coverD1]) (hyq ▸ him_zy)
      by_cases hxb : px = b
      · exact meet s(H.u, b) (by simp [X, coverD1]) (hxb ▸ him_zx)
      by_cases hyb : py = b
      · exact meet s(H.u, b) (by simp [X, coverD1]) (hyb ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.A) (hnq : w ≠ q) (hnb : w ≠ b) :
          w = x ∨ w = y ∨ w = p ∨ w = a := by
        rcases mem_union.1 hwN with hwC | hwA
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact False.elim (hnq h)
        · have : w = a ∨ w = b := by simpa [hA] using hwA
          rcases this with h | h
          · exact Or.inr (Or.inr (Or.inr h))
          · exact False.elim (hnb h)
      have hpxR := inRim px hxCA hxq hxb
      have hpyR := inRim py hyCA hyq hyb
      rcases hpxR with hpx | hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD1]) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(x, a) (by simp [X, coverD1]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, p) (by simp [X, coverD1]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nya_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD1]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact meet s(y, p) (by simp [X, coverD1]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (npa_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, a) (by simp [X, coverD1]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact False.elim (nya_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (npa_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
    · -- hub = v
      have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · -- him_zx is s(v,u); cover has s(u,v)
        exact meet s(H.u, H.v) (by simp [X, coverD1]) (by
          simpa [hxu, Sym2.eq_swap] using him_zx)
      by_cases hyu : py = H.u
      · exact meet s(H.u, H.v) (by simp [X, coverD1]) (by
          simpa [hyu, Sym2.eq_swap] using him_zy)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxq : px = q
      · exact meet s(H.v, q) (by simp [X, coverD1]) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.v, q) (by simp [X, coverD1]) (hyq ▸ him_zy)
      by_cases hxc : px = c
      · exact meet s(H.v, c) (by simp [X, coverD1]) (hxc ▸ him_zx)
      by_cases hyc' : py = c
      · exact meet s(H.v, c) (by simp [X, coverD1]) (hyc' ▸ him_zy)
      by_cases hxd : px = d
      · exact meet s(H.v, d) (by simp [X, coverD1]) (hxd ▸ him_zx)
      by_cases hyd : py = d
      · exact meet s(H.v, d) (by simp [X, coverD1]) (hyd ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.B)
          (hnq : w ≠ q) (hnc : w ≠ c) (hnd : w ≠ d) :
          w = x ∨ w = y ∨ w = p := by
        rcases mem_union.1 hwN with hwC | hwB
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact False.elim (hnq h)
        · have : w = c ∨ w = d := by simpa [hB] using hwB
          rcases this with h | h
          · exact False.elim (hnc h)
          · exact False.elim (hnd h)
      have hpxR := inRim px hxCB hxq hxc hxd
      have hpyR := inRim py hyCB hyq hyc' hyd
      rcases hpxR with hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD1]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, p) (by simp [X, coverD1]) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(x, p) (by simp [X, coverD1]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact meet s(y, p) (by simp [X, coverD1]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩


/-! ### Proposition 6.2 certificate D3 (two unused private vertices) -/

def packing10_D3 : Finset (Finset (Fin 10)) :=
  {{0, 1, 5}, {0, 2, 4}, {0, 3, 6}, {1, 2, 8}, {1, 3, 4}}

def cover10_D3 : Finset (Sym2 (Fin 10)) :=
  {s(2, 4), s(3, 6), s(2, 8), s(3, 4),
   s(0, 1), s(0, 5), s(0, 6), s(1, 5), s(1, 8)}

lemma packing10_D3_card : packing10_D3.card = 5 := by native_decide
lemma cover10_D3_card : cover10_D3.card = 9 := by native_decide
lemma packing10_D3_pairwise :
    ∀ σ ∈ packing10_D3, ∀ τ ∈ packing10_D3, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- D3 packing: `{uvq, uxp, uya, vxc, vyp}`. -/
def packingD3 (u v x y p q a c : V) : Finset (Finset V) :=
  {{u, v, q}, {u, x, p}, {u, y, a}, {v, x, c}, {v, y, p}}

/-- D3 cover: R ∪ {uv, uq, ua, vq, vc}. -/
def coverD3 (u v x y p q a c : V) : Finset (Sym2 V) :=
  {s(x, p), s(y, a), s(x, c), s(y, p),
   s(u, v), s(u, q), s(u, a), s(v, q), s(v, c)}

private lemma packingD3_image_eq (u v x y p q a b c d : V) :
    packing10_D3.image (mapTri (labels10 u v x y p q a b c d)) =
      packingD3 u v x y p q a c := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, _, f8, _⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have e1 : mapTri f {0, 1, 5} = ({u, v, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f5]
  have e2 : mapTri f {0, 2, 4} = ({u, x, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f4]
  have e3 : mapTri f {0, 3, 6} = ({u, y, a} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f6]
  have e4 : mapTri f {1, 2, 8} = ({v, x, c} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f8]
  have e5 : mapTri f {1, 3, 4} = ({v, y, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f4]
  simp only [packing10_D3, packingD3, image_insert, image_singleton,
    e1, e2, e3, e4, e5]

private lemma coverD3_image_eq (u v x y p q a b c d : V) :
    cover10_D3.image (Sym2.map (labels10 u v x y p q a b c d)) =
      coverD3 u v x y p q a c := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, _, f8, _⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_D3, coverD3, image_insert, image_singleton,
    mk 2 4 f2 f4, mk 3 6 f3 f6, mk 2 8 f2 f8, mk 3 4 f3 f4,
    mk 0 1 f0 f1, mk 0 5 f0 f5, mk 0 6 f0 f6, mk 1 5 f1 f5, mk 1 8 f1 f8]

lemma packingD3_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (packingD3 u v x y p q a c).card = 5 := by
  let f := labels10 u v x y p q a b c d
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packingD3_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjT, packing10_D3_card]

lemma coverD3_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (coverD3 u v x y p q a c).card = 9 := by
  let f := labels10 u v x y p q a b c d
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← coverD3_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjE, cover10_D3_card]

lemma packingD3_disjoint (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    ∀ σ ∈ packingD3 u v x y p q a c,
      ∀ τ ∈ packingD3 u v x y p q a c,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rw [← packingD3_image_eq u v x y p q a b c d] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  exact packing53G_disjoint_of_pairwise u v x y p q a b c d hinj
    packing10_D3 packing10_D3_pairwise _ _ s0 t0 hs0 ht0
    (fun h => by subst h; exact hst rfl) rfl rfl

/-- **Prop 6.2 certificate D3**: unused privates `b,d` miss `{x,y,p}`; attachments `ya,xc`. -/
theorem diamond_certificate_D3 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hya : G.Adj y a) (hxc : G.Adj x c)
    (hnb : ∀ w ∈ ({x, y, p} : Finset V), ¬ G.Adj b w)
    (hnd : ∀ w ∈ ({x, y, p} : Finset V), ¬ G.Adj d w)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y p q a b c d h10
  let f := labels10 H.u H.v x y p q a b c d
  let S := packingD3 H.u H.v x y p q a c
  let X := coverD3 H.u H.v x y p q a c
  have inj_ne {i j : Fin 10} (hij : i ≠ j) : f i ≠ f j := fun h => hij (hinj h)
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc : G.Adj H.v c := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  obtain ⟨hxy, hxp', hxq', hyp', hyq', hpq'⟩ := core4_distinct G H hC
  have c3 {a0 b0 c0 : V} (hab : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
      ({a0, b0, c0} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  have c_uvq : ({H.u, H.v, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 1)) (inj_ne (by decide : (0:Fin 10) ≠ 5))
      (inj_ne (by decide : (1:Fin 10) ≠ 5))
  have c_uxp : ({H.u, x, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 2)) (inj_ne (by decide : (0:Fin 10) ≠ 4)) hxp'
  have c_uya : ({H.u, y, a} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 3)) (inj_ne (by decide : (0:Fin 10) ≠ 6))
      (inj_ne (by decide : (3:Fin 10) ≠ 6))
  have c_vxc : ({H.v, x, c} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 2)) (inj_ne (by decide : (1:Fin 10) ≠ 8))
      (inj_ne (by decide : (2:Fin 10) ≠ 8))
  have c_vyp : ({H.v, y, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 3)) (inj_ne (by decide : (1:Fin 10) ≠ 4)) hyp'
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packingD3_disjoint H.u H.v x y p q a b c d hinj⟩
    intro t ht
    simp only [S, packingD3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uvs uq vq c_uvq
    · exact is3clique_of_adj G ux up hK.1 c_uxp
    · exact is3clique_of_adj G uy ua hya c_uya
    · exact is3clique_of_adj G vx vc hxc c_vxc
    · exact is3clique_of_adj G vy vp hK.2.2.1 c_vyp
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, coverD3, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hK.1
    · subst h; exact (mem_edgeFinset).2 hya
    · subst h; exact (mem_edgeFinset).2 hxc
    · subst h; exact (mem_edgeFinset).2 hK.2.2.1
    · subst h; exact (mem_edgeFinset).2 uvs
    · subst h; exact (mem_edgeFinset).2 uq
    · subst h; exact (mem_edgeFinset).2 ua
    · subst h; exact (mem_edgeFinset).2 vq
    · subst h; exact (mem_edgeFinset).2 vc
  have hcardS := packingD3_card H.u H.v x y p q a b c d hinj
  have hcardX := coverD3_card H.u H.v x y p q a b c d hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 5 := hcardS
    have hX : X.card = 9 := hcardX
    omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packingD3, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · have h := triEdges_omit_vertex c_uvq he hu; rw [h]; simp [X, coverD3]
    · have h := triEdges_omit_vertex c_uxp he hu; rw [h]; simp [X, coverD3]
    · have h := triEdges_omit_vertex c_uya he hu; rw [h]; simp [X, coverD3]
    · have h := triEdges_omit_vertex c_vxc he hv; rw [h]; simp [X, coverD3]
    · have h := triEdges_omit_vertex c_vyp he hv; rw [h]; simp [X, coverD3]
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core4 (w : V) (hw : w ∈ H.C) : w = x ∨ w = y ∨ w = p ∨ w = q := by
      simpa [hC] using hw
    have nxy_of (hA : G.Adj x y) : False := hnxy hA
    have nb_of {w : V} (hw : w ∈ ({x, y, p} : Finset V)) (hA : G.Adj b w) : False :=
      hnb w hw hA
    have nd_of {w : V} (hw : w ∈ ({x, y, p} : Finset V)) (hA : G.Adj d w) : False :=
      hnd w hw hA
    rcases hhub with rfl | rfl
    · -- hub = u; delete uq, ua → rims in {x,y,p,b}
      have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · exact meet s(H.u, H.v) (by simp [X, coverD3]) (hxv ▸ him_zx)
      by_cases hyv : py = H.v
      · exact meet s(H.u, H.v) (by simp [X, coverD3]) (hyv ▸ him_zy)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxq : px = q
      · exact meet s(H.u, q) (by simp [X, coverD3]) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.u, q) (by simp [X, coverD3]) (hyq ▸ him_zy)
      by_cases hxa : px = a
      · exact meet s(H.u, a) (by simp [X, coverD3]) (hxa ▸ him_zx)
      by_cases hya' : py = a
      · exact meet s(H.u, a) (by simp [X, coverD3]) (hya' ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.A) (hnq : w ≠ q) (hna : w ≠ a) :
          w = x ∨ w = y ∨ w = p ∨ w = b := by
        rcases mem_union.1 hwN with hwC | hwA
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact False.elim (hnq h)
        · have : w = a ∨ w = b := by simpa [hA] using hwA
          rcases this with h | h
          · exact False.elim (hna h)
          · exact Or.inr (Or.inr (Or.inr h))
      have hpxR := inRim px hxCA hxq hxa
      have hpyR := inRim py hyCA hyq hya'
      rcases hpxR with hpx | hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD3]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nb_of (by simp [hpy] : x ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, p) (by simp [X, coverD3]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nb_of (by simp [hpy] : y ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact meet s(x, p) (by simp [X, coverD3]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact meet s(y, p) (by simp [X, coverD3]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nb_of (by simp [hpy] : p ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (nb_of (by simp [hpx] : x ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact False.elim (nb_of (by simp [hpx] : y ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact False.elim (nb_of (by simp [hpx] : p ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact absurd (hpx.trans hpy.symm) hpxy
    · -- hub = v; delete vq, vc → rims in {x,y,p,d}
      have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · exact meet s(H.u, H.v) (by simp [X, coverD3]) (by
          simpa [hxu, Sym2.eq_swap] using him_zx)
      by_cases hyu : py = H.u
      · exact meet s(H.u, H.v) (by simp [X, coverD3]) (by
          simpa [hyu, Sym2.eq_swap] using him_zy)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxq : px = q
      · exact meet s(H.v, q) (by simp [X, coverD3]) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.v, q) (by simp [X, coverD3]) (hyq ▸ him_zy)
      by_cases hxc' : px = c
      · exact meet s(H.v, c) (by simp [X, coverD3]) (hxc' ▸ him_zx)
      by_cases hyc' : py = c
      · exact meet s(H.v, c) (by simp [X, coverD3]) (hyc' ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.B) (hnq : w ≠ q) (hnc : w ≠ c) :
          w = x ∨ w = y ∨ w = p ∨ w = d := by
        rcases mem_union.1 hwN with hwC | hwB
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact False.elim (hnq h)
        · have : w = c ∨ w = d := by simpa [hB] using hwB
          rcases this with h | h
          · exact False.elim (hnc h)
          · exact Or.inr (Or.inr (Or.inr h))
      have hpxR := inRim px hxCB hxq hxc'
      have hpyR := inRim py hyCB hyq hyc'
      rcases hpxR with hpx | hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD3]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nd_of (by simp [hpy] : x ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (nxy_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, p) (by simp [X, coverD3]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nd_of (by simp [hpy] : y ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact meet s(x, p) (by simp [X, coverD3]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact meet s(y, p) (by simp [X, coverD3]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nd_of (by simp [hpy] : p ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (nd_of (by simp [hpx] : x ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact False.elim (nd_of (by simp [hpx] : y ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact False.elim (nd_of (by simp [hpx] : p ∈ ({x,y,p}:Finset V))
          (by simpa [hpx, hpy] using hxyAdj))
      · exact absurd (hpx.trans hpy.symm) hpxy
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩


/-! ### Proposition 6.2 certificate D5 (two private edges + double center) -/

def packing10_D5 : Finset (Finset (Fin 10)) :=
  {{0, 2, 5}, {0, 3, 4}, {0, 6, 7}, {1, 2, 4}, {1, 3, 5}, {1, 8, 9}, {4, 5, 9}}

def cover10_D5 : Finset (Sym2 (Fin 10)) :=
  {s(2, 4), s(2, 5), s(3, 4), s(3, 5), s(4, 5),
   s(6, 7), s(8, 9), s(4, 9), s(5, 9),
   s(0, 1), s(0, 6), s(0, 7), s(1, 8), s(1, 9)}

lemma packing10_D5_card : packing10_D5.card = 7 := by native_decide
lemma cover10_D5_card : cover10_D5.card = 14 := by native_decide
lemma packing10_D5_pairwise :
    ∀ σ ∈ packing10_D5, ∀ τ ∈ packing10_D5, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- D5 packing: `{uxq, uyp, uab, vxp, vyq, vcd, dpq}`. -/
def packingD5 (u v x y p q a b c d : V) : Finset (Finset V) :=
  {{u, x, q}, {u, y, p}, {u, a, b}, {v, x, p}, {v, y, q}, {v, c, d}, {d, p, q}}

/-- D5 cover: E(G[C]) ∪ {ab,cd,dp,dq} ∪ {uv,ua,ub,vc,vd}. -/
def coverD5 (u v x y p q a b c d : V) : Finset (Sym2 V) :=
  {s(x, p), s(x, q), s(y, p), s(y, q), s(p, q),
   s(a, b), s(c, d), s(p, d), s(q, d),
   s(u, v), s(u, a), s(u, b), s(v, c), s(v, d)}

private lemma packingD5_image_eq (u v x y p q a b c d : V) :
    packing10_D5.image (mapTri (labels10 u v x y p q a b c d)) =
      packingD5 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have e1 : mapTri f {0, 2, 5} = ({u, x, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f5]
  have e2 : mapTri f {0, 3, 4} = ({u, y, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f4]
  have e3 : mapTri f {0, 6, 7} = ({u, a, b} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f6, f7]
  have e4 : mapTri f {1, 2, 4} = ({v, x, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f4]
  have e5 : mapTri f {1, 3, 5} = ({v, y, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f5]
  have e6 : mapTri f {1, 8, 9} = ({v, c, d} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f8, f9]
  have e7 : mapTri f {4, 5, 9} = ({d, p, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f4, f5, f9]
    ext; simp [or_comm, or_left_comm]
  simp only [packing10_D5, packingD5, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6, e7]

private lemma coverD5_image_eq (u v x y p q a b c d : V) :
    cover10_D5.image (Sym2.map (labels10 u v x y p q a b c d)) =
      coverD5 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_D5, coverD5, image_insert, image_singleton,
    mk 2 4 f2 f4, mk 2 5 f2 f5, mk 3 4 f3 f4, mk 3 5 f3 f5, mk 4 5 f4 f5,
    mk 6 7 f6 f7, mk 8 9 f8 f9, mk 4 9 f4 f9, mk 5 9 f5 f9,
    mk 0 1 f0 f1, mk 0 6 f0 f6, mk 0 7 f0 f7, mk 1 8 f1 f8, mk 1 9 f1 f9]

lemma packingD5_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (packingD5 u v x y p q a b c d).card = 7 := by
  let f := labels10 u v x y p q a b c d
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packingD5_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjT, packing10_D5_card]

lemma coverD5_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (coverD5 u v x y p q a b c d).card = 14 := by
  let f := labels10 u v x y p q a b c d
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← coverD5_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjE, cover10_D5_card]

lemma packingD5_disjoint (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    ∀ σ ∈ packingD5 u v x y p q a b c d,
      ∀ τ ∈ packingD5 u v x y p q a b c d,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rw [← packingD5_image_eq u v x y p q a b c d] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  exact packing53G_disjoint_of_pairwise u v x y p q a b c d hinj
    packing10_D5 packing10_D5_pairwise _ _ s0 t0 hs0 ht0
    (fun h => by subst h; exact hst rfl) rfl rfl

/-- **Prop 6.2 certificate D5**: private edges `ab,cd` and double center `dp,dq`.
Paper coverage: two-hub meets `uv`; remaining hub triangles use a private spoke in `X`
or a rim in `E(G[C]) ⊆ X`. -/
theorem diamond_certificate_D5 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdp : G.Adj d p) (hdq : G.Adj d q)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y p q a b c d h10
  let f := labels10 H.u H.v x y p q a b c d
  let S := packingD5 H.u H.v x y p q a b c d
  let X := coverD5 H.u H.v x y p q a b c d
  have inj_ne {i j : Fin 10} (hij : i ≠ j) : f i ≠ f j := fun h => hij (hinj h)
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ub : G.Adj H.u b := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc : G.Adj H.v c := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vd : G.Adj H.v d := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  obtain ⟨hxy, hxp', hxq', hyp', hyq', hpq'⟩ := core4_distinct G H hC
  have c3 {a0 b0 c0 : V} (hab0 : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
      ({a0, b0, c0} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab0, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  have c_uxq : ({H.u, x, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 2)) (inj_ne (by decide : (0:Fin 10) ≠ 5)) hxq'
  have c_uyp : ({H.u, y, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 3)) (inj_ne (by decide : (0:Fin 10) ≠ 4)) hyp'
  have c_uab : ({H.u, a, b} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 6)) (inj_ne (by decide : (0:Fin 10) ≠ 7))
      (inj_ne (by decide : (6:Fin 10) ≠ 7))
  have c_vxp : ({H.v, x, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 2)) (inj_ne (by decide : (1:Fin 10) ≠ 4)) hxp'
  have c_vyq : ({H.v, y, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 3)) (inj_ne (by decide : (1:Fin 10) ≠ 5)) hyq'
  have c_vcd : ({H.v, c, d} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 8)) (inj_ne (by decide : (1:Fin 10) ≠ 9))
      (inj_ne (by decide : (8:Fin 10) ≠ 9))
  have c_dpq : ({d, p, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (9:Fin 10) ≠ 4)) (inj_ne (by decide : (9:Fin 10) ≠ 5)) hpq'
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packingD5_disjoint H.u H.v x y p q a b c d hinj⟩
    intro t ht
    simp only [S, packingD5, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G ux uq hK.2.1 c_uxq
    · exact is3clique_of_adj G uy up hK.2.2.1 c_uyp
    · exact is3clique_of_adj G ua ub hab c_uab
    · exact is3clique_of_adj G vx vp hK.1 c_vxp
    · exact is3clique_of_adj G vy vq hK.2.2.2.1 c_vyq
    · exact is3clique_of_adj G vc vd hcd c_vcd
    · exact is3clique_of_adj G hdp hdq hK.2.2.2.2 c_dpq
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, coverD5, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hK.1
    · subst h; exact (mem_edgeFinset).2 hK.2.1
    · subst h; exact (mem_edgeFinset).2 hK.2.2.1
    · subst h; exact (mem_edgeFinset).2 hK.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 hK.2.2.2.2
    · subst h; exact (mem_edgeFinset).2 hab
    · subst h; exact (mem_edgeFinset).2 hcd
    · subst h; exact (mem_edgeFinset).2 hdp.symm
    · subst h; exact (mem_edgeFinset).2 hdq.symm
    · subst h; exact (mem_edgeFinset).2 uvs
    · subst h; exact (mem_edgeFinset).2 ua
    · subst h; exact (mem_edgeFinset).2 ub
    · subst h; exact (mem_edgeFinset).2 vc
    · subst h; exact (mem_edgeFinset).2 vd
  have hcardS := packingD5_card H.u H.v x y p q a b c d hinj
  have hcardX := coverD5_card H.u H.v x y p q a b c d hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 7 := hcardS
    have hX : X.card = 14 := hcardX
    omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packingD5, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := triEdges_omit_vertex c_uxq he hu; rw [h]; simp [X, coverD5]
    · have h := triEdges_omit_vertex c_uyp he hu; rw [h]; simp [X, coverD5]
    · have h := triEdges_omit_vertex c_uab he hu; rw [h]; simp [X, coverD5]
    · have h := triEdges_omit_vertex c_vxp he hv; rw [h]; simp [X, coverD5]
    · have h := triEdges_omit_vertex c_vyq he hv; rw [h]; simp [X, coverD5]
    · have h := triEdges_omit_vertex c_vcd he hv; rw [h]; simp [X, coverD5]
    · -- outside triangle dpq: all three edges in X
      have he' : e ∈ triEdges ({d, p, q} : Finset V) := he
      rw [triEdges_eq_of_card3 c_dpq] at he'
      simp only [mem_insert, mem_singleton] at he'
      rcases he' with h | h | h
      · simp [X, coverD5, h]
      · simp [X, coverD5, h, Sym2.eq_swap]
      · simp [X, coverD5, h, Sym2.eq_swap]
  -- coversZ: paper argument — leave as structured case for now if long; try full
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have core4 (w : V) (hw : w ∈ H.C) : w = x ∨ w = y ∨ w = p ∨ w = q := by
      simpa [hC] using hw
    have rim_core (hxC : px ∈ H.C) (hyC : py ∈ H.C) :
        s(px, py) ∈ X := by
      -- both in C ⇒ edge is one of xp,xq,yp,yq,pq (xy absent)
      have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
      rcases core4 px hxC with hpx | hpx | hpx | hpx <;>
        rcases core4 py hyC with hpy | hpy | hpy | hpy
      · exact False.elim (hpxy (hpx.trans hpy.symm))
      · exact False.elim (hnxy (by simpa [hpx, hpy] using hxyAdj))
      · simp [X, coverD5, hpx, hpy]
      · simp [X, coverD5, hpx, hpy]
      · exact False.elim (hnxy (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (hpxy (hpx.trans hpy.symm))
      · simp [X, coverD5, hpx, hpy]
      · simp [X, coverD5, hpx, hpy]
      · simp [X, coverD5, hpx, hpy, Sym2.eq_swap]
      · simp [X, coverD5, hpx, hpy, Sym2.eq_swap]
      · exact False.elim (hpxy (hpx.trans hpy.symm))
      · simp [X, coverD5, hpx, hpy]
      · simp [X, coverD5, hpx, hpy, Sym2.eq_swap]
      · simp [X, coverD5, hpx, hpy, Sym2.eq_swap]
      · simp [X, coverD5, hpx, hpy, Sym2.eq_swap]
      · exact False.elim (hpxy (hpx.trans hpy.symm))
    rcases hhub with rfl | rfl
    · have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · exact meet s(H.u, H.v) (by simp [X, coverD5]) (hxv ▸ him_zx)
      by_cases hyv : py = H.v
      · exact meet s(H.u, H.v) (by simp [X, coverD5]) (hyv ▸ him_zy)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxa : px = a
      · exact meet s(H.u, a) (by simp [X, coverD5]) (hxa ▸ him_zx)
      by_cases hya : py = a
      · exact meet s(H.u, a) (by simp [X, coverD5]) (hya ▸ him_zy)
      by_cases hxb : px = b
      · exact meet s(H.u, b) (by simp [X, coverD5]) (hxb ▸ him_zx)
      by_cases hyb : py = b
      · exact meet s(H.u, b) (by simp [X, coverD5]) (hyb ▸ him_zy)
      -- both in C (A exhausted)
      have hxC : px ∈ H.C := by
        rcases mem_union.1 hxCA with h | h
        · exact h
        · have : px = a ∨ px = b := by simpa [hA] using h
          exact this.elim (fun e => False.elim (hxa e)) (fun e => False.elim (hxb e))
      have hyC : py ∈ H.C := by
        rcases mem_union.1 hyCA with h | h
        · exact h
        · have : py = a ∨ py = b := by simpa [hA] using h
          exact this.elim (fun e => False.elim (hya e)) (fun e => False.elim (hyb e))
      exact meet _ (rim_core hxC hyC) him_rim
    · have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · exact meet s(H.u, H.v) (by simp [X, coverD5]) (by
          simpa [hxu, Sym2.eq_swap] using him_zx)
      by_cases hyu : py = H.u
      · exact meet s(H.u, H.v) (by simp [X, coverD5]) (by
          simpa [hyu, Sym2.eq_swap] using him_zy)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxc : px = c
      · exact meet s(H.v, c) (by simp [X, coverD5]) (hxc ▸ him_zx)
      by_cases hyc : py = c
      · exact meet s(H.v, c) (by simp [X, coverD5]) (hyc ▸ him_zy)
      by_cases hxd : px = d
      · exact meet s(H.v, d) (by simp [X, coverD5]) (hxd ▸ him_zx)
      by_cases hyd : py = d
      · exact meet s(H.v, d) (by simp [X, coverD5]) (hyd ▸ him_zy)
      have hxC : px ∈ H.C := by
        rcases mem_union.1 hxCB with h | h
        · exact h
        · have : px = c ∨ px = d := by simpa [hB] using h
          exact this.elim (fun e => False.elim (hxc e)) (fun e => False.elim (hxd e))
      have hyC : py ∈ H.C := by
        rcases mem_union.1 hyCB with h | h
        · exact h
        · have : py = c ∨ py = d := by simpa [hB] using h
          exact this.elim (fun e => False.elim (hyc e)) (fun e => False.elim (hyd e))
      exact meet _ (rim_core hxC hyC) him_rim
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩

/-! ### Proposition 6.2 certificate D2 (crossed attachment matchings) -/

def packing10_D2 : Finset (Finset (Fin 10)) :=
  {{0, 2, 6}, {0, 4, 7}, {0, 3, 5}, {1, 2, 4}, {1, 3, 8}, {1, 5, 9}}

def cover10_D2 : Finset (Sym2 (Fin 10)) :=
  {s(2, 6), s(4, 7), s(3, 5), s(2, 4), s(3, 8), s(5, 9),
   s(0, 3), s(0, 5), s(1, 2), s(1, 4), s(1, 9)}

lemma packing10_D2_card : packing10_D2.card = 6 := by native_decide
lemma cover10_D2_card : cover10_D2.card = 11 := by native_decide
lemma packing10_D2_pairwise :
    ∀ σ ∈ packing10_D2, ∀ τ ∈ packing10_D2, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- D2 packing: `{uxa, upb, uyq, vxp, vyc, vqd}`. -/
def packingD2 (u v x y p q a b c d : V) : Finset (Finset V) :=
  {{u, x, a}, {u, p, b}, {u, y, q}, {v, x, p}, {v, y, c}, {v, q, d}}

/-- D2 base cover: R ∪ {uy, uq, vx, vp, vd}. -/
def coverD2 (u v x y p q a b c d : V) : Finset (Sym2 V) :=
  {s(x, a), s(p, b), s(y, q), s(x, p), s(y, c), s(q, d),
   s(u, y), s(u, q), s(v, x), s(v, p), s(v, d)}

private lemma packingD2_image_eq (u v x y p q a b c d : V) :
    packing10_D2.image (mapTri (labels10 u v x y p q a b c d)) =
      packingD2 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have e1 : mapTri f {0, 2, 6} = ({u, x, a} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f2, f6]
  have e2 : mapTri f {0, 4, 7} = ({u, p, b} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f4, f7]
  have e3 : mapTri f {0, 3, 5} = ({u, y, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e4 : mapTri f {1, 2, 4} = ({v, x, p} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f2, f4]
  have e5 : mapTri f {1, 3, 8} = ({v, y, c} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  have e6 : mapTri f {1, 5, 9} = ({v, q, d} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f5, f9]
  simp only [packing10_D2, packingD2, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma coverD2_image_eq (u v x y p q a b c d : V) :
    cover10_D2.image (Sym2.map (labels10 u v x y p q a b c d)) =
      coverD2 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_D2, coverD2, image_insert, image_singleton,
    mk 2 6 f2 f6, mk 4 7 f4 f7, mk 3 5 f3 f5, mk 2 4 f2 f4, mk 3 8 f3 f8, mk 5 9 f5 f9,
    mk 0 3 f0 f3, mk 0 5 f0 f5, mk 1 2 f1 f2, mk 1 4 f1 f4, mk 1 9 f1 f9]

lemma packingD2_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (packingD2 u v x y p q a b c d).card = 6 := by
  let f := labels10 u v x y p q a b c d
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packingD2_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjT, packing10_D2_card]

lemma coverD2_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (coverD2 u v x y p q a b c d).card = 11 := by
  let f := labels10 u v x y p q a b c d
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← coverD2_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjE, cover10_D2_card]

lemma packingD2_disjoint (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    ∀ σ ∈ packingD2 u v x y p q a b c d,
      ∀ τ ∈ packingD2 u v x y p q a b c d,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rw [← packingD2_image_eq u v x y p q a b c d] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  exact packing53G_disjoint_of_pairwise u v x y p q a b c d hinj
    packing10_D2 packing10_D2_pairwise _ _ s0 t0 hs0 ht0
    (fun h => by subst h; exact hst rfl) rfl rfl

/-- **Prop 6.2 certificate D2**: crossed matchings `xa,pb,yc,qd` with absences `pa,xb,qc`. -/
theorem diamond_certificate_D2 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hxa : G.Adj x a) (hpb : G.Adj p b) (hyc : G.Adj y c) (hqd : G.Adj q d)
    (hnpa : ¬ G.Adj p a) (hnxb : ¬ G.Adj x b) (hnqc : ¬ G.Adj q c)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y p q a b c d h10
  let f := labels10 H.u H.v x y p q a b c d
  let S := packingD2 H.u H.v x y p q a b c d
  let X0 := coverD2 H.u H.v x y p q a b c d
  let X : Finset (Sym2 V) := if G.Adj a b then insert s(a, b) X0 else X0
  have inj_ne {i j : Fin 10} (hij : i ≠ j) : f i ≠ f j := fun h => hij (hinj h)
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ub : G.Adj H.u b := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc : G.Adj H.v c := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vd : G.Adj H.v d := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  obtain ⟨hxy, hxp', hxq', hyp', hyq', hpq'⟩ := core4_distinct G H hC
  have c3 {a0 b0 c0 : V} (hab0 : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
      ({a0, b0, c0} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab0, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  have c_uxa : ({H.u, x, a} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 2)) (inj_ne (by decide : (0:Fin 10) ≠ 6))
      (inj_ne (by decide : (2:Fin 10) ≠ 6))
  have c_upb : ({H.u, p, b} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 4)) (inj_ne (by decide : (0:Fin 10) ≠ 7))
      (inj_ne (by decide : (4:Fin 10) ≠ 7))
  have c_uyq : ({H.u, y, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 3)) (inj_ne (by decide : (0:Fin 10) ≠ 5)) hyq'
  have c_vxp : ({H.v, x, p} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 2)) (inj_ne (by decide : (1:Fin 10) ≠ 4)) hxp'
  have c_vyc : ({H.v, y, c} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 3)) (inj_ne (by decide : (1:Fin 10) ≠ 8))
      (inj_ne (by decide : (3:Fin 10) ≠ 8))
  have c_vqd : ({H.v, q, d} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 5)) (inj_ne (by decide : (1:Fin 10) ≠ 9))
      (inj_ne (by decide : (5:Fin 10) ≠ 9))
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packingD2_disjoint H.u H.v x y p q a b c d hinj⟩
    intro t ht
    simp only [S, packingD2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G ux ua hxa c_uxa
    · exact is3clique_of_adj G up ub hpb c_upb
    · exact is3clique_of_adj G uy uq hK.2.2.2.1 c_uyq
    · exact is3clique_of_adj G vx vp hK.1 c_vxp
    · exact is3clique_of_adj G vy vc hyc c_vyc
    · exact is3clique_of_adj G vq vd hqd c_vqd
  have hX0edges : ∀ e ∈ X0, e ∈ G.edgeFinset := by
    intro e he
    simp only [X0, coverD2, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hxa
    · subst h; exact (mem_edgeFinset).2 hpb
    · subst h; exact (mem_edgeFinset).2 hK.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 hK.1
    · subst h; exact (mem_edgeFinset).2 hyc
    · subst h; exact (mem_edgeFinset).2 hqd
    · subst h; exact (mem_edgeFinset).2 uy
    · subst h; exact (mem_edgeFinset).2 uq
    · subst h; exact (mem_edgeFinset).2 vx
    · subst h; exact (mem_edgeFinset).2 vp
    · subst h; exact (mem_edgeFinset).2 vd
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    by_cases hab : G.Adj a b
    · simp only [X, hab, ↓reduceIte, mem_insert] at he
      rcases he with h | h
      · subst h; exact (mem_edgeFinset).2 hab
      · exact hX0edges e h
    · simp only [X, hab, ↓reduceIte] at he
      exact hX0edges e he
  have hcardS := packingD2_card H.u H.v x y p q a b c d hinj
  have hcardX0 := coverD2_card H.u H.v x y p q a b c d hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 6 := hcardS
    by_cases hab : G.Adj a b
    · have : X.card ≤ X0.card + 1 := by
        simp only [X, hab, ↓reduceIte]; exact card_insert_le _ _
      have hX0 : X0.card = 11 := hcardX0; omega
    · simp only [X, hab, ↓reduceIte]
      have hX0 : X0.card = 11 := hcardX0; omega
  have memX0 (e : Sym2 V) (he0 : e ∈ X0) : e ∈ X := by
    by_cases hab : G.Adj a b <;> simp [X, hab, he0]
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packingD2, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have h := triEdges_omit_vertex c_uxa he hu; rw [h]; exact memX0 _ (by simp [X0, coverD2])
    · have h := triEdges_omit_vertex c_upb he hu; rw [h]; exact memX0 _ (by simp [X0, coverD2])
    · have h := triEdges_omit_vertex c_uyq he hu; rw [h]; exact memX0 _ (by simp [X0, coverD2])
    · have h := triEdges_omit_vertex c_vxp he hv; rw [h]; exact memX0 _ (by simp [X0, coverD2])
    · have h := triEdges_omit_vertex c_vyc he hv; rw [h]; exact memX0 _ (by simp [X0, coverD2])
    · have h := triEdges_omit_vertex c_vqd he hv; rw [h]; exact memX0 _ (by simp [X0, coverD2])
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core4 (w : V) (hw : w ∈ H.C) : w = x ∨ w = y ∨ w = p ∨ w = q := by
      simpa [hC] using hw
    have not_A_adj_v (w : V) (hwA : w ∈ H.A) (hvw : G.Adj H.v w) : False :=
      not_adj_hub_priv G H hwA hvw
    have not_B_adj_u (w : V) (hwB : w ∈ H.B) (huw : G.Adj H.u w) : False := by
      have hwN : w ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 huw
      have : w ∈ insert H.v (H.C ∪ H.A) := by rwa [H.hNu] at hwN
      have hvB : H.v ∉ H.B := fun h => by
        have : H.v ∈ G.neighborFinset H.v := by
          rw [H.hNv]; exact mem_insert_of_mem (mem_union_right _ h)
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
      have hwne : w ≠ H.v := fun eq => hvB (eq ▸ hwB)
      have hwCA : w ∈ H.C ∪ H.A := (mem_insert.1 this).resolve_left hwne
      rcases mem_union.1 hwCA with hwC | hwA
      · exact Finset.disjoint_left.1 H.hBdisj hwB hwC
      · exact Finset.disjoint_left.1 H.hABdisj hwA hwB
    rcases hhub with rfl | rfl
    · -- hub = u
      have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv
        have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hpxy.symm
        rcases mem_union.1 hyCA with hyC | hyA
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy] using him_zy)
          · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy] using him_zy)
        · exact False.elim (not_A_adj_v py hyA hxyAdj)
      by_cases hyv : py = H.v
      · subst hyv
        have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hpxy
        rcases mem_union.1 hxCA with hxC | hxA
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx] using him_zx)
          · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx] using him_zx)
        · exact False.elim (not_A_adj_v px hxA hxyAdj.symm)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxy_y : px = y
      · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (hxy_y ▸ him_zx)
      by_cases hyy : py = y
      · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (hyy ▸ him_zy)
      by_cases hxq : px = q
      · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (hyq ▸ him_zy)
      -- remaining rim in {x,p,a,b}
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.A)
          (hny : w ≠ y) (hnq : w ≠ q) : w = x ∨ w = p ∨ w = a ∨ w = b := by
        rcases mem_union.1 hwN with hwC | hwA
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact False.elim (hny h)
          · exact Or.inr (Or.inl h)
          · exact False.elim (hnq h)
        · have : w = a ∨ w = b := by simpa [hA] using hwA
          rcases this with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      have hpxR := inRim px hxCA hxy_y hxq
      have hpyR := inRim py hyCA hyy hyq
      have npa_of (hA' : G.Adj p a) : False := hnpa hA'
      have nxb_of (hA' : G.Adj x b) : False := hnxb hA'
      rcases hpxR with hpx | hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(x, p) (memX0 _ (by simp [X0, coverD2])) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(x, a) (memX0 _ (by simp [X0, coverD2])) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nxb_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (memX0 _ (by simp [X0, coverD2])) (by
          simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (npa_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(p, b) (memX0 _ (by simp [X0, coverD2])) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(x, a) (memX0 _ (by simp [X0, coverD2])) (by
          simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact False.elim (npa_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
      · -- rim ab: need ab ∈ X if present
        by_cases hab : G.Adj a b
        · have : s(a, b) ∈ X := by simp [X, hab]
          exact meet s(a, b) this (by simpa [hpx, hpy] using him_rim)
        · exact absurd (by simpa [hpx, hpy] using hxyAdj) hab
      · exact False.elim (nxb_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact meet s(p, b) (memX0 _ (by simp [X0, coverD2])) (by
          simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · by_cases hab : G.Adj a b
        · have : s(a, b) ∈ X := by simp [X, hab]
          exact meet s(a, b) this (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
        · exact absurd (by simpa [hpx, hpy] using hxyAdj.symm) hab
      · exact absurd (hpx.trans hpy.symm) hpxy
    · -- hub = v
      have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hpxy.symm
        rcases mem_union.1 hyCB with hyC | hyB
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy] using him_zy)
          · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy] using him_zy)
          · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
        · exact False.elim (not_B_adj_u py hyB hxyAdj)
      by_cases hyu : py = H.u
      · subst hyu
        have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hpxy
        rcases mem_union.1 hxCB with hxC | hxB
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx] using him_zx)
          · exact meet s(H.u, y) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx] using him_zx)
          · exact meet s(H.u, q) (memX0 _ (by simp [X0, coverD2])) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
        · exact False.elim (not_B_adj_u px hxB hxyAdj.symm)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxx : px = x
      · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (hxx ▸ him_zx)
      by_cases hyx : py = x
      · exact meet s(H.v, x) (memX0 _ (by simp [X0, coverD2])) (hyx ▸ him_zy)
      by_cases hxp : px = p
      · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (hxp ▸ him_zx)
      by_cases hyp : py = p
      · exact meet s(H.v, p) (memX0 _ (by simp [X0, coverD2])) (hyp ▸ him_zy)
      by_cases hxd : px = d
      · exact meet s(H.v, d) (memX0 _ (by simp [X0, coverD2])) (hxd ▸ him_zx)
      by_cases hyd : py = d
      · exact meet s(H.v, d) (memX0 _ (by simp [X0, coverD2])) (hyd ▸ him_zy)
      -- remaining in {y,q,c}
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.B)
          (hnx : w ≠ x) (hnp : w ≠ p) (hnd : w ≠ d) :
          w = y ∨ w = q ∨ w = c := by
        rcases mem_union.1 hwN with hwC | hwB
        · rcases core4 w hwC with h | h | h | h
          · exact False.elim (hnx h)
          · exact Or.inl h
          · exact False.elim (hnp h)
          · exact Or.inr (Or.inl h)
        · have : w = c ∨ w = d := by simpa [hB] using hwB
          rcases this with h | h
          · exact Or.inr (Or.inr h)
          · exact False.elim (hnd h)
      have hpxR := inRim px hxCB hxx hxp hxd
      have hpyR := inRim py hyCB hyx hyp hyd
      have nqc_of (hA' : G.Adj q c) : False := hnqc hA'
      rcases hpxR with hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, q) (memX0 _ (by simp [X0, coverD2])) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(y, c) (memX0 _ (by simp [X0, coverD2])) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(y, q) (memX0 _ (by simp [X0, coverD2])) (by
          simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nqc_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(y, c) (memX0 _ (by simp [X0, coverD2])) (by
          simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact False.elim (nqc_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩



/-! ### Proposition 6.2 certificate D4 (private edge + outside triangle) -/

def packing10_D4 : Finset (Finset (Fin 10)) :=
  {{0, 1, 2}, {0, 3, 5}, {0, 6, 7}, {1, 3, 8}, {1, 5, 9}, {2, 4, 6}}

def cover10_D4 : Finset (Sym2 (Fin 10)) :=
  {s(2, 4), s(2, 6), s(4, 6), s(3, 5), s(3, 8), s(5, 9), s(6, 7),
   s(0, 3), s(0, 5), s(1, 2), s(1, 4), s(1, 9)}

lemma packing10_D4_card : packing10_D4.card = 6 := by native_decide
lemma cover10_D4_card : cover10_D4.card = 12 := by native_decide
lemma packing10_D4_pairwise :
    ∀ σ ∈ packing10_D4, ∀ τ ∈ packing10_D4, σ ≠ τ → (σ ∩ τ).card ≤ 1 := by
  native_decide

/-- D4 packing: `{uvx, uyq, uab, vyc, vqd, xpa}`. -/
def packingD4 (u v x y p q a b c d : V) : Finset (Finset V) :=
  {{u, v, x}, {u, y, q}, {u, a, b}, {v, y, c}, {v, q, d}, {x, p, a}}

/-- D4 cover: R ∪ {uy, uq, vx, vp, vd}. -/
def coverD4 (u v x y p q a b c d : V) : Finset (Sym2 V) :=
  {s(x, p), s(x, a), s(p, a), s(y, q), s(y, c), s(q, d), s(a, b),
   s(u, y), s(u, q), s(v, x), s(v, p), s(v, d)}

private lemma packingD4_image_eq (u v x y p q a b c d : V) :
    packing10_D4.image (mapTri (labels10 u v x y p q a b c d)) =
      packingD4 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have e1 : mapTri f {0, 1, 2} = ({u, v, x} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f1, f2]
  have e2 : mapTri f {0, 3, 5} = ({u, y, q} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f3, f5]
  have e3 : mapTri f {0, 6, 7} = ({u, a, b} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f0, f6, f7]
  have e4 : mapTri f {1, 3, 8} = ({v, y, c} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f3, f8]
  have e5 : mapTri f {1, 5, 9} = ({v, q, d} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f1, f5, f9]
  have e6 : mapTri f {2, 4, 6} = ({x, p, a} : Finset V) := by
    simp only [mapTri, image_insert, image_singleton]; rw [f2, f4, f6]
  simp only [packing10_D4, packingD4, image_insert, image_singleton,
    e1, e2, e3, e4, e5, e6]

private lemma coverD4_image_eq (u v x y p q a b c d : V) :
    cover10_D4.image (Sym2.map (labels10 u v x y p q a b c d)) =
      coverD4 u v x y p q a b c d := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    map_lab u v x y p q a b c d
  set f := labels10 u v x y p q a b c d
  have mk (i j : Fin 10) {p q : V} (hi : f i = p) (hj : f j = q) :
      Sym2.map f s(i, j) = s(p, q) := by rw [Sym2.map_mk, hi, hj]
  simp only [cover10_D4, coverD4, image_insert, image_singleton,
    mk 2 4 f2 f4, mk 2 6 f2 f6, mk 4 6 f4 f6, mk 3 5 f3 f5, mk 3 8 f3 f8, mk 5 9 f5 f9,
    mk 6 7 f6 f7, mk 0 3 f0 f3, mk 0 5 f0 f5, mk 1 2 f1 f2, mk 1 4 f1 f4, mk 1 9 f1 f9]

lemma packingD4_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (packingD4 u v x y p q a b c d).card = 6 := by
  let f := labels10 u v x y p q a b c d
  have hinjT : Function.Injective (mapTri f) := Finset.image_injective hinj
  rw [← packingD4_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjT, packing10_D4_card]

lemma coverD4_card (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    (coverD4 u v x y p q a b c d).card = 12 := by
  let f := labels10 u v x y p q a b c d
  have hinjE : Function.Injective (Sym2.map f) := Sym2.map.injective hinj
  rw [← coverD4_image_eq u v x y p q a b c d,
    card_image_of_injective _ hinjE, cover10_D4_card]

lemma packingD4_disjoint (u v x y p q a b c d : V)
    (hinj : Function.Injective (labels10 u v x y p q a b c d)) :
    ∀ σ ∈ packingD4 u v x y p q a b c d,
      ∀ τ ∈ packingD4 u v x y p q a b c d,
        σ ≠ τ → Disjoint (triEdges σ) (triEdges τ) := by
  intro σ hs τ ht hst
  rw [← packingD4_image_eq u v x y p q a b c d] at hs ht
  obtain ⟨s0, hs0, rfl⟩ := mem_image.1 hs
  obtain ⟨t0, ht0, rfl⟩ := mem_image.1 ht
  exact packing53G_disjoint_of_pairwise u v x y p q a b c d hinj
    packing10_D4 packing10_D4_pairwise _ _ s0 t0 hs0 ht0
    (fun h => by subst h; exact hst rfl) rfl rfl

/-- **Prop 6.2 certificate D4**: private edge `ab`, outside triangle `xpa`, matching `yc,qd`. -/
theorem diamond_certificate_D4 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hxa : G.Adj x a) (hpa : G.Adj p a) (hab : G.Adj a b)
    (hyc : G.Adj y c) (hqd : G.Adj q d)
    (hnxb : ¬ G.Adj x b) (hnpb : ¬ G.Adj p b) (hnqc : ¬ G.Adj q c)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  let hinj := labels10_injective H.u H.v x y p q a b c d h10
  let f := labels10 H.u H.v x y p q a b c d
  let S := packingD4 H.u H.v x y p q a b c d
  let X := coverD4 H.u H.v x y p q a b c d
  have inj_ne {i j : Fin 10} (hij : i ≠ j) : f i ≠ f j := fun h => hij (hinj h)
  have uvs : G.Adj H.u H.v := H.huv
  have ux : G.Adj H.u x := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uy : G.Adj H.u y := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have up : G.Adj H.u p := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have uq : G.Adj H.u q := hub_adj_CA G H (mem_union_left _ (by rw [hC]; simp))
  have ua : G.Adj H.u a := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have ub : G.Adj H.u b := hub_adj_CA G H (mem_union_right _ (by rw [hA]; simp))
  have vx : G.Adj H.v x := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vy : G.Adj H.v y := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vp : G.Adj H.v p := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vq : G.Adj H.v q := hub_adj_CB G H (mem_union_left _ (by rw [hC]; simp))
  have vc : G.Adj H.v c := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  have vd : G.Adj H.v d := hub_adj_CB G H (mem_union_right _ (by rw [hB]; simp))
  obtain ⟨hxy, hxp', hxq', hyp', hyq', hpq'⟩ := core4_distinct G H hC
  have c3 {a0 b0 c0 : V} (hab0 : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
      ({a0, b0, c0} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab0, hac]),
      card_insert_of_notMem (by simp [hbc]), card_singleton]
  have c_uvx : ({H.u, H.v, x} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 1)) (inj_ne (by decide : (0:Fin 10) ≠ 2))
      (inj_ne (by decide : (1:Fin 10) ≠ 2))
  have c_uyq : ({H.u, y, q} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 3)) (inj_ne (by decide : (0:Fin 10) ≠ 5)) hyq'
  have c_uab : ({H.u, a, b} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (0:Fin 10) ≠ 6)) (inj_ne (by decide : (0:Fin 10) ≠ 7))
      (inj_ne (by decide : (6:Fin 10) ≠ 7))
  have c_vyc : ({H.v, y, c} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 3)) (inj_ne (by decide : (1:Fin 10) ≠ 8))
      (inj_ne (by decide : (3:Fin 10) ≠ 8))
  have c_vqd : ({H.v, q, d} : Finset V).card = 3 :=
    c3 (inj_ne (by decide : (1:Fin 10) ≠ 5)) (inj_ne (by decide : (1:Fin 10) ≠ 9))
      (inj_ne (by decide : (5:Fin 10) ≠ 9))
  have c_xpa : ({x, p, a} : Finset V).card = 3 :=
    c3 hxp' (inj_ne (by decide : (2:Fin 10) ≠ 6)) (inj_ne (by decide : (4:Fin 10) ≠ 6))
  have hpack : IsTrianglePacking G S := by
    refine ⟨?_, packingD4_disjoint H.u H.v x y p q a b c d hinj⟩
    intro t ht
    simp only [S, packingD4, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact is3clique_of_adj G uvs ux vx c_uvx
    · exact is3clique_of_adj G uy uq hK.2.2.2.1 c_uyq
    · exact is3clique_of_adj G ua ub hab c_uab
    · exact is3clique_of_adj G vy vc hyc c_vyc
    · exact is3clique_of_adj G vq vd hqd c_vqd
    · exact is3clique_of_adj G hK.1 hxa hpa c_xpa
  have hXedges : ∀ e ∈ X, e ∈ G.edgeFinset := by
    intro e he
    simp only [X, coverD4, mem_insert, mem_singleton] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact (mem_edgeFinset).2 hK.1
    · subst h; exact (mem_edgeFinset).2 hxa
    · subst h; exact (mem_edgeFinset).2 hpa
    · subst h; exact (mem_edgeFinset).2 hK.2.2.2.1
    · subst h; exact (mem_edgeFinset).2 hyc
    · subst h; exact (mem_edgeFinset).2 hqd
    · subst h; exact (mem_edgeFinset).2 hab
    · subst h; exact (mem_edgeFinset).2 uy
    · subst h; exact (mem_edgeFinset).2 uq
    · subst h; exact (mem_edgeFinset).2 vx
    · subst h; exact (mem_edgeFinset).2 vp
    · subst h; exact (mem_edgeFinset).2 vd
  have hcardS := packingD4_card H.u H.v x y p q a b c d hinj
  have hcardX := coverD4_card H.u H.v x y p q a b c d hinj
  have hsize : X.card ≤ 2 * S.card := by
    have hS : S.card = 6 := hcardS
    have hX : X.card = 12 := hcardX
    omega
  have hexternal : ∀ t ∈ S, ∀ e ∈ triEdges t,
      (∀ zz ∈ ({H.u, H.v} : Finset V), zz ∉ e) → e ∈ X := by
    intro t ht e he hZ
    have hu : H.u ∉ e := hZ H.u (by simp)
    have hv : H.v ∉ e := hZ H.v (by simp)
    simp only [S, packingD4, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have h := triEdges_omit_vertex c_uvx he hu; rw [h]; simp [X, coverD4]
    · have h := triEdges_omit_vertex c_uyq he hu; rw [h]; simp [X, coverD4]
    · have h := triEdges_omit_vertex c_uab he hu; rw [h]; simp [X, coverD4]
    · have h := triEdges_omit_vertex c_vyc he hv; rw [h]; simp [X, coverD4]
    · have h := triEdges_omit_vertex c_vqd he hv; rw [h]; simp [X, coverD4]
    · have he' : e ∈ triEdges ({x, p, a} : Finset V) := he
      rw [triEdges_eq_of_card3 c_xpa] at he'
      simp only [mem_insert, mem_singleton] at he'
      rcases he' with h | h | h <;> simp [X, coverD4, h, Sym2.eq_swap]
  -- coversZ: mirror D2 (spokes uy,uq,vx,vp; rims {x,p,a,b} / {y,q,c})
  have hcoversZ : ∀ t ∈ G.cliqueFinset 3, (∃ zz ∈ ({H.u, H.v} : Finset V), zz ∈ t) →
      ¬ Disjoint X (triEdges t) := by
    intro t ht hZmeet
    classical
    obtain ⟨hub, hhub, hhubt⟩ := hZmeet
    simp only [mem_insert, mem_singleton] at hhub
    have hN : G.IsNClique 3 t := (mem_cliqueFinset_iff).1 ht
    have hcard : t.card = 3 := hN.card_eq
    have hadj : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G.Adj a b :=
      fun a ha b hb hab => hN.isClique ha hb hab
    have herase : (t.erase hub).card = 2 := by rw [card_erase_of_mem hhubt, hcard]
    rcases (card_eq_two (s := t.erase hub)).1 herase with ⟨px, py, hpxy, ht_erase⟩
    have hpx_erase : px ∈ t.erase hub := by rw [ht_erase]; exact mem_insert_self _ _
    have hpy_erase : py ∈ t.erase hub := by rw [ht_erase]; simp
    have ht_eq : t = {hub, px, py} := by
      ext q; constructor
      · intro hq
        by_cases hqz : q = hub
        · simp [hqz]
        · have hq' : q ∈ t.erase hub := mem_erase.2 ⟨hqz, hq⟩
          rw [ht_erase] at hq'; exact mem_insert_of_mem hq'
      · intro hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hhubt
        · exact (mem_erase.1 hpx_erase).2
        · exact (mem_erase.1 hpy_erase).2
    have hx_ne : px ≠ hub := (mem_erase.1 hpx_erase).1
    have hy_ne : py ≠ hub := (mem_erase.1 hpy_erase).1
    have hxyt : px ∈ t := (mem_erase.1 hpx_erase).2
    have hyyt : py ∈ t := (mem_erase.1 hpy_erase).2
    have hcard3 : ({hub, px, py} : Finset V).card = 3 := by
      simp [card_insert_of_notMem, hx_ne.symm, hy_ne.symm, hpxy]
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
    have hxyAdj : G.Adj px py := hadj px hxyt py hyyt hpxy
    have core4 (w : V) (hw : w ∈ H.C) : w = x ∨ w = y ∨ w = p ∨ w = q := by
      simpa [hC] using hw
    have not_A_adj_v (w : V) (hwA : w ∈ H.A) (hvw : G.Adj H.v w) : False :=
      not_adj_hub_priv G H hwA hvw
    have not_B_adj_u (w : V) (hwB : w ∈ H.B) (huw : G.Adj H.u w) : False := by
      have hwN : w ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 huw
      have : w ∈ insert H.v (H.C ∪ H.A) := by rwa [H.hNu] at hwN
      have hvB : H.v ∉ H.B := fun h => by
        have : H.v ∈ G.neighborFinset H.v := by
          rw [H.hNv]; exact mem_insert_of_mem (mem_union_right _ h)
        exact G.irrefl ((G.mem_neighborFinset _ _).1 this)
      have hwne : w ≠ H.v := fun eq => hvB (eq ▸ hwB)
      have hwCA : w ∈ H.C ∪ H.A := (mem_insert.1 this).resolve_left hwne
      rcases mem_union.1 hwCA with hwC | hwA
      · exact Finset.disjoint_left.1 H.hBdisj hwB hwC
      · exact Finset.disjoint_left.1 H.hABdisj hwA hwB
    rcases hhub with rfl | rfl
    · have hxN : px ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.u := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNu] at hxN hyN
      by_cases hxv : px = H.v
      · subst hxv
        have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hpxy.symm
        rcases mem_union.1 hyCA with hyC | hyA
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (by simp [X, coverD4]) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, y) (by simp [X, coverD4]) (by simpa [hpy] using him_zy)
          · exact meet s(H.v, p) (by simp [X, coverD4]) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, q) (by simp [X, coverD4]) (by simpa [hpy] using him_zy)
        · exact False.elim (not_A_adj_v py hyA hxyAdj)
      by_cases hyv : py = H.v
      · subst hyv
        have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hpxy
        rcases mem_union.1 hxCA with hxC | hxA
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (by simp [X, coverD4]) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, y) (by simp [X, coverD4]) (by simpa [hpx] using him_zx)
          · exact meet s(H.v, p) (by simp [X, coverD4]) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.u, q) (by simp [X, coverD4]) (by simpa [hpx] using him_zx)
        · exact False.elim (not_A_adj_v px hxA hxyAdj.symm)
      have hxCA : px ∈ H.C ∪ H.A := (mem_insert.1 hxN).resolve_left hxv
      have hyCA : py ∈ H.C ∪ H.A := (mem_insert.1 hyN).resolve_left hyv
      by_cases hxy_y : px = y
      · exact meet s(H.u, y) (by simp [X, coverD4]) (hxy_y ▸ him_zx)
      by_cases hyy : py = y
      · exact meet s(H.u, y) (by simp [X, coverD4]) (hyy ▸ him_zy)
      by_cases hxq : px = q
      · exact meet s(H.u, q) (by simp [X, coverD4]) (hxq ▸ him_zx)
      by_cases hyq : py = q
      · exact meet s(H.u, q) (by simp [X, coverD4]) (hyq ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.A) (hny : w ≠ y) (hnq : w ≠ q) :
          w = x ∨ w = p ∨ w = a ∨ w = b := by
        rcases mem_union.1 hwN with hwC | hwA
        · rcases core4 w hwC with h | h | h | h
          · exact Or.inl h
          · exact False.elim (hny h)
          · exact Or.inr (Or.inl h)
          · exact False.elim (hnq h)
        · have : w = a ∨ w = b := by simpa [hA] using hwA
          rcases this with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      have hpxR := inRim px hxCA hxy_y hxq
      have hpyR := inRim py hyCA hyy hyq
      have nxb_of (hA' : G.Adj x b) : False := hnxb hA'
      have npb_of (hA' : G.Adj p b) : False := hnpb hA'
      rcases hpxR with hpx | hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(x, p) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(x, a) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nxb_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, p) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(p, a) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (npb_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(x, a) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact meet s(p, a) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(a, b) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact False.elim (nxb_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact False.elim (npb_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact meet s(a, b) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
    · have hxN : px ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzx
      have hyN : py ∈ G.neighborFinset H.v := (G.mem_neighborFinset _ _).2 hzy
      rw [H.hNv] at hxN hyN
      by_cases hxu : px = H.u
      · subst hxu
        have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hpxy.symm
        rcases mem_union.1 hyCB with hyC | hyB
        · rcases core4 py hyC with hpy | hpy | hpy | hpy
          · exact meet s(H.v, x) (by simp [X, coverD4]) (by simpa [hpy] using him_zy)
          · exact meet s(H.u, y) (by simp [X, coverD4]) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
          · exact meet s(H.v, p) (by simp [X, coverD4]) (by simpa [hpy] using him_zy)
          · exact meet s(H.u, q) (by simp [X, coverD4]) (by
              simpa [hpy, Sym2.eq_swap] using him_rim)
        · exact False.elim (not_B_adj_u py hyB hxyAdj)
      by_cases hyu : py = H.u
      · subst hyu
        have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hpxy
        rcases mem_union.1 hxCB with hxC | hxB
        · rcases core4 px hxC with hpx | hpx | hpx | hpx
          · exact meet s(H.v, x) (by simp [X, coverD4]) (by simpa [hpx] using him_zx)
          · exact meet s(H.u, y) (by simp [X, coverD4]) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
          · exact meet s(H.v, p) (by simp [X, coverD4]) (by simpa [hpx] using him_zx)
          · exact meet s(H.u, q) (by simp [X, coverD4]) (by
              simpa [hpx, Sym2.eq_swap] using him_rim)
        · exact False.elim (not_B_adj_u px hxB hxyAdj.symm)
      have hxCB : px ∈ H.C ∪ H.B := (mem_insert.1 hxN).resolve_left hxu
      have hyCB : py ∈ H.C ∪ H.B := (mem_insert.1 hyN).resolve_left hyu
      by_cases hxx : px = x
      · exact meet s(H.v, x) (by simp [X, coverD4]) (hxx ▸ him_zx)
      by_cases hyx : py = x
      · exact meet s(H.v, x) (by simp [X, coverD4]) (hyx ▸ him_zy)
      by_cases hxp : px = p
      · exact meet s(H.v, p) (by simp [X, coverD4]) (hxp ▸ him_zx)
      by_cases hyp : py = p
      · exact meet s(H.v, p) (by simp [X, coverD4]) (hyp ▸ him_zy)
      by_cases hxd : px = d
      · exact meet s(H.v, d) (by simp [X, coverD4]) (hxd ▸ him_zx)
      by_cases hyd : py = d
      · exact meet s(H.v, d) (by simp [X, coverD4]) (hyd ▸ him_zy)
      have inRim (w : V) (hwN : w ∈ H.C ∪ H.B)
          (hnx : w ≠ x) (hnp : w ≠ p) (hnd : w ≠ d) : w = y ∨ w = q ∨ w = c := by
        rcases mem_union.1 hwN with hwC | hwB
        · rcases core4 w hwC with h | h | h | h
          · exact False.elim (hnx h)
          · exact Or.inl h
          · exact False.elim (hnp h)
          · exact Or.inr (Or.inl h)
        · have : w = c ∨ w = d := by simpa [hB] using hwB
          rcases this with h | h
          · exact Or.inr (Or.inr h)
          · exact False.elim (hnd h)
      have hpxR := inRim px hxCB hxx hxp hxd
      have hpyR := inRim py hyCB hyx hyp hyd
      have nqc_of (hA' : G.Adj q c) : False := hnqc hA'
      rcases hpxR with hpx | hpx | hpx <;> rcases hpyR with hpy | hpy | hpy
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact meet s(y, q) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(y, c) (by simp [X, coverD4]) (by simpa [hpx, hpy] using him_rim)
      · exact meet s(y, q) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact absurd (hpx.trans hpy.symm) hpxy
      · exact False.elim (nqc_of (by simpa [hpx, hpy] using hxyAdj))
      · exact meet s(y, c) (by simp [X, coverD4]) (by simpa [hpx, hpy, Sym2.eq_swap] using him_rim)
      · exact False.elim (nqc_of (by simpa [hpx, hpy] using hxyAdj.symm))
      · exact absurd (hpx.trans hpy.symm) hpxy
  exact ⟨{
    packing := S
    cover := X
    isPacking := hpack
    cover_edges := hXedges
    size := hsize
    coversZ := hcoversZ
    external := hexternal
  }⟩

/-- Full A/B support on a diamond from Lemma 6.1 on both links. -/
theorem diamond_full_support (H : HubConfig G) (hA1 : H.A1)
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hyq : G.Adj y q) :
    (∀ c ∈ H.C, ∃ a ∈ H.A, G.Adj c a) ∧ (∀ c ∈ H.C, ∃ b ∈ H.B, G.Adj c b) := by
  refine ⟨?_, ?_⟩
  · exact lemma61 G H hA1.1 hA1.2.1 hC hxp hyq
  · have hsw : H.swap.A1 := hA1.swap
    have hC' : H.swap.C = {x, y, p, q} := hC
    have h := lemma61 G H.swap hsw.1 hsw.2.1 hC' hxp hyq
    intro c hc
    obtain ⟨b, hb, hadj⟩ := h c hc
    exact ⟨b, hb, hadj⟩

/-- Centres `p,q` of a diamond have unique A/B neighbours (coreDeg 3 + (A2) + support). -/
theorem diamond_center_unique (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) :
    (∀ c ∈ ({p, q} : Finset V), ∃! a, a ∈ H.A ∧ G.Adj c a) ∧
    (∀ c ∈ ({p, q} : Finset V), ∃! b, b ∈ H.B ∧ G.Adj c b) := by
  classical
  obtain ⟨hsuppA, hsuppB⟩ := diamond_full_support G H hA1 hC hxp hyq
  have coreDeg3 : ∀ c ∈ ({p, q} : Finset V), H.coreDeg c = 3 := by
    intro c hc
    unfold HubConfig.coreDeg
    have hcC : c ∈ H.C := by
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [hC]
    have hadj_all : ∀ t ∈ H.C.erase c, G.Adj c t := by
      intro t ht
      have htC : t ∈ H.C := (mem_erase.1 ht).2
      have hne : t ≠ c := (mem_erase.1 ht).1
      have ht' : t = x ∨ t = y ∨ t = p ∨ t = q := by simpa [hC] using htC
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl
      · -- c = p; neighbours x,y,q
        rcases ht' with rfl | rfl | rfl | rfl
        · exact hxp.symm
        · exact hyp.symm
        · exact absurd rfl hne.symm
        · exact hpq
      · -- c = q; neighbours x,y,p
        rcases ht' with rfl | rfl | rfl | rfl
        · exact hxq.symm
        · exact hyq.symm
        · exact hpq.symm
        · exact absurd rfl hne.symm
    have hfilter : (H.C.erase c).filter (G.Adj c) = H.C.erase c := by
      ext t; simp only [mem_filter]; constructor
      · exact And.left
      · intro ht; exact ⟨ht, hadj_all t ht⟩
    rw [hfilter, card_erase_of_mem hcC, H.hCcard]
  refine ⟨?_, ?_⟩
  · intro c hc
    have hcC : c ∈ H.C := by
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [hC]
    have hneA : (G.neighborFinset c ∩ H.A).Nonempty := by
      obtain ⟨a, ha, hadj⟩ := hsuppA c hcC
      exact ⟨a, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, ha⟩⟩
    have hneB : (G.neighborFinset c ∩ H.B).Nonempty := by
      obtain ⟨b, hb, hadj⟩ := hsuppB c hcC
      exact ⟨b, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hb⟩⟩
    have hAcard : (G.neighborFinset c ∩ H.A).card = 1 := by
      have hA2c := hA2 c hcC
      have hde := coreDeg3 c hc
      have hApos : 1 ≤ (G.neighborFinset c ∩ H.A).card := Finset.card_pos.2 hneA
      have hBpos : 1 ≤ (G.neighborFinset c ∩ H.B).card := Finset.card_pos.2 hneB
      omega
    obtain ⟨a, ha⟩ := (card_eq_one (s := G.neighborFinset c ∩ H.A)).1 hAcard
    refine ⟨a, ?_, ?_⟩
    · have : a ∈ G.neighborFinset c ∩ H.A := by simp [ha]
      exact ⟨(mem_inter.1 this).2, (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1⟩
    · intro a' ⟨ha'A, hadj⟩
      have : a' ∈ G.neighborFinset c ∩ H.A :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, ha'A⟩
      simpa [ha] using this
  · intro c hc
    have hcC : c ∈ H.C := by
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [hC]
    have hneA : (G.neighborFinset c ∩ H.A).Nonempty := by
      obtain ⟨a, ha, hadj⟩ := hsuppA c hcC
      exact ⟨a, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, ha⟩⟩
    have hneB : (G.neighborFinset c ∩ H.B).Nonempty := by
      obtain ⟨b, hb, hadj⟩ := hsuppB c hcC
      exact ⟨b, mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hb⟩⟩
    have hBcard : (G.neighborFinset c ∩ H.B).card = 1 := by
      have hA2c := hA2 c hcC
      have hde := coreDeg3 c hc
      have hApos : 1 ≤ (G.neighborFinset c ∩ H.A).card := Finset.card_pos.2 hneA
      have hBpos : 1 ≤ (G.neighborFinset c ∩ H.B).card := Finset.card_pos.2 hneB
      omega
    obtain ⟨b, hb⟩ := (card_eq_one (s := G.neighborFinset c ∩ H.B)).1 hBcard
    refine ⟨b, ?_, ?_⟩
    · have : b ∈ G.neighborFinset c ∩ H.B := by simp [hb]
      exact ⟨(mem_inter.1 this).2, (G.mem_neighborFinset _ _).1 (mem_inter.1 this).1⟩
    · intro b' ⟨hb'B, hadj⟩
      have : b' ∈ G.neighborFinset c ∩ H.B :=
        mem_inter.2 ⟨(G.mem_neighborFinset _ _).2 hadj, hb'B⟩
      simpa [hb] using this





/-- Membership helper: permute Finset10 without heavy `or_comm` simp. -/
private lemma mem10_iff {u v x y p q a b c d z : V} :
    z ∈ ({u, v, x, y, p, q, a, b, c, d} : Finset V) ↔
      z = u ∨ z = v ∨ z = x ∨ z = y ∨ z = p ∨ z = q ∨ z = a ∨ z = b ∨ z = c ∨ z = d := by
  simp only [mem_insert, mem_singleton]

private lemma card10_of_same_elems {u v x y p q a b c d : V}
    {s : Finset V}
    (hin : ∀ z, z ∈ s → z = u ∨ z = v ∨ z = x ∨ z = y ∨ z = p ∨ z = q ∨
      z = a ∨ z = b ∨ z = c ∨ z = d)
    (hout : ∀ z, (z = u ∨ z = v ∨ z = x ∨ z = y ∨ z = p ∨ z = q ∨
      z = a ∨ z = b ∨ z = c ∨ z = d) → z ∈ s)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    s.card = 10 := by
  have heq : s = {u, v, x, y, p, q, a, b, c, d} := by
    ext z; constructor
    · intro hz; simpa [mem10_iff] using hin z hz
    · intro hz; exact hout z (by simpa [mem10_iff] using hz)
  rwa [heq]

set_option maxHeartbeats 4000000 in
lemma labels10_swapA (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, x, y, p, q, b, a, c, d} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

lemma labels10_swapLeaves (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, y, x, p, q, a, b, c, d} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

lemma labels10_swapCenters (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, x, y, q, p, a, b, c, d} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

lemma labels10_swapLeavesCenters (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, y, x, q, p, a, b, c, d} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

lemma labels10_swapB (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, x, y, p, q, a, b, d, c} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

lemma labels10_swapHubsAB (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({v, u, x, y, p, q, c, d, a, b} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h

private lemma core4_perm_leaves {x y p q : V} {C : Finset V}
    (hC : C = {x, y, p, q}) : C = {y, x, p, q} := by
  rw [hC]; ext z; simp only [mem_insert, mem_singleton]; constructor
  · rintro (h | h | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

private lemma core4_perm_centers {x y p q : V} {C : Finset V}
    (hC : C = {x, y, p, q}) : C = {x, y, q, p} := by
  rw [hC]; ext z; simp only [mem_insert, mem_singleton]; constructor
  · rintro (h | h | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

private lemma core4_perm_leaves_centers {x y p q : V} {C : Finset V}
    (hC : C = {x, y, p, q}) : C = {y, x, q, p} := by
  rw [hC]; ext z; simp only [mem_insert, mem_singleton]; constructor
  · rintro (h | h | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [h]

private lemma A_perm {a b : V} {A : Finset V} (hA : A = {a, b}) : A = {b, a} := by
  rw [hA]; ext z; simp only [mem_insert, mem_singleton]; constructor
  · rintro (h | h) <;> simp [h]
  · rintro (h | h) <;> simp [h]

private lemma B_perm {c d : V} {B : Finset V} (hB : B = {c, d}) : B = {d, c} := by
  rw [hB]; ext z; simp only [mem_insert, mem_singleton]; constructor
  · rintro (h | h) <;> simp [h]
  · rintro (h | h) <;> simp [h]

/-- Apply D1 after choosing opposite-side neighbour of the missed leaf. -/
lemma diamond_D1_with_Bsupport (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q)
    (hnxy : ¬ G.Adj x y)
    (hxa : G.Adj x a) (hnya : ¬ G.Adj y a) (hnpa : ¬ G.Adj p a)
    (hsuppBy : ∃ β ∈ H.B, G.Adj y β)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨β, hβB, hyβ⟩ := hsuppBy
  have hβ : β = c ∨ β = d := by simpa [hB] using hβB
  rcases hβ with hβc | hβd
  · rw [hβc] at hyβ
    exact diamond_certificate_D1 G H x y p q a b c d hC hA hB hK hnxy
      hxa hyβ hnya hnpa h10
  · rw [hβd] at hyβ
    exact diamond_certificate_D1 G H x y p q a b d c hC hA (B_perm hB) hK hnxy
      hxa hyβ hnya hnpa (labels10_swapB _ _ _ _ _ _ _ _ _ _ h10)

set_option maxHeartbeats 4000000 in
/-- D1 after orienting an A-private that hits exactly one leaf and misses a centre. -/
lemma diamond_force_D1_Apriv (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) (hnxy : ¬ G.Adj x y)
    (hsuppB : ∀ t ∈ H.C, ∃ β ∈ H.B, G.Adj t β)
    (w : V) (hwA : w ∈ H.A)
    (hleaf : (G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w))
    (hmiss : ¬ G.Adj p w ∨ ¬ G.Adj q w)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  have hw : w = a ∨ w = b := by simpa [hA] using hwA
  rcases hw with hw | hw <;> subst w
  · rcases hleaf with ⟨hxa, hnya⟩ | ⟨hya, hnxa⟩
    · rcases hmiss with hnpa | hnqa
      · exact diamond_D1_with_Bsupport G H x y p q a b c d hC hA hB
          ⟨hxp, hxq, hyp, hyq, hpq⟩ hnxy hxa hnya hnpa
          (hsuppB y (by simp [hC])) h10
      · exact diamond_D1_with_Bsupport G H x y q p a b c d (core4_perm_centers hC) hA hB
          ⟨hxq, hxp, hyq, hyp, hpq.symm⟩ hnxy hxa hnya hnqa
          (hsuppB y (by simp [hC])) (labels10_swapCenters _ _ _ _ _ _ _ _ _ _ h10)
    · rcases hmiss with hnpa | hnqa
      · exact diamond_D1_with_Bsupport G H y x p q a b c d (core4_perm_leaves hC) hA hB
          ⟨hyp, hyq, hxp, hxq, hpq⟩ (fun e => hnxy e.symm) hya hnxa hnpa
          (hsuppB x (by simp [hC])) (labels10_swapLeaves _ _ _ _ _ _ _ _ _ _ h10)
      · exact diamond_D1_with_Bsupport G H y x q p a b c d
          (core4_perm_leaves_centers hC) hA hB
          ⟨hyq, hyp, hxq, hxp, hpq.symm⟩ (fun e => hnxy e.symm) hya hnxa hnqa
          (hsuppB x (by simp [hC]))
          (labels10_swapLeavesCenters _ _ _ _ _ _ _ _ _ _ h10)
  · have h10' := labels10_swapA H.u H.v x y p q a b c d h10
    rcases hleaf with ⟨hxb, hnyb⟩ | ⟨hyb, hnxb⟩
    · rcases hmiss with hnpb | hnqb
      · exact diamond_D1_with_Bsupport G H x y p q b a c d hC (A_perm hA) hB
          ⟨hxp, hxq, hyp, hyq, hpq⟩ hnxy hxb hnyb hnpb
          (hsuppB y (by simp [hC])) h10'
      · exact diamond_D1_with_Bsupport G H x y q p b a c d
          (core4_perm_centers hC) (A_perm hA) hB
          ⟨hxq, hxp, hyq, hyp, hpq.symm⟩ hnxy hxb hnyb hnqb
          (hsuppB y (by simp [hC])) (labels10_swapCenters _ _ _ _ _ _ _ _ _ _ h10')
    · rcases hmiss with hnpb | hnqb
      · exact diamond_D1_with_Bsupport G H y x p q b a c d
          (core4_perm_leaves hC) (A_perm hA) hB
          ⟨hyp, hyq, hxp, hxq, hpq⟩ (fun e => hnxy e.symm) hyb hnxb hnpb
          (hsuppB x (by simp [hC])) (labels10_swapLeaves _ _ _ _ _ _ _ _ _ _ h10')
      · exact diamond_D1_with_Bsupport G H y x q p b a c d
          (core4_perm_leaves_centers hC) (A_perm hA) hB
          ⟨hyq, hyp, hxq, hxp, hpq.symm⟩ (fun e => hnxy e.symm) hyb hnxb hnqb
          (hsuppB x (by simp [hC]))
          (labels10_swapLeavesCenters _ _ _ _ _ _ _ _ _ _ h10')

set_option maxHeartbeats 4000000 in
/-- D1 when the exceptional private lies in `B`, via `H.swap`. -/
lemma diamond_force_D1_Bpriv (H : HubConfig G) (hA1 : H.A1)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) (hnxy : ¬ G.Adj x y)
    (hsuppA : ∀ t ∈ H.C, ∃ α ∈ H.A, G.Adj t α)
    (w : V) (hwB : w ∈ H.B)
    (hleaf : (G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w))
    (hmiss : ¬ G.Adj p w ∨ ¬ G.Adj q w)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  have hC' : H.swap.C = {x, y, p, q} := hC
  have hA' : H.swap.A = {c, d} := hB
  have hB' : H.swap.B = {a, b} := hA
  have h10' : ({H.swap.u, H.swap.v, x, y, p, q, c, d, a, b} : Finset V).card = 10 := by
    simp only [HubConfig.swap]
    exact labels10_swapHubsAB _ _ _ _ _ _ _ _ _ _ h10
  have hsuppBsw : ∀ t ∈ H.swap.C, ∃ β ∈ H.swap.B, G.Adj t β := by
    intro t ht; simpa [HubConfig.swap] using hsuppA t ht
  have hwA' : w ∈ H.swap.A := by simpa [HubConfig.swap] using hwB
  have h := diamond_force_D1_Apriv G H.swap x y p q c d a b hC' hA' hB'
    hxp hxq hyp hyq hpq hnxy hsuppBsw w hwA' hleaf hmiss h10'
  simpa [HubConfig.swap, Finset.pair_comm] using h


lemma labels10_swapCentersB (u v x y p q a b c d : V)
    (h : ({u, v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    ({u, v, x, y, q, p, a, b, d, c} : Finset V).card = 10 :=
  card10_of_same_elems
    (fun z hz => by
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h])
    (fun z hz => by
      rcases hz with h | h | h | h | h | h | h | h | h | h <;> simp [h]) h


set_option maxHeartbeats 4000000 in
/-- Sparse split on A (oriented): `pa,qb,xa,ya` / `¬qa,¬pb,¬xb,¬yb`; unique B-nbr of `p` is `c`. -/
lemma diamond_sparse_split_A (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) (hnxy : ¬ G.Adj x y)
    (hpa : G.Adj p a) (hqb : G.Adj q b)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hnqa : ¬ G.Adj q a) (hnpb : ¬ G.Adj p b)
    (hnxb : ¬ G.Adj x b) (hnyb : ¬ G.Adj y b)
    (hpc : G.Adj p c) (hnpd : ¬ G.Adj p d)
    (hnxd : ¬ G.Adj x d)  -- follows from (3) when ¬yd; required for D3
    (hxc : G.Adj x c)     -- forced by support when xd absent
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  by_cases hyd : G.Adj y d
  · exact diamond_certificate_D2 G H x y q p a b d c
      (core4_perm_centers hC) hA (B_perm hB)
      ⟨hxq, hxp, hyq, hyp, hpq.symm⟩ hnxy
      hxa hqb hyd hpc hnqa hnxb hnpd
      (labels10_swapCentersB _ _ _ _ _ _ _ _ _ _ h10)
  · -- D3: ya, xc; b and d miss {x,y,p}
    exact diamond_certificate_D3 G H x y p q a b c d hC hA hB
      ⟨hxp, hxq, hyp, hyq, hpq⟩ hnxy hya hxc
      (fun w hw => by
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact fun h => hnxb h.symm
        · exact fun h => hnyb h.symm
        · exact fun h => hnpb h.symm)
      (fun w hw => by
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact fun h => hnxd h.symm
        · exact fun h => hyd h.symm
        · exact fun h => hnpd h.symm)
      h10

set_option maxHeartbeats 4000000 in
/-- Both sides paired, neither weak sees a leaf → D5 after swapping B-labels so `d` is dominant. -/
lemma diamond_paired_D5 (H : HubConfig G)
    (x y p q a b c d : V)
    (hC : H.C = {x, y, p, q})
    (hA : H.A = {a, b}) (hB : H.B = {c, d})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) (hnxy : ¬ G.Adj x y)
    (hpa : G.Adj p a) (hqa : G.Adj q a)  -- a dominant
    (hpc : G.Adj p c) (hqc : G.Adj q c)  -- c dominant (before swap)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    -- after interchange c,d: d becomes the double-center attachment
    (hdp : G.Adj d p) (hdq : G.Adj d q)
    (h10 : ({H.u, H.v, x, y, p, q, a, b, c, d} : Finset V).card = 10) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  -- Paper: D5 after interchanging c,d so dominant is named d with dp,dq.
  -- If c is dominant with cp,cq, swap B labels to make d the dominant with those edges.
  -- Here we assume already oriented with dp,dq (caller swaps if needed).
  exact diamond_certificate_D5 G H x y p q a b c d hC hA hB
    ⟨hxp, hxq, hyp, hyq, hpq⟩ hnxy hab hcd hdp hdq h10

/-- **Proposition 6.2**: diamond core `{xp,xq,yp,yq,pq}` is reducible under (A1)–(A2).
Certificates D1–D5 are fully proved; the remaining work is the paper's attachment
classification that forces one of those five hypothesis packages. -/
theorem diamond_core_reducible (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2)
    {x y p q : V} (hC : H.C = {x, y, p, q})
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hyp : G.Adj y p) (hyq : G.Adj y q)
    (hpq : G.Adj p q) (hnxy : ¬ G.Adj x y)
    (honly : ∀ a ∈ H.C, ∀ b ∈ H.C, G.Adj a b →
      s(a, b) = s(x, p) ∨ s(a, b) = s(x, q) ∨ s(a, b) = s(y, p) ∨
      s(a, b) = s(y, q) ∨ s(a, b) = s(p, q)) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  classical
  obtain ⟨hsuppA, hsuppB⟩ := diamond_full_support G H hA1 hC hxp hyq
  obtain ⟨uniqA, uniqB⟩ := diamond_center_unique G H hA1 hA2 hC hxp hxq hyp hyq hpq
  obtain ⟨a, b, hneA, hAeq⟩ := (card_eq_two (s := H.A)).1 H.hA
  obtain ⟨c, d, hneB, hBeq⟩ := (card_eq_two (s := H.B)).1 H.hB
  have hC4 : ({x, y, p, q} : Finset V).card = 4 := by rw [← hC]; exact H.hCcard
  have h10 := labels10_of_hub G H hC hAeq hBeq hC4 hneA hneB
  have hK : G.Adj x p ∧ G.Adj x q ∧ G.Adj y p ∧ G.Adj y q ∧ G.Adj p q :=
    ⟨hxp, hxq, hyp, hyq, hpq⟩
  -- Condition (3) failure → D1.
  by_cases hfail3 :
      (∃ w ∈ H.A, ((G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w)) ∧
        (¬ G.Adj p w ∨ ¬ G.Adj q w)) ∨
      (∃ w ∈ H.B, ((G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w)) ∧
        (¬ G.Adj p w ∨ ¬ G.Adj q w))
  · rcases hfail3 with hAfail | hBfail
    · obtain ⟨w, hwA, hleaf, hmiss⟩ := hAfail
      exact diamond_force_D1_Apriv G H x y p q a b c d hC hAeq hBeq
        hxp hxq hyp hyq hpq hnxy hsuppB w hwA hleaf hmiss h10
    · obtain ⟨w, hwB, hleaf, hmiss⟩ := hBfail
      exact diamond_force_D1_Bpriv G H hA1 x y p q a b c d hC hAeq hBeq
        hxp hxq hyp hyq hpq hnxy hsuppA w hwB hleaf hmiss h10
  -- (3): private missing a centre does not see exactly one leaf.
  have h3A : ∀ w ∈ H.A, (¬ G.Adj p w ∨ ¬ G.Adj q w) →
      ¬ ((G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w)) := by
    intro w hw hm hleaf
    exact hfail3 (Or.inl ⟨w, hw, hleaf, hm⟩)
  have h3B : ∀ w ∈ H.B, (¬ G.Adj p w ∨ ¬ G.Adj q w) →
      ¬ ((G.Adj x w ∧ ¬ G.Adj y w) ∨ (G.Adj y w ∧ ¬ G.Adj x w)) := by
    intro w hw hm hleaf
    exact hfail3 (Or.inr ⟨w, hw, hleaf, hm⟩)
  -- Cases 1–3 under (3): sparse/dense/paired (paper pp.13–14).
  -- Ready: diamond_sparse_split_A, diamond_paired_D5; need relabel + D4 dense-split.
  sorry

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
