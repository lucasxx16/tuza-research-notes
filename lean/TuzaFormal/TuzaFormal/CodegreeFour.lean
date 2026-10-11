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


/-- **Proposition 3.1.** If a hub link satisfies (A1) connectivity/non-WKE and the core has
at most one edge, contradiction. Edgeless cores use `puleo_large_indep`; one-edge cores use
the constructive WKE witnesses once a labelling is supplied by case analysis (partial). -/
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
    have hV : Fintype.card V = 7 := by sorry
    have hWKE : IsWKE (linkGraph G H.u) :=
      puleo_large_indep (linkGraph G H.u) (by omega) hA1.1 H.C
        (by simp [hV, H.hCcard]) hind
    exact hA1.2.1 hWKE
  · -- One-edge core: needs labelling extraction then wke_private_edge / attach
    sorry

/-- **Theorem 1.3 (Structural codegree-four reduction).** -/
theorem structural_codegree_four (H : HubConfig G) (hA1 : H.A1) (hA2 : H.A2) :
    IsReducible G ({H.u, H.v} : Finset V) := by
  sorry

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

end Prop31

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

lemma packing42_card' (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    (packing42 u v c0 c1 c2 c3 a0 a1 b1).card = 5 := by
  -- Distinctness of the five triangles follows from injective labels; finish by `simp`.
  sorry

lemma packing42_disjoint (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    ∀ s ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1,
      ∀ t ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1,
        s ≠ t → Disjoint (triEdges s) (triEdges t) := by
  sorry

lemma cover42_card (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1)) :
    (cover42 u v c0 c1 c2 c3 a0 a1 b0 b1).card = 10 := by
  sorry

lemma external42 (u v c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (_hinj : Function.Injective (labels10 u v c0 c1 c2 c3 a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ packing42 u v c0 c1 c2 c3 a0 a1 b1)
    {e : Sym2 V} (he : e ∈ triEdges t)
    (hZ : ∀ z ∈ ({u, v} : Finset V), z ∉ e) :
    e ∈ cover42 u v c0 c1 c2 c3 a0 a1 b0 b1 := by
  simp only [packing42, mem_insert, mem_singleton] at ht
  have hu : u ∉ e := hZ u (by simp)
  have hv : v ∉ e := hZ v (by simp)
  -- Rim of each packed triangle lies in cover42
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    · refine Finset.mem_insert.2 ?_
      sorry

lemma coversZ42 (H : HubConfig G)
    (c0 c1 c2 c3 a0 a1 b0 b1 : V)
    (hC : H.C = {c0, c1, c2, c3})
    (hA : H.A = {a0, a1})
    (hB : H.B = {b0, b1})
    (hcore_only : ∀ x ∈ H.C, ∀ y ∈ H.C, G.Adj x y →
      s(x, y) = s(c0, c3) ∨ s(x, y) = s(c1, c2))
    (hinj : Function.Injective (labels10 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1))
    {t : Finset V} (ht : t ∈ G.cliqueFinset 3)
    (hZ : ∃ z ∈ ({H.u, H.v} : Finset V), z ∈ t) :
    ¬ Disjoint (cover42 H.u H.v c0 c1 c2 c3 a0 a1 b0 b1) (triEdges t) := by
  sorry

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

theorem lemma41_cross (H : HubConfig G)
    (_hA1u : (linkGraph G H.u).Connected ∧ ¬ IsWKE (linkGraph G H.u))
    (p0 p1 q0 q1 : V) (_hC : H.C = {p0, p1, q0, q1})
    (_hcore : G.Adj p0 p1 ∧ G.Adj q0 q1) :
    ∃ d0 d1, H.A = {d0, d1} ∧
      ((G.Adj p0 d0 ∧ G.Adj p1 d1) ∨ (G.Adj p0 d1 ∧ G.Adj p1 d0) ∨
       (G.Adj q0 d0 ∧ G.Adj q1 d1) ∨ (G.Adj q0 d1 ∧ G.Adj q1 d0)) := by
  sorry

end MatchingCore

end Tuza.CodegreeFour
