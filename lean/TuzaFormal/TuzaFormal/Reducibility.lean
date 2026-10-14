import TuzaFormal.Basic

/-!
# Reducibility framework (Defs 1.1–1.2) and the reduction bridge (Lemma 2.1)
-/

open Finset SimpleGraph

namespace Tuza

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set of edges is a matching if every edge is present and no two share a vertex. -/
def IsEdgeMatching (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset

/-- Weak König–Egerváry (Def 1.1). -/
def IsWKE : Prop :=
  ∃ (M : Finset (Sym2 V)) (Q : Finset V),
    IsEdgeMatching G M ∧ Q.card ≤ M.card ∧
    ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M

/-- Display (1): a concrete WKE witness. -/
def IsWKEWitness (M : Finset (Sym2 V)) (Q : Finset V) : Prop :=
  IsEdgeMatching G M ∧ Q.card ≤ M.card ∧
  ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∉ Q) → e ∈ M

lemma isWKE_of_witness {M : Finset (Sym2 V)} {Q : Finset V}
    (h : IsWKEWitness G M Q) : IsWKE G := ⟨M, Q, h⟩

/-- A reduction certificate for a nonempty vertex set `Z` (Def 1.2). -/
structure ReductionCertificate (Z : Finset V) where
  packing : Finset (Finset V)
  cover : Finset (Sym2 V)
  isPacking : IsTrianglePacking G packing
  /-- Cover edges are edges of `G`. -/
  cover_edges : cover ⊆ G.edgeFinset
  size : cover.card ≤ 2 * packing.card
  coversZ : ∀ t ∈ G.cliqueFinset 3, (∃ z ∈ Z, z ∈ t) → ¬ Disjoint cover (triEdges t)
  external : ∀ t ∈ packing, ∀ e ∈ triEdges t, (∀ z ∈ Z, z ∉ e) → e ∈ cover

/-- `Z` is reducible if it admits a reduction certificate. -/
def IsReducible (Z : Finset V) : Prop :=
  Z.Nonempty ∧ Nonempty (ReductionCertificate G Z)

/-- Triangles of `G` that avoid `Z` and use no edge of `X`. -/
def residualTriangles (X : Finset (Sym2 V)) (Z : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t =>
    (∀ z ∈ Z, z ∉ t) ∧ Disjoint (triEdges t) X

def IsResidualPacking (X : Finset (Sym2 V)) (Z : Finset V) (P : Finset (Finset V)) : Prop :=
  P ⊆ residualTriangles G X Z ∧
  ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint (triEdges s) (triEdges t)

def IsResidualCover (X : Finset (Sym2 V)) (Z : Finset V) (Y : Finset (Sym2 V)) : Prop :=
  Y ⊆ G.edgeFinset \ X ∧
  ∀ t ∈ residualTriangles G X Z, ¬ Disjoint Y (triEdges t)

lemma empty_packing : IsTrianglePacking G ∅ := by
  simp [IsTrianglePacking]

lemma packingNumber_le {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    P.card ≤ packingNumber G :=
  le_csSup ⟨Fintype.card (Finset V), by
    rintro _ ⟨Q, _, rfl⟩; exact card_le_card (subset_univ Q)⟩ ⟨P, hP, rfl⟩

lemma edgeFinset_cover : IsTriangleCover G G.edgeFinset := by
  refine ⟨subset_rfl, fun t ht => ?_⟩
  have hc := (mem_cliqueFinset_iff).1 ht
  obtain ⟨a, b, c, hab, _, _, rfl⟩ := is3Clique_iff.1 hc
  refine not_disjoint_iff_nonempty_inter.2 ⟨s(a, b), mem_inter.2 ⟨?_, ?_⟩⟩
  · exact (mem_edgeFinset).2 hab
  · simp only [triEdges, mem_filter, mem_sym2_iff, Sym2.mk_isDiag_iff, true_and]
    exact ⟨by simp, hab.ne⟩

lemma coverNumber_le {X : Finset (Sym2 V)} (hX : IsTriangleCover G X) :
    coverNumber G ≤ X.card :=
  Nat.sInf_le ⟨X, hX, rfl⟩

lemma mem_triEdges_imp_mem {t : Finset V} {e : Sym2 V} (he : e ∈ triEdges t) :
    ∀ x ∈ e, x ∈ t := by
  intro x hx
  simp only [triEdges, mem_filter] at he
  exact (mem_sym2_iff.1 he.1) x hx

lemma triEdges_of_adj {a b c : V} (hab : a ≠ b) :
    s(a, b) ∈ triEdges ({a, b, c} : Finset V) := by
  simp [triEdges, mem_sym2_iff, Sym2.mk_isDiag_iff, hab]

/-- Edges of a packed triangle that avoid `Z` lie in the certificate cover. -/
lemma packing_edge_in_cover {Z : Finset V} (cert : ReductionCertificate G Z)
    {t : Finset V} (ht : t ∈ cert.packing) {e : Sym2 V}
    (he : e ∈ triEdges t) (hZ : ∀ z ∈ Z, z ∉ e) : e ∈ cert.cover :=
  cert.external t ht e he hZ

/-- A residual packing and the certificate packing are disjoint as sets of triangles. -/
lemma residual_packing_disj {Z : Finset V} (cert : ReductionCertificate G Z)
    {P : Finset (Finset V)} (hP : IsResidualPacking G cert.cover Z P) :
    Disjoint cert.packing P := by
  rw [Finset.disjoint_left]
  intro t htS htP
  have htRes := mem_filter.1 (hP.1 htP)
  have hclique := cert.isPacking.1 htS
  obtain ⟨a, b, c, hab, _, _, rfl⟩ := is3Clique_iff.1 ((mem_cliqueFinset_iff).1 hclique)
  have he : s(a, b) ∈ triEdges ({a, b, c} : Finset V) := triEdges_of_adj (Adj.ne hab)
  have hAvoid : ∀ z ∈ Z, z ∉ s(a, b) := by
    intro z hz hz'
    have zin : z ∈ ({a, b, c} : Finset V) := by
      simp only [Sym2.mem_iff] at hz'
      rcases hz' with rfl | rfl <;> simp
    exact htRes.2.1 z hz zin
  have heX := cert.external _ htS _ he hAvoid
  exact (Finset.disjoint_left.1 htRes.2.2) he heX

/-- Combined packing from a certificate and a residual packing. -/
lemma combine_packing {Z : Finset V} (cert : ReductionCertificate G Z)
    {P : Finset (Finset V)} (hP : IsResidualPacking G cert.cover Z P) :
    IsTrianglePacking G (cert.packing ∪ P) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases mem_union.1 ht with h | h
    · exact cert.isPacking.1 h
    · exact (mem_filter.1 (hP.1 h)).1
  · intro s hs t ht hst
    rcases mem_union.1 hs with hsS | hsP <;> rcases mem_union.1 ht with htS | htP
    · exact cert.isPacking.2 s hsS t htS hst
    · -- s ∈ S, t ∈ residual: no shared edge
      rw [Finset.disjoint_left]
      intro e heS heP
      have htRes := mem_filter.1 (hP.1 htP)
      have hAvoid : ∀ z ∈ Z, z ∉ e := by
        intro z hz hz'
        exact htRes.2.1 z hz (mem_triEdges_imp_mem heP z hz')
      exact (Finset.disjoint_left.1 htRes.2.2) heP (cert.external s hsS e heS hAvoid)
    · rw [Finset.disjoint_left]
      intro e heP heS
      have hsRes := mem_filter.1 (hP.1 hsP)
      have hAvoid : ∀ z ∈ Z, z ∉ e := by
        intro z hz hz'
        exact hsRes.2.1 z hz (mem_triEdges_imp_mem heP z hz')
      exact (Finset.disjoint_left.1 hsRes.2.2) heP (cert.external t htS e heS hAvoid)
    · exact hP.2 s hsP t htP hst

/-- Combined cover from a certificate and a residual cover. -/
lemma combine_cover {Z : Finset V} (cert : ReductionCertificate G Z)
    {Y : Finset (Sym2 V)} (hY : IsResidualCover G cert.cover Z Y) :
    IsTriangleCover G (cert.cover ∪ Y) := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases mem_union.1 he with h | h
    · exact cert.cover_edges h
    · exact (mem_sdiff.1 (hY.1 h)).1
  · intro t ht
    by_cases hZ : ∃ z ∈ Z, z ∈ t
    · exact mt (fun hdis => (disjoint_union_left.1 hdis).1) (cert.coversZ t ht hZ)
    · push_neg at hZ
      by_cases hX : Disjoint cert.cover (triEdges t)
      · have htRes : t ∈ residualTriangles G cert.cover Z :=
          mem_filter.2 ⟨ht, hZ, hX.symm⟩
        exact mt (fun hdis => (disjoint_union_left.1 hdis).2) (hY.2 t htRes)
      · exact mt (fun hdis => (disjoint_union_left.1 hdis).1) hX

/-- **Lemma 2.1 (Reduction bridge)**, ambient formulation.
Given a residual packing `P` and residual cover `Y` with `|Y| ≤ 2|P|`
(as supplied by `τ(G') ≤ 2ν(G')`), conclude `τ(G) ≤ 2ν(G)`. -/
theorem reduction_bridge (Z : Finset V) (cert : ReductionCertificate G Z)
    (P : Finset (Finset V)) (Y : Finset (Sym2 V))
    (hP : IsResidualPacking G cert.cover Z P)
    (hY : IsResidualCover G cert.cover Z Y)
    (hTuza : Y.card ≤ 2 * P.card) :
    coverNumber G ≤ 2 * packingNumber G := by
  have hpack := combine_packing G cert hP
  have hcover := combine_cover G cert hY
  have hdisj := residual_packing_disj G cert hP
  have hcard : (cert.cover ∪ Y).card ≤ 2 * (cert.packing ∪ P).card := by
    calc (cert.cover ∪ Y).card
        ≤ cert.cover.card + Y.card := card_union_le _ _
      _ ≤ 2 * cert.packing.card + 2 * P.card := by
          have := cert.size; omega
      _ = 2 * (cert.packing.card + P.card) := by ring
      _ = 2 * (cert.packing ∪ P).card := by rw [card_union_of_disjoint hdisj]
  have hν := packingNumber_le G hpack
  have hτ := coverNumber_le G hcover
  omega

end Tuza
