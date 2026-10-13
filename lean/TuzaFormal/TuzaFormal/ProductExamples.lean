import TuzaFormal.Product
import TuzaFormal.K4K5
import TuzaFormal.Family

/-!
# Instances of Proposition 8.1

* Lemma 8.2 (`ν(K₄)=1, τ(K₄)=2, ν(K₅)=2, τ(K₅)=4`) for Mathlib's complete graphs `⊤`.
* `K4K5.G = K₄ □ K₅`, so Prop 8.1 + Lemma 8.2 re-derive `ν = 13`, `τ = 26`
  (this is how `K4K5.main` gets its `ν`/`τ` values; `main` is stated at the end of this file).
* `Family.box J = K₄ □ J`, so Prop 8.1 gives `ν = |W|`, `τ = 2|W|` for triangle-free `J`; `Family.infinite_family` is stated at the end of this file.
-/

open Finset

namespace Tuza.Product

lemma packingNumber_congr {V : Type*} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G = G') : packingNumber G = packingNumber G' := by
  subst h; congr

lemma coverNumber_congr {V : Type*} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G = G') : coverNumber G = coverNumber G' := by
  subst h; congr

theorem clique_top (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).cliqueFinset 3 = univ.powersetCard 3 := by
  ext t
  simp [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff,
    Set.Pairwise]
theorem clique_top4 : (⊤ : SimpleGraph (Fin 4)).cliqueFinset 3 = univ.powersetCard 3 :=
  clique_top 4
theorem clique_top5 : (⊤ : SimpleGraph (Fin 5)).cliqueFinset 3 = univ.powersetCard 3 :=
  clique_top 5
theorem edges_top4 : (⊤ : SimpleGraph (Fin 4)).edgeFinset = triEdges univ := by decide +kernel
theorem edges_top5 : (⊤ : SimpleGraph (Fin 5)).edgeFinset = triEdges univ := by decide +kernel

/-- **Lemma 8.2.** -/
theorem nu_K4 : packingNumber (⊤ : SimpleGraph (Fin 4)) = 1 := by
  refine packingNumber_eq _ (fun P hP => k4pack P (clique_top4 ▸ hP.1)
    fun s hs t ht hst => disjoint_iff_inter_eq_empty.1 (hP.2 s hs t ht hst)) {{0, 1, 2}} ?_ rfl
  unfold IsTrianglePacking; rw [clique_top4]; decide +kernel

theorem nu_K5 : packingNumber (⊤ : SimpleGraph (Fin 5)) = 2 := by
  refine packingNumber_eq _ (fun P hP => k5pack P (clique_top5 ▸ hP.1)
    fun s hs t ht hst => disjoint_iff_inter_eq_empty.1 (hP.2 s hs t ht hst))
    {{0, 1, 2}, {0, 3, 4}} ?_ rfl
  unfold IsTrianglePacking; rw [clique_top5]; decide +kernel

theorem tau_K4 : coverNumber (⊤ : SimpleGraph (Fin 4)) = 2 := by
  refine coverNumber_eq _ (fun X hX => k4cover X (edges_top4 ▸ hX.1)
    fun t ht => not_disjoint_iff_nonempty_inter.1 (hX.2 t (clique_top4 ▸ ht)))
    {s(0, 1), s(2, 3)} ?_ rfl
  unfold IsTriangleCover; rw [clique_top4, edges_top4]; decide +kernel

theorem tau_K5 : coverNumber (⊤ : SimpleGraph (Fin 5)) = 4 := by
  refine coverNumber_eq _ (fun X hX => k5cover X (edges_top5 ▸ hX.1)
    fun t ht => not_disjoint_iff_nonempty_inter.1 (hX.2 t (clique_top5 ▸ ht)))
    {s(0, 1), s(2, 3), s(2, 4), s(3, 4)} ?_ rfl
  unfold IsTriangleCover; rw [clique_top5, edges_top5]; decide +kernel

theorem K4K5_eq : K4K5.G = (⊤ : SimpleGraph (Fin 4)) □ (⊤ : SimpleGraph (Fin 5)) := by
  ext a b
  simp only [K4K5.G, SimpleGraph.boxProd_adj, SimpleGraph.top_adj]
  tauto

/-- Theorem 1.4 (first assertion) via Prop 8.1 + Lemma 8.2, used by `K4K5.main`. -/
theorem K4K5_via_prod :
    packingNumber (⊤ □ ⊤ : SimpleGraph (Fin 4 × Fin 5)) = 5 * 1 + 4 * 2 ∧
    coverNumber (⊤ □ ⊤ : SimpleGraph (Fin 4 × Fin 5)) = 5 * 2 + 4 * 4 ∧
    packingNumber K4K5.G = packingNumber (⊤ □ ⊤ : SimpleGraph (Fin 4 × Fin 5)) ∧
    coverNumber K4K5.G = coverNumber (⊤ □ ⊤ : SimpleGraph (Fin 4 × Fin 5)) := by
  refine ⟨?_, ?_, packingNumber_congr K4K5_eq, coverNumber_congr K4K5_eq⟩
  · rw [nu_boxProd, nu_K4, nu_K5]; simp
  · rw [tau_boxProd, tau_K4, tau_K5]; simp

section Fam
set_option linter.unusedSectionVars false
variable {W : Type*} [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj]

theorem box_eq : Family.box J = (⊤ : SimpleGraph (Fin 4)) □ J := by
  ext a b
  simp only [Family.box, SimpleGraph.boxProd_adj, SimpleGraph.top_adj]
  tauto

theorem triangleFree_clique (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False) :
    J.cliqueFinset 3 = ∅ := by
  apply eq_empty_of_forall_notMem
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ :=
    SimpleGraph.is3Clique_iff.1 (SimpleGraph.mem_cliqueFinset_iff.1 ht)
  exact htf a b c hab hbc hac

/-- Prop 8.3's parameter formulas re-derived from Prop 8.1 . -/
theorem box_via_prod (htf : ∀ x y z, J.Adj x y → J.Adj y z → J.Adj x z → False) :
    packingNumber (Family.box J) = Fintype.card W ∧
    coverNumber (Family.box J) = 2 * Fintype.card W := by
  have h0 := triangleFree_clique J htf
  have hnu : packingNumber J = 0 :=
    packingNumber_eq J (fun P hP => by
      have := card_le_card hP.1; rw [h0] at this; simpa using this) ∅ ⟨by simp, by simp⟩ rfl
  have htau : coverNumber J = 0 :=
    coverNumber_eq J (fun _ _ => Nat.zero_le _) ∅ ⟨empty_subset _, by simp [h0]⟩ rfl
  rw [packingNumber_congr (box_eq J), coverNumber_congr (box_eq J), nu_boxProd, tau_boxProd,
    nu_K4, tau_K4, hnu, htau]
  simp [mul_comm]

/-- The explicit family `G_k`, `k = m + 4`, through Prop 8.1: used by `infinite_family`. -/
theorem infinite_family_via_prod (m : ℕ) :
    packingNumber (Family.box (Family.circ (2 * (m + 4)))) = 2 * (m + 4) ∧
    coverNumber (Family.box (Family.circ (2 * (m + 4)))) = 4 * (m + 4) := by
  obtain ⟨h1, h2⟩ := box_via_prod _ (Family.circ_triangleFree (n := 2 * (m + 4)) (dvd_mul_right 2 _))
  rw [ZMod.card] at h1 h2
  exact ⟨h1, by rw [h2]; ring⟩

end Fam

end Tuza.Product

/-! ## Main theorems (ν/τ derived from Prop 8.1) -/

namespace Tuza.K4K5

theorem packingNumber_eq_13 : packingNumber G = 13 := by
  obtain ⟨h1, -, h3, -⟩ := Tuza.Product.K4K5_via_prod; rw [h3, h1]

theorem coverNumber_eq_26 : coverNumber G = 26 := by
  obtain ⟨-, h2, -, h4⟩ := Tuza.Product.K4K5_via_prod; rw [h4, h2]

/-- **Theorem 1.4 (K₄ □ K₅).** -/
theorem main : G.Connected ∧ G.IsRegularOfDegree 7 ∧ Fintype.card V = 20 ∧
    G.edgeFinset.card = 70 ∧ (∀ e ∈ G.edgeFinset, ∃ t ∈ G.cliqueFinset 3, e ∈ triEdges t) ∧
    packingNumber G = 13 ∧ coverNumber G = 26 ∧ coverNumber G = 2 * packingNumber G := by
  refine ⟨connected, regular, card_V, card_edges, every_edge_in_triangle,
    packingNumber_eq_13, coverNumber_eq_26, ?_⟩
  rw [packingNumber_eq_13, coverNumber_eq_26]

end Tuza.K4K5

namespace Tuza.Family

open Finset in
/-- **Proposition 8.3** (explicit family). For `k = m + 4 ≥ 4`, `G_k = K₄ □ C_{2k}(1,3)` is a
connected 7-regular graph on `8k` vertices with `28k` edges, `ν = 2k` and `τ = 4k = 2ν`. -/
theorem infinite_family (m : ℕ) :
    let k := m + 4
    (box (circ (2 * k))).Connected ∧ (box (circ (2 * k))).IsRegularOfDegree 7 ∧
    Fintype.card (Fin 4 × ZMod (2 * k)) = 8 * k ∧
    (box (circ (2 * k))).edgeFinset.card = 28 * k ∧
    packingNumber (box (circ (2 * k))) = 2 * k ∧
    coverNumber (box (circ (2 * k))) = 4 * k ∧
    coverNumber (box (circ (2 * k))) = 2 * packingNumber (box (circ (2 * k))) := by
  intro k
  have hn : 8 ≤ 2 * k := by omega
  have hcard : Fintype.card (Fin 4 × ZMod (2 * k)) = 8 * k := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]; ring
  have hreg : (box (circ (2 * k))).IsRegularOfDegree 7 := box_regular _ 4 (circ_regular hn)
  obtain ⟨hnu, htau⟩ := Tuza.Product.infinite_family_via_prod m
  refine ⟨box_connected _ (circ_connected hn), hreg, hcard, ?_, hnu, htau, ?_⟩
  · have hs := (box (circ (2 * k))).sum_degrees_eq_twice_card_edges
    simp only [hreg.degree_eq, sum_const, card_univ, hcard, smul_eq_mul] at hs
    omega
  · rw [hnu, htau]; ring

end Tuza.Family
