import TuzaFormal.Reducibility
import Mathlib.Combinatorics.Hall.Finite

/-!
# Puleo's Cor 4.12, 7-vertex case (human proof)

Let every edge of `L` lie in `N = I ∪ {a,b,c}` with `|I| = 4`, `I` independent, and no vertex
of `N` isolated. Then `L` is WKE. Write `S r = I ∩ N(r)` for `r ∈ R = {a,b,c}`.
* Hall holds for `(S a, S b, S c)`: three disjoint `R–I` edges, `Q = R`.
* Some `S z = ∅` (`caseEmpty`), or two of them equal a singleton `{i₀}` (`caseSame`):
  small explicit witnesses with `|Q| ≤ 2`.
-/

open Finset SimpleGraph

namespace Tuza.Puleo

set_option linter.unusedSectionVars false

variable {W : Type*} [Fintype W] [DecidableEq W] (L : SimpleGraph W) [DecidableRel L.Adj]

omit [Fintype W] in
lemma toFinset_pair (x y : W) : (s(x, y) : Sym2 W).toFinset = {x, y} := Sym2.toFinset_mk_eq

lemma wke_mk (M : Finset (Sym2 W)) (Q : Finset W) (hM : ∀ e ∈ M, e ∈ L.edgeSet)
    (hd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset) (hc : Q.card ≤ M.card)
    (hcov : ∀ u v, L.Adj u v → u ∉ Q → v ∉ Q → s(u, v) ∈ M) : IsWKE L := by
  refine ⟨M, Q, ⟨fun e he => mem_edgeFinset.2 (hM e he), hd⟩, hc, ?_⟩
  intro e he hQ
  induction e using Sym2.ind with
  | _ u v =>
    exact hcov u v (mem_edgeFinset.1 he) (hQ u (Sym2.mem_mk_left u v))
      (hQ v (Sym2.mem_mk_right u v))

lemma wke1 (x y q : W) (h : L.Adj x y)
    (hcov : ∀ u v, L.Adj u v → u ≠ q → v ≠ q → s(u, v) = s(x, y)) : IsWKE L := by
  refine wke_mk L {s(x, y)} {q} (by simpa using h) (by simp) (by simp) ?_
  intro u v huv hu hv
  simpa using hcov u v huv (by simpa using hu) (by simpa using hv)

lemma wke2 (x1 y1 x2 y2 : W) (Q : Finset W) (hQ : Q.card ≤ 2) (h1 : L.Adj x1 y1)
    (h2 : L.Adj x2 y2) (d1 : x1 ≠ x2) (d2 : x1 ≠ y2) (d3 : y1 ≠ x2) (d4 : y1 ≠ y2)
    (hcov : ∀ u v, L.Adj u v → u ∉ Q → v ∉ Q → s(u, v) = s(x1, y1) ∨ s(u, v) = s(x2, y2)) :
    IsWKE L := by
  have hne : s(x1, y1) ≠ s(x2, y2) := by
    intro h; rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact d1 h
    · exact d2 h
  refine wke_mk L {s(x1, y1), s(x2, y2)} Q ?_ ?_ ?_ ?_
  · intro e he; simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact h1
    · exact h2
  · intro e he f hf hef
    simp only [mem_insert, mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      first | exact absurd rfl hef | (simp only [toFinset_pair]; simp [*, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4])
  · rw [card_pair hne]; exact hQ
  · intro u v huv hu hv
    rcases hcov u v huv hu hv with h | h <;> simp [h]

lemma wke3 (x1 y1 x2 y2 x3 y3 : W) (Q : Finset W) (hQ : Q.card ≤ 3) (h1 : L.Adj x1 y1)
    (h2 : L.Adj x2 y2) (h3 : L.Adj x3 y3)
    (a2 : x1 ≠ x2) (a3 : x1 ≠ y2) (a6 : y1 ≠ x2) (a7 : y1 ≠ y2)
    (a4 : x1 ≠ x3) (a5 : x1 ≠ y3) (a8 : y1 ≠ x3) (a9 : y1 ≠ y3)
    (a11 : x2 ≠ x3) (a12 : x2 ≠ y3) (a13 : y2 ≠ x3) (a14 : y2 ≠ y3)
    (hcov : ∀ u v, L.Adj u v → u ∉ Q → v ∉ Q → False) : IsWKE L := by
  have e12 : s(x1, y1) ≠ s(x2, y2) := by simp [a2, a3]
  have e13 : s(x1, y1) ≠ s(x3, y3) := by simp [a4, a5]
  have e23 : s(x2, y2) ≠ s(x3, y3) := by simp [a11, a12]
  have dj : ∀ (p q r t : W), p ≠ r → p ≠ t → q ≠ r → q ≠ t →
      Disjoint (s(p, q) : Sym2 W).toFinset (s(r, t) : Sym2 W).toFinset := by
    intro p q r t h1 h2 h3 h4
    simp only [toFinset_pair]; simp
    exact ⟨⟨Ne.symm h1, Ne.symm h3⟩, Ne.symm h2, Ne.symm h4⟩
  refine wke_mk L {s(x1, y1), s(x2, y2), s(x3, y3)} Q ?_ ?_ ?_ ?_
  · intro e he; simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  · intro e he f hf hef
    simp only [mem_insert, mem_singleton] at he hf
    rcases he with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl
    · exact absurd rfl hef
    · exact dj _ _ _ _ a2 a3 a6 a7
    · exact dj _ _ _ _ a4 a5 a8 a9
    · exact dj _ _ _ _ a2.symm a6.symm a3.symm a7.symm
    · exact absurd rfl hef
    · exact dj _ _ _ _ a11 a12 a13 a14
    · exact dj _ _ _ _ a4.symm a8.symm a5.symm a9.symm
    · exact dj _ _ _ _ a11.symm a13.symm a12.symm a14.symm
    · exact absurd rfl hef
  · rw [card_insert_of_notMem (by simp [e12, e13]), card_pair e23]; exact hQ
  · intro u v huv hu hv; exact (hcov u v huv hu hv).elim

/-- Hypotheses of the 7-vertex Puleo lemma; `R = {a,b,c}`. -/
structure Ctx (I : Finset W) (a b c : W) : Prop where
  ha : a ∉ I
  hb : b ∉ I
  hc : c ∉ I
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  card : I.card = 4
  supp : ∀ u v, L.Adj u v → u ∈ I ∨ u = a ∨ u = b ∨ u = c
  ind : ∀ x ∈ I, ∀ y ∈ I, ¬ L.Adj x y
  nbI : ∀ i ∈ I, ∃ v, L.Adj i v

variable {L}

lemma Ctx.swap12 {I : Finset W} {a b c : W} (h : Ctx L I a b c) : Ctx L I b a c :=
  ⟨h.hb, h.ha, h.hc, h.hab.symm, h.hbc, h.hac, h.card,
    fun u v huv => by rcases h.supp u v huv with h' | h' | h' | h' <;> simp [h'],
    h.ind, h.nbI⟩

lemma Ctx.rot {I : Finset W} {a b c : W} (h : Ctx L I a b c) : Ctx L I b c a :=
  ⟨h.hb, h.hc, h.ha, h.hbc, h.hab.symm, h.hac.symm, h.card,
    fun u v huv => by rcases h.supp u v huv with h' | h' | h' | h' <;> simp [h'],
    h.ind, h.nbI⟩

lemma Ctx.nbr {I : Finset W} {a b c : W} (h : Ctx L I a b c) {i v : W} (hi : i ∈ I)
    (hv : L.Adj i v) : v = a ∨ v = b ∨ v = c := by
  rcases h.supp v i hv.symm with h' | h' | h' | h'
  · exact (h.ind i hi v h' hv).elim
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

lemma Ctx.other {I : Finset W} {a b c : W} (h : Ctx L I a b c) (i : W) : ∃ k ∈ I, k ≠ i := by
  have : 1 < I.card := by rw [h.card]; norm_num
  obtain ⟨k, hk, hki⟩ := exists_mem_ne this i
  exact ⟨k, hk, hki⟩

lemma Ctx.some {I : Finset W} {a b c : W} (h : Ctx L I a b c) : ∃ k, k ∈ I := by
  have : 0 < I.card := by rw [h.card]; norm_num
  exact card_pos.1 this

/-- `x` is the only `R`-vertex with `I`-neighbours (`y`, `z` have none). -/
lemma caseOnly {I : Finset W} {x y z : W} (h : Ctx L I x y z)
    (hz : ∀ i ∈ I, ¬ L.Adj z i) (hy : ∀ i ∈ I, ¬ L.Adj y i) : IsWKE L := by
  obtain ⟨i, hi⟩ := h.some
  have hxi : L.Adj x i := by
    obtain ⟨v, hv⟩ := h.nbI i hi
    rcases h.nbr hi hv with rfl | rfl | rfl
    · exact hv.symm
    · exact (hy i hi hv.symm).elim
    · exact (hz i hi hv.symm).elim
  have key : ∀ u v, L.Adj u v → u ≠ x → v ≠ x → (u = y ∧ v = z) ∨ (u = z ∧ v = y) := by
    intro u v huv hu hv
    rcases h.supp u v huv with hu' | rfl | rfl | rfl
    · rcases h.nbr hu' huv with rfl | rfl | rfl
      · exact (hv rfl).elim
      · exact (hy u hu' huv.symm).elim
      · exact (hz u hu' huv.symm).elim
    · exact (hu rfl).elim
    · rcases h.supp v u huv.symm with hv' | rfl | rfl | rfl
      · exact (hy v hv' huv).elim
      · exact (hv rfl).elim
      · exact (huv.ne rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases h.supp v u huv.symm with hv' | rfl | rfl | rfl
      · exact (hz v hv' huv).elim
      · exact (hv rfl).elim
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (huv.ne rfl).elim
  by_cases hyz : L.Adj y z
  · refine wke2 L x i y z {x} (by simp) hxi hyz h.hab h.hac
      (fun e => h.hb (e ▸ hi)) (fun e => h.hc (e ▸ hi)) ?_
    intro u v huv hu hv
    rcases key u v huv (by simpa using hu) (by simpa using hv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inr Sym2.eq_swap
  · refine wke1 L x i x hxi ?_
    intro u v huv hu hv
    rcases key u v huv hu hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hyz huv).elim
    · exact (hyz huv.symm).elim

/-- `z` has no `I`-neighbour. -/
lemma caseEmpty {I : Finset W} {x y z : W} (h : Ctx L I x y z)
    (hz : ∀ i ∈ I, ¬ L.Adj z i) : IsWKE L := by
  by_cases hp : ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ L.Adj x i ∧ L.Adj y j
  · obtain ⟨i, hi, j, hj, hij, hxi, hyj⟩ := hp
    refine wke2 L x i y j {x, y} card_le_two hxi hyj h.hab
      (fun e => h.ha (e ▸ hj)) (fun e => h.hb (e ▸ hi)) hij ?_
    intro u v huv hu hv
    exfalso
    simp only [mem_insert, mem_singleton, not_or] at hu hv
    rcases h.supp u v huv with hu' | rfl | rfl | rfl
    · rcases h.nbr hu' huv with rfl | rfl | rfl
      · exact hv.1 rfl
      · exact hv.2 rfl
      · exact hz u hu' huv.symm
    · exact hu.1 rfl
    · exact hu.2 rfl
    · rcases h.supp v u huv.symm with hv' | rfl | rfl | rfl
      · exact hz v hv' huv
      · exact hv.1 rfl
      · exact hv.2 rfl
      · exact huv.ne rfl
  · push Not at hp
    by_cases hy : ∀ j ∈ I, ¬ L.Adj y j
    · exact caseOnly h hz hy
    by_cases hx : ∀ j ∈ I, ¬ L.Adj x j
    · exact caseOnly h.swap12 hz hx
    push Not at hx hy
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    have hij : i = j := by by_contra hne; exact hp i hi j hj hne hxi hyj
    subst hij
    obtain ⟨k, hk, hki⟩ := h.other i
    obtain ⟨v, hv⟩ := h.nbI k hk
    exfalso
    rcases h.nbr hk hv with rfl | rfl | rfl
    · exact hp k hk i hi hki hv.symm hyj
    · exact hp i hi k hk (Ne.symm hki) hxi hv.symm
    · exact hz k hk hv.symm

/-- `x`, `y` both have the single `I`-neighbour `i₀`. -/
lemma caseSame {I : Finset W} {x y z : W} (h : Ctx L I x y z) {i0 : W} (hi0 : i0 ∈ I)
    (hx0 : L.Adj x i0) (hxs : ∀ i ∈ I, L.Adj x i → i = i0)
    (hys : ∀ i ∈ I, L.Adj y i → i = i0) : IsWKE L := by
  obtain ⟨k, hk, hki⟩ := h.other i0
  have hkz : L.Adj z k := by
    obtain ⟨v, hv⟩ := h.nbI k hk
    rcases h.nbr hk hv with rfl | rfl | rfl
    · exact (hki (hxs k hk hv.symm)).elim
    · exact (hki (hys k hk hv.symm)).elim
    · exact hv.symm
  have key : ∀ u v, L.Adj u v → u ∉ ({z, i0} : Finset W) → v ∉ ({z, i0} : Finset W) →
      (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
    intro u v huv hu hv
    simp only [mem_insert, mem_singleton, not_or] at hu hv
    have hI : ∀ w ∈ I, w ≠ i0 → ∀ t, L.Adj w t → t ≠ z → False := by
      intro w hw hw0 t ht htz
      rcases h.nbr hw ht with rfl | rfl | rfl
      · exact hw0 (hxs w hw ht.symm)
      · exact hw0 (hys w hw ht.symm)
      · exact htz rfl
    rcases h.supp u v huv with hu' | rfl | rfl | rfl
    · exact (hI u hu' hu.2 v huv hv.1).elim
    · rcases h.supp v u huv.symm with hv' | rfl | rfl | rfl
      · exact (hI v hv' hv.2 u huv.symm hu.1).elim
      · exact (huv.ne rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact (hv.1 rfl).elim
    · rcases h.supp v u huv.symm with hv' | rfl | rfl | rfl
      · exact (hI v hv' hv.2 u huv.symm hu.1).elim
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (huv.ne rfl).elim
      · exact (hv.1 rfl).elim
    · exact (hu.1 rfl).elim
  by_cases hxy : L.Adj x y
  · refine wke2 L x y z k {z, i0} card_le_two hxy hkz h.hac (fun e => h.ha (e ▸ hk))
      h.hbc (fun e => h.hb (e ▸ hk)) ?_
    intro u v huv hu hv
    rcases key u v huv hu hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl Sym2.eq_swap
  · refine wke2 L x i0 z k {z, i0} card_le_two hx0 hkz h.hac (fun e => h.ha (e ▸ hk))
      (fun e => h.hc (e ▸ hi0)) (Ne.symm hki) ?_
    intro u v huv hu hv
    rcases key u v huv hu hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hxy huv).elim
    · exact (hxy huv.symm).elim

lemma fin3_subsets : ∀ s : Finset (Fin 3), s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨
    s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} ∨ s = {0, 1, 2} := by decide

/-- Puleo's Cor 4.12 for `|N| = 7`, `|I| = 4` (proved, no axiom). -/
theorem wke_of_ctx {I : Finset W} {a b c : W} (h : Ctx L I a b c) : IsWKE L := by
  classical
  by_cases ea : ∀ i ∈ I, ¬ L.Adj a i
  · exact caseEmpty h.rot ea
  by_cases eb : ∀ i ∈ I, ¬ L.Adj b i
  · exact caseEmpty h.rot.rot eb
  by_cases ec : ∀ i ∈ I, ¬ L.Adj c i
  · exact caseEmpty h ec
  push Not at ea eb ec
  -- a pair whose `I`-neighbourhoods lie in one singleton
  have same : ∀ {x y z : W}, Ctx L I x y z → (∃ i ∈ I, L.Adj x i) →
      (∃ i0, (∀ i ∈ I, L.Adj x i → i = i0) ∧ (∀ i ∈ I, L.Adj y i → i = i0)) → IsWKE L := by
    intro x y z hc ⟨i, hi, hxi⟩ ⟨i0, h1, h2⟩
    have := h1 i hi hxi; subst this
    exact caseSame hc hi hxi h1 h2
  by_cases pab : ∃ i0, (∀ i ∈ I, L.Adj a i → i = i0) ∧ (∀ i ∈ I, L.Adj b i → i = i0)
  · exact same h ea pab
  by_cases pac : ∃ i0, (∀ i ∈ I, L.Adj a i → i = i0) ∧ (∀ i ∈ I, L.Adj c i → i = i0)
  · exact same h.rot.rot.swap12 ea pac
  by_cases pbc : ∃ i0, (∀ i ∈ I, L.Adj b i → i = i0) ∧ (∀ i ∈ I, L.Adj c i → i = i0)
  · exact same h.rot eb pbc
  -- Hall
  set t : Fin 3 → Finset W := ![I.filter (L.Adj a), I.filter (L.Adj b), I.filter (L.Adj c)]
    with ht
  have ne1 : ∀ r : W, (∃ i ∈ I, L.Adj r i) → 1 ≤ (I.filter (L.Adj r)).card := by
    rintro r ⟨i, hi, hri⟩
    exact card_pos.2 ⟨i, mem_filter.2 ⟨hi, hri⟩⟩
  have ne2 : ∀ r r' : W,
      ¬ (∃ i0, (∀ i ∈ I, L.Adj r i → i = i0) ∧ (∀ i ∈ I, L.Adj r' i → i = i0)) →
      2 ≤ (I.filter (L.Adj r) ∪ I.filter (L.Adj r')).card := by
    intro r r' hn
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_succ_iff.1 hlt |>.lt_or_eq with h0 | h1
    · have : I.filter (L.Adj r) ∪ I.filter (L.Adj r') = ∅ := card_eq_zero.1 (by omega)
      obtain ⟨i, -⟩ := h.some
      refine hn ⟨i, fun j hj hrj => ?_, fun j hj hrj => ?_⟩
      · have : j ∈ (∅ : Finset W) := this ▸ mem_union_left _ (mem_filter.2 ⟨hj, hrj⟩)
        simp at this
      · have : j ∈ (∅ : Finset W) := this ▸ mem_union_right _ (mem_filter.2 ⟨hj, hrj⟩)
        simp at this
    · obtain ⟨i0, hi0⟩ := card_eq_one.1 h1
      refine hn ⟨i0, fun j hj hrj => ?_, fun j hj hrj => ?_⟩
      · have := hi0 ▸ mem_union_left _ (mem_filter.2 ⟨hj, hrj⟩); simpa using this
      · have := hi0 ▸ mem_union_right _ (mem_filter.2 ⟨hj, hrj⟩); simpa using this
  have hall : ∀ s : Finset (Fin 3), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases fin3_subsets s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simpa [ht] using ne1 a ea
    · simpa [ht] using ne1 b eb
    · simpa [ht] using ne1 c ec
    · simpa [ht, biUnion_insert] using ne2 a b pab
    · simpa [ht, biUnion_insert] using ne2 a c pac
    · simpa [ht, biUnion_insert] using ne2 b c pbc
    · have hsub : I ⊆ ({0, 1, 2} : Finset (Fin 3)).biUnion t := by
        intro i hi
        obtain ⟨v, hv⟩ := h.nbI i hi
        simp only [biUnion_insert, singleton_biUnion, mem_union, ht]
        rcases h.nbr hi hv with rfl | rfl | rfl
        · exact Or.inl (by simpa using ⟨hi, hv.symm⟩)
        · exact Or.inr (Or.inl (by simpa using ⟨hi, hv.symm⟩))
        · exact Or.inr (Or.inr (by simpa using ⟨hi, hv.symm⟩))
      have := card_le_card hsub
      rw [h.card] at this
      have h3 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
      omega
  obtain ⟨f, hfi, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have h0 := hf 0; have h1 := hf 1; have h2 := hf 2
  simp only [ht, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mem_filter] at h0 h1 h2
  have i01 : f 0 ≠ f 1 := fun e => by have := hfi e; exact absurd this (by decide)
  have i02 : f 0 ≠ f 2 := fun e => by have := hfi e; exact absurd this (by decide)
  have i12 : f 1 ≠ f 2 := fun e => by have := hfi e; exact absurd this (by decide)
  have nI : ∀ {r w : W}, r ∉ I → w ∈ I → r ≠ w := fun hr hw e => hr (e ▸ hw)
  refine wke3 L a (f 0) b (f 1) c (f 2) {a, b, c} card_le_three h0.2 h1.2 h2.2
    h.hab (nI h.ha h1.1) (Ne.symm (nI h.hb h0.1)) i01
    h.hac (nI h.ha h2.1) (Ne.symm (nI h.hc h0.1)) i02
    h.hbc (nI h.hb h2.1) (Ne.symm (nI h.hc h1.1)) i12 ?_
  intro u v huv hu hv
  simp only [mem_insert, mem_singleton, not_or] at hu hv
  have hu' : u ∈ I := by
    rcases h.supp u v huv with h' | h' | h' | h'
    · exact h'
    · exact (hu.1 h').elim
    · exact (hu.2.1 h').elim
    · exact (hu.2.2 h').elim
  have hv' : v ∈ I := by
    rcases h.supp v u huv.symm with h' | h' | h' | h'
    · exact h'
    · exact (hv.1 h').elim
    · exact (hv.2.1 h').elim
    · exact (hv.2.2 h').elim
  exact h.ind u hu' v hv' huv

end Tuza.Puleo
