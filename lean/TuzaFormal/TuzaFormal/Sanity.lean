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
