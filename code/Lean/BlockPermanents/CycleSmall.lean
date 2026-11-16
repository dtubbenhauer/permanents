import BlockPermanents.CycleCuts
import Mathlib.Tactic.IntervalCases

/-! Actual cycle representatives used in the six- and ten-label examples.
The finite checks compare directed edge multisets and matching endpoints;
the inequalities for arbitrary complex Gram entries are the generic cut theorems. -/
namespace BlockPermanents.CycleSmall
open CycleMatching CycleComposition CyclePolynomial CycleCuts
noncomputable section

private abbrev od (r : ℕ) := 2*r+3
private abbrev om (r s : ℕ) := od r+s
private instance (r s : ℕ) : NeZero (om r s) := ⟨by dsimp [om,od]; omega⟩
private abbrev mids (r s : ℕ) : Finset (Fin (om r s)) := Finset.univ.filter (fun i => 2*r+2 ≤ i.val)
private abbrev jlab (r s : ℕ) : Fin (om r s) := Fin.ofNat' _ (2*r+1)
private abbrev vlab (r s : ℕ) : Fin (om r s) := Fin.ofNat' _ (2*r+2)
private abbrev raw {m r : ℕ} (f : Fin r × Fin 2 → Fin m) : Multiset (Wire m) :=
  Finset.univ.val.map (fun t => (f (t,0),f (t,1)))

private def oddCheck (r s : ℕ) : Prop :=
  let m := om r s
  let U := mids r s
  let j := jlab r s
  let v := vlab r s
  let a := @upperWire m inferInstance (r+1)
  let b := @lowerWire m inferInstance r
  Function.Injective a ∧ Function.Injective b ∧ 0 ≠ j ∧
  (∀ p, b p ≠ 0 ∧ b p ≠ j) ∧
  (∀ w ∈ U, 0 ≠ w ∧ j ≠ w ∧ (∀ p, a p ≠ w) ∧ ∀ p, b p ≠ w) ∧
  v ∈ U ∧ U.card = s+1 ∧
  wiring (localPerm (od r) s) = (raw a).map Prod.swap + (raw b + {(0,v),(v,j)})

private instance (r s) : Decidable (oddCheck r s) := by unfold oddCheck; infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem oddChecks : ∀ (r : Fin 4) (s : Fin 8), om r s ≤ 10 → oddCheck r s := by
  decide +kernel

theorem odd_small (r s : ℕ) (hn : 2*r+3+s ≤ 10) (u : ℚ) (hu : 0 < u) :
    Admits (localPerm (2*r+3) s) (oddPolynomial (r+1) s u) := by
  obtain ⟨ha,hb,hij,hib,hU,hv,hs,hw⟩ :=
    oddChecks (⟨r,by omega⟩ : Fin 4) (⟨s,by omega⟩ : Fin 8) hn
  let a : Fin (r+1) × Fin 2 ↪ Fin (om r s) := ⟨_,ha⟩
  let b : Fin r × Fin 2 ↪ Fin (om r s) := ⟨_,hb⟩
  apply admits_odd _ a b 0 (jlab r s) (vlab r s) (mids r s) hij ?_ ?_ ?_ hv hw s hs u hu
  · rintro ⟨p,h⟩; exact (hib p).1 h
  · rintro ⟨p,h⟩; exact (hib p).2 h
  · intro w hw'
    obtain ⟨hi,hj,hx,hy⟩ := hU w hw'
    exact ⟨hi,hj,fun ⟨p,h⟩ => hx p h, fun ⟨p,h⟩ => hy p h⟩

private abbrev em (r : ℕ) := 2*r+2
private instance (r : ℕ) : NeZero (em r + 0) := ⟨by dsimp [em]; omega⟩

private def evenCheck (r : ℕ) : Prop :=
  let m := em r + 0
  let a := @upperWire m inferInstance (r+1)
  let b := @lowerWire m inferInstance (r+1)
  Function.Injective a ∧ Function.Injective b ∧
    wiring (localPerm (em r) 0) = (raw a).map Prod.swap + raw b

private instance (r) : Decidable (evenCheck r) := by unfold evenCheck; infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem evenChecks : ∀ r : Fin 5, evenCheck r := by decide +kernel

theorem even_small (r : ℕ) (hn : 2*r+2 ≤ 10) :
    Admits (localPerm (2*r+2) 0) [(r+1,1)] := by
  obtain ⟨ha,hb,hw⟩ := evenChecks (⟨r,by omega⟩ : Fin 5)
  exact admits_even _ ⟨_,ha⟩ ⟨_,hb⟩ hw

end
end BlockPermanents.CycleSmall
