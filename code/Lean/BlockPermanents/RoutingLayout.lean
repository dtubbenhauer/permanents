import BlockPermanents.RoutedCables

/-! # Routing a prescribed number of slots out of each symmetric cable -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

def splitSlots (I : Type) : (r : ℕ) → Cable I r ≃ I ⊕ Fin r
  | 0 => (Equiv.sumEmpty I (Fin 0)).symm
  | r+1 =>
    (Equiv.optionEquivSumPUnit.{0,0} (Cable I r)).trans
      (((splitSlots I r).sumCongr (Equiv.refl _)).trans
        ((Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr
          (((Equiv.refl (Fin r)).sumCongr (Equiv.equivPUnit (Fin 1)).symm).trans finSumFinEquiv))))

variable {H : Type} [Fintype H] [DecidableEq H]

/-- An α-route explicitly splits each of its dᵢ slots into dᵢ−αᵢ
survivors followed by αᵢ marked strands, then collects the two bundles. -/
def bySizes (d a : H → ℕ) (ha : ∀ i,a i≤d i) : Layout d (∑ i,(d i-a i)) (∑ i,a i) :=
  let split := Equiv.sigmaCongrRight (fun i => (finCongr (show d i=(d i-a i)+a i by
    have := ha i;omega)).trans finSumFinEquiv.symm)
  let keep := Fintype.equivFinOfCardEq (α := Σ i,Fin (d i-a i)) (show _=∑ i,(d i-a i) by simp)
  let cut := Fintype.equivFinOfCardEq (α := Σ i,Fin (a i)) (show _=∑ i,a i by simp)
  split.trans ((Equiv.sigmaSumDistrib _ _).trans
    ((keep.sumCongr cut).trans (splitSlots (Fin (∑ i,(d i-a i))) (∑ i,a i)).symm))

end
end BlockPermanents.RoutedTrace
