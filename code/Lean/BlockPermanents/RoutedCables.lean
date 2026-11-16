import BlockPermanents.RoutedClasp
import BlockPermanents.RoutedAdjoint

/-! # Applying the sector calculation to the clasps of arbitrary cable sizes -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H]
/-- A physical layout puts every positive slot either on the output or on
one of the paired strands. Two layouts may use different cap routes. -/
abbrev Layout (lengths : H → ℕ) (N r : ℕ) :=
  (Σ i, Fin (lengths i)) ≃ Cable (Fin N) r

/-- A common reference layout merely numbers the common positive boundary. -/
def wiring {N r : ℕ} (lengths : H → ℕ) (base L : Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r)
    (g : ((i : H) → Perm (Fin (lengths i))) × Perm (Fin r)) : Perm (Cable (Fin N) r) :=
  base.symm.trans ((Equiv.sigmaCongrRight g.1).trans (L.trans
    (markSplit.trans (((Equiv.refl (Fin N)).sumCongr g.2).trans markSplit.symm))))

/-- Weight of each product of the normalized cable clasps, including the
marked dual clasp. -/
def claspWeight {r : ℕ} (lengths : H → ℕ)
    (_ : ((i : H) → Perm (Fin (lengths i))) × Perm (Fin r)) : ℚ :=
  (Fintype.card (((i : H) → Perm (Fin (lengths i))) × Perm (Fin r)) : ℚ)⁻¹

theorem weight_factor {r : ℕ} (lengths : H → ℕ)
    (g : ((i : H) → Perm (Fin (lengths i))) × Perm (Fin r)) :
    claspWeight lengths g = ((((∏ i, (lengths i).factorial : ℕ) * r.factorial : ℕ) : ℚ))⁻¹ := by
  simp [claspWeight,Fintype.card_prod,Fintype.card_pi,Fintype.card_perm]

/-- The finite choices in the intersection-form theorem are the actual
permutations at the positive and marked clasps. -/
theorem clasped_intersection {N r d : ℕ} (lengths : H → ℕ) (base L K : Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) :
    let P := wiring lengths base L markSplit
    let Q := wiring lengths base K markSplit
    let wt := @claspWeight H _ _ r lengths
    ∃ j k : _ → _ → ℕ, (∀ i t,k i t ≤ N ∧ j i t+k i t ≤ r ∧ 0≤wt i*wt t) ∧
      ∀ (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
      Closures.clasp (capAverage S r P wt (reflectedAverage S r Q wt f)) w =
        (∑ i, ∑ t, ((wt i*wt t : ℚ):ℂ) * (S.card : ℂ)^(j i t) *
          (((occupied S w).card.choose (k i t) : ℕ) : ℂ)/(N.choose (k i t) : ℂ)) * f w := by
  apply intersection_form
  all_goals intro g; unfold claspWeight; positivity

end
end BlockPermanents.RoutedTrace
