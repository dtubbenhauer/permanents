import BlockPermanents.FourSecondProper
import BlockPermanents.FourThirdProper
import BlockPermanents.FourCommonCuts

/-! # The three families of cuts, Lemma 5C.2, equation (5C.3) -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourThickOpenings Support
open scoped Matrix BigOperators
noncomputable section

/-- On the four packet clasps, bend packet four in the original transfer.
The single index i represents r = i+1, from 1 through k−1. All three
proper-cut halves and the four terminal contributions are explicit. -/
theorem four_packet_bend {d k : ℕ} (hk : 0 < k)
    (h₁ : SchurNormalization.HomogeneousSchur d k k)
    (h₂ : SchurNormalization.HomogeneousSchur d (2*k) k)
    (h₃ : SchurNormalization.HomogeneousSchur d (3*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    let u := terminalU M N
    let w := terminalW M N
    let v := terminalV M N
    let pu := totalClasp d k k * u
    let z := v - (b k)⁻¹ • pu
    read M N (Q d k) =
      (∑ i : Fin (k-1), (k.choose (i.val+1) : ℚ) •
        ((6 * (k.choose (i.val+1) : ℚ)) •
          reflected (firstProperHalf (d:=d) (properCut (p:=1*k) (by omega) i)) +
         (3 * a k * ((2*k).choose (i.val+1) : ℚ)) •
          reflected (secondProperHalf (d:=d) (properCut (p:=2*k) (by omega) i)) +
         (scale 3 k * ((3*k).choose (i.val+1) : ℚ)) •
          reflected (thirdProperHalf (d:=d) (properCut (p:=3*k) (by omega) i)))) +
      ((scale 3 k*b k) • (zᴴ*z) + (3*(a k)^2) • (wᴴ*w) -
        (12:ℚ) • (uᴴ*u) - (4*a k) • (puᴴ*pu)) := by
  dsimp only
  rw [transfer_second_proper hk h₁ h₂ h₃, third_proper_family]
  unfold terminalSquares
  apply congrArg (· + _)
  rw [sum_proper_eq (p:=1*k) (by omega), sum_proper_eq (p:=2*k) (by omega),
    sum_proper_eq (p:=3*k) (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_add, smul_smul, pow_two, properCut]
  congr 2 <;> ring

/-- At k=2 each proper-cut family has one term. -/
theorem four_packet_bend_quadratic {d : ℕ}
    (h₁ : SchurNormalization.HomogeneousSchur d 2 2)
    (h₂ : SchurNormalization.HomogeneousSchur d 4 2)
    (h₃ : SchurNormalization.HomogeneousSchur d 6 2) :
    let M := ZeroCap.inner d 2 3
    let N := symClasp d 2
    read M N (Q d 2) =
      (24 : ℚ) • reflected (firstProperHalf (d:=d) (k:=2) 1) +
      (144 : ℚ) • reflected (secondProperHalf (d:=d) (k:=2) 1) +
      (1080 : ℚ) • reflected (thirdProperHalf (d:=d) (k:=2) 1) +
      terminalSquares M N := by
  dsimp only
  rw [full_cap_row (by decide : 0 < 2) h₁ h₂ h₃, quadratic_first_family,
    quadratic_second_family, quadratic_third_family]

end
end BlockPermanents.FourNative
