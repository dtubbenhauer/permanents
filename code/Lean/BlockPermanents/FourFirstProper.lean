import BlockPermanents.FourProperOrder
import BlockPermanents.FourFullCapRow

/-! # The first family of proper cuts in the four-packet bend, equation (5C.3) -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourThickCompression FourThickOpenings
open FourExchangeKernel FourWireAlgebra Support
open scoped Matrix BigOperators
noncomputable section

/-- The half-map Uᵣ: average the three ordinary packets, cap r strands of
the rightmost ordinary packet against the fourth, and carry the first two through. -/
def firstProperHalf {d k : ℕ} (r : CutIndex (1*k) k) :=
  drawnHalf (ZeroCap.inner d k 3) (symClasp d k) r

/-- Each cut in the first family, with its coefficient in the actual transfer. -/
theorem first_proper_term {d k : ℕ} (r : CutIndex (1*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    let P := localClasp d k 1
    let e := act d k (FourThickSlots.exchange k 1 (by decide) r)
    let F := ordinary (packets d k)
    (6 : ℚ) • read M N (sand F ((weight (1*k) k r : ℚ) • (P * e * P))) =
      (6 * (k.choose r : ℚ)^2) • reflected (firstProperHalf (d:=d) r) := by
  dsimp only
  rw [map_smul, map_smul, smul_smul,
    proper_boundary _ _ (clasps_fixed d k) 1 (by decide) _, read_block_cut]
  simp only [weight, one_mul, Nat.cast_mul, pow_two, firstProperHalf, drawn_half_eq]

/-- Sum only the proper indices 0 < r < k. The endpoint cuts are separate. -/
theorem first_proper_family (d k : ℕ) :
    (6 : ℚ) • read (ZeroCap.inner d k 3) (symClasp d k) (U d k) =
      ∑ r ∈ properIndices (1*k) k,
        (6 * (k.choose r : ℚ)^2) • reflected (firstProperHalf (d:=d) r) := by
  unfold U proper
  rw [map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun r _ => first_proper_term r)

/-- For quadratic packets there is just one proper cut. Its weight is 24. -/
theorem quadratic_first_family (d : ℕ) :
    (6 : ℚ) • read (ZeroCap.inner d 2 3) (symClasp d 2) (U d 2) =
      (24 : ℚ) • reflected (firstProperHalf (d:=d) (k:=2) 1) := by
  rw [first_proper_family, show properIndices (1*2) 2 = {1} by decide +kernel,
    Finset.sum_singleton]
  congr 1
  decide +kernel

/-- The first proper family and the full-cap row in the original bent Q.
The remaining two proper families retain their native local openings. -/
theorem transfer_first_proper {d k : ℕ} (hk : 0 < k)
    (h₁ : SchurNormalization.HomogeneousSchur d k k)
    (h₂ : SchurNormalization.HomogeneousSchur d (2*k) k)
    (h₃ : SchurNormalization.HomogeneousSchur d (3*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    read M N (Q d k) =
      (∑ r ∈ properIndices (1*k) k,
        (6 * (k.choose r : ℚ)^2) • reflected (firstProperHalf (d:=d) r)) +
      (3 * a k) • read M N (W₂ d k) + scale 3 k • read M N (V d k) +
      terminalSquares M N := by
  dsimp only
  rw [full_cap_row hk h₁ h₂ h₃, first_proper_family]

end
end BlockPermanents.FourNative
