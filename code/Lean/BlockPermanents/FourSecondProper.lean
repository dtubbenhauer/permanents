import BlockPermanents.FourMergedOrder
import BlockPermanents.FourMergedClasp
import BlockPermanents.FourFirstProper

/-! # The second family of proper cuts in the four-packet bend, equation (5C.3) -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourThickOpenings FourWireAlgebra Support ThreeGeneralOpen
open scoped Matrix BigOperators
noncomputable section

/-- Wᵣ in the displayed order. The first ordinary packet passes through;
the next two enter the symmetric 2k-clasp before the contraction with packet four. -/
def secondProperHalf {d k : ℕ} (r : CutIndex (2*k) k) :
    Matrix (Word d ((3-2)*k) × (Word d (2*k-r) × Word d (k-r)))
      (Triple d k × Word d k) ℂ :=
  fun row col => routed
    (fun s => symClasp d (2*k) * (drawnMergedSlice s * (ordinaryFoot d k * ZeroCap.inner d k 3)))
    (symClasp d k) r row.1 row.2 col

theorem secondProperHalf_native {d k : ℕ} (r : CutIndex (2*k) k) :
    secondProperHalf (d:=d) r = mergedProperHalf 2 (by decide)
      (ordinaryFoot d k * ZeroCap.inner d k 3) (symClasp d k) r := by
  rw [← drawn_merged_eq]
  funext row col
  exact congrFun (congrFun
    (routed_merge_clasp (fun s => drawnMergedSlice s * (ordinaryFoot d k * ZeroCap.inner d k 3))
      (symClasp d k) r row.1) row.2) col

/-- The individual weighted exchange in the actual second family. -/
theorem second_proper_term {d k : ℕ} (r : CutIndex (2*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    let P := localClasp d k 2
    let e := act d k (FourThickSlots.exchange k 2 (by decide) r)
    let F := ordinary (packets d k)
    (3 * a k) • read M N (sand F ((weight (2*k) k r : ℚ) • (P * e * P))) =
      (3 * a k * ((2*k).choose r : ℚ) * (k.choose r : ℚ)) •
        reflected (secondProperHalf (d:=d) r) := by
  dsimp only
  rw [map_smul, map_smul, smul_smul, proper_boundary _ _ (clasps_fixed d k) 2 (by decide) _,
    read_merged_cut, secondProperHalf_native]
  simp only [weight, Nat.cast_mul, mul_assoc]

/-- All indices satisfy 0 < r < k. -/
theorem second_proper_family (d k : ℕ) :
    (3 * a k) • read (ZeroCap.inner d k 3) (symClasp d k) (W₂ d k) =
      ∑ r ∈ properIndices (2*k) k,
        (3 * a k * ((2*k).choose r : ℚ) * (k.choose r : ℚ)) •
          reflected (secondProperHalf (d:=d) r) := by
  unfold W₂ proper
  rw [map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun r _ => second_proper_term r)

/-- For quadratic packets the only proper cut contributes 144 W₁† W₁. -/
theorem quadratic_second_family (d : ℕ) :
    (3 * a 2) • read (ZeroCap.inner d 2 3) (symClasp d 2) (W₂ d 2) =
      (144 : ℚ) • reflected (secondProperHalf (d:=d) (k:=2) 1) := by
  rw [second_proper_family, show properIndices (2*2) 2 = {1} by decide +kernel,
    Finset.sum_singleton]
  congr 1
  decide +kernel

/-- The first two proper families and the full-cap row in the original bent Q.
The third proper family retains its native opening. -/
theorem transfer_second_proper {d k : ℕ} (hk : 0 < k)
    (h₁ : SchurNormalization.HomogeneousSchur d k k)
    (h₂ : SchurNormalization.HomogeneousSchur d (2*k) k)
    (h₃ : SchurNormalization.HomogeneousSchur d (3*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    read M N (Q d k) =
      (∑ r ∈ properIndices (1*k) k,
        (6 * (k.choose r : ℚ)^2) • reflected (firstProperHalf (d:=d) r)) +
      (∑ r ∈ properIndices (2*k) k,
        (3 * a k * ((2*k).choose r : ℚ) * (k.choose r : ℚ)) •
          reflected (secondProperHalf (d:=d) r)) +
      scale 3 k • read M N (V d k) + terminalSquares M N := by
  dsimp only
  rw [transfer_first_proper hk h₁ h₂ h₃, second_proper_family]

end
end BlockPermanents.FourNative
