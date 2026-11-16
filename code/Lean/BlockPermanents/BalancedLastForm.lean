import BlockPermanents.BalancedLastWeight
import BlockPermanents.HomogeneousSchurProof

/-! Squares of the balanced marked operator on two independently supported turned packets. -/
namespace BlockPermanents.BalancedLast
open Bend BalancedPairTrace BalancedPacket BalancedRoutes BalancedEvaluation
open BalancedLastDifferences BalancedSupport SchurNormalization
open scoped Matrix
noncomputable section

/-- The supported quadratic form of the original marked partial transpose.
For k ≥ 4 every displayed summand is nonnegative. -/
theorem marked_decomposition {d k : ℕ} (hk : 0 < k)
    (U V : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (z : Boundary (Word d k) → ℂ) (hz : Supported U V z) :
    (quadratic (partialTranspose (BalancedAssembly.marked d k)) z).re =
      ((k+k).choose k : ℝ)^2 * fineEnergy z +
        (borderRemainder false U V z + borderRemainder true U V z)/2 +
        sixDifferences (L00 z) (L01 z) (L10 z) (L11 z) +
        Complex.normSq (Ndirect z - Ncross z) +
        (lastWeight k/2 - 4) * edgeDiagonal z + (lastWeight k - 2) * matchingDiagonal z := by
  rw [BalancedEvaluation.opening hk (homogeneousSchur d k k) (homogeneousSchur d (k+k) (k+k))
      (homogeneousSchur _ 2 2), last_cap_weight hk U V hU hV z hz]
  linarith only [completed_routes (lastWeight k) z]

/-- Lemma 6B.3 from the individual squares of Lemma 6B.1. -/
theorem marked_nonnegative {d k : ℕ} (hk : 4 ≤ k)
    (U V : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (z : Boundary (Word d k) → ℂ) (hz : Supported U V z) :
    0 ≤ (quadratic (partialTranspose (BalancedAssembly.marked d k)) z).re := by
  rw [marked_decomposition (by omega) U V hU hV z hz]
  have hFine : 0 ≤ ((k+k).choose k : ℝ)^2 * fineEnergy z :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
  have hBorder := add_nonneg (borderRemainder_nonneg false U V z) (borderRemainder_nonneg true U V z)
  obtain ⟨hE,hM⟩ := unused_diagonals_nonneg hk z
  linarith only [hFine,hBorder,sixDifferences_nonneg (L00 z) (L01 z) (L10 z) (L11 z),
    Complex.normSq_nonneg (Ndirect z - Ncross z),hE,hM]

end
end BlockPermanents.BalancedLast
