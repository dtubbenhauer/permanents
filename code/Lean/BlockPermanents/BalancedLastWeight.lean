import BlockPermanents.BalancedLastJoint
import BlockPermanents.BalancedLastRectangle
import BlockPermanents.BalancedLastDifferences
import BlockPermanents.BalancedEvaluation

/-! Exact last-cap weights for the two crossing pairings of a balanced bend. -/
namespace BlockPermanents.BalancedLast
open Bend BalancedPairTrace BalancedPacket BalancedRoutes BalancedEvaluation BalancedExtremes
open BalancedLastJoint BalancedLastDifferences BalancedSupport
open scoped Matrix
noncomputable section

/-- For this pairing, keep each of the four perpendicular border halves and
each full interior half. The outer sum uses the two Schur cut weights. -/
def borderRemainder {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) : ℝ :=
  BalancedLastRectangle.remainder k (E flip z)
    (firstSquares flip U V z) (secondSquares flip U V z)

theorem borderRemainder_nonneg {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) : 0 ≤ borderRemainder flip U V z :=
  BalancedLastRectangle.remainder_nonneg k _ _ _
    (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (firstSquares_nonneg flip U V z) (secondSquares_nonneg flip U V z)

/-- Lemma 6B.1 before the factor 1/2. For a fixed crossing pairing,
the upper and right sides both complete to the same double cap. -/
theorem pairing_decomposition {d k : ℕ} (hk : 0 < k) (flip : Bool)
    (U V : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (z : Boundary (Word d k) → ℂ) (hz : Supported U V z) :
    edgeEnergy flip z = lastWeight k *
      (energy (if flip then L01 z else L00 z) + energy (if flip then L10 z else L11 z) +
        2 * Complex.normSq (if flip then Ncross z else Ndirect z)) +
      borderRemainder flip U V z := by
  have eqn := BalancedLastRectangle.rectangle_exact hk (E flip z) (firstSquares flip U V z)
    (secondSquares flip U V z) (fun r t _ _ => first_split hk flip U V hU hV z hz r t)
    (fun r t _ _ => second_split hk flip U V hU hV z hz r t)
  rw [first flip hz, second flip hz, full flip hz] at eqn
  exact eqn

/-- All four edge weights and both completed-pairing weights in (6A.4).
The two remainders are explicit weighted sums of reflected cuts. -/
theorem last_cap_weight {d k : ℕ} (hk : 0 < k)
    (U V : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (z : Boundary (Word d k) → ℂ) (hz : Supported U V z) :
    (edgeEnergy false z + edgeEnergy true z)/2 =
      lastWeight k/2 * edgeDiagonal z + lastWeight k * matchingDiagonal z +
      (borderRemainder false U V z + borderRemainder true U V z)/2 := by
  rw [pairing_decomposition hk false U V hU hV z hz, pairing_decomposition hk true U V hU hV z hz]
  simp only [Bool.false_eq_true, if_false, if_true, edgeDiagonal, matchingDiagonal]
  ring

end
end BlockPermanents.BalancedLast
