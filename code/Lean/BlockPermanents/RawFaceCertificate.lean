import BlockPermanents.FacePropagationSquares
import BlockPermanents.RawFaceWeights
import BlockPermanents.RefinedCoarse

/-! Lemma AA.3 with its sum over actual unordered disjoint configurations. -/
namespace BlockPermanents.RawFaceCertificate
open FaceMeans FaceSlacks FacePeel FaceCounts RawFaceMeans RawFaceWeights CycleMatching
noncomputable section

variable {q d : ℕ}

/-- Sum on the right of (AA.4), counting a prescribed four-set and unordered
matching once each. Terms outside 4+2r ≤ q have zero coefficient. -/
def prescribed (x : Input q d) : ℝ :=
  ∑ r ∈ Finset.range (q+1), coeff q r * ∑ c ∈ configs q r, value x c

open private four_slack from BlockPermanents.RefinedCoarse in
private theorem one_degree (x : Input q d) (r : ℕ) :
    (Threshold.spectator q r : ℝ) * S x 4 r =
      4 * (coeff q r * ∑ c ∈ configs q r, value x c) := by
  by_cases fit : 4+2*r ≤ q
  · rw [RawFaceWeights.sum_eq x r fit,four_slack x (by omega),← FaceCounts.counted]
    ring
  · have ho := FaceWeights.spectator_outside (lt_of_not_ge fit)
    simp only [coeff,ho,Nat.cast_zero,zero_div,zero_mul,mul_zero]

open private U_sum full_H from BlockPermanents.RefinedCoarse in
/-- The physical exit squares left over in (AA.4), including the first
four labels where the raw bound is tight. -/
theorem raw_identity (x : Input q d) (unit : ∀ i, Bend.energy (x i)=1) :
    (∑ r ∈ Finset.range (q/2+1), (Threshold.pathCoeff q r : ℝ) * Z (Closures.crossGram x x) r) -
      MatchingFine.fine x = prescribed x + FacePropagationSquares.propagation x q 0 / 4 := by
  have h := FacePropagationSquares.propagate_squares (q:=q) (r:=0) (R:=q) x unit (by omega) le_rfl
  change 4*(U _ q 0-H x 0 q) = _ at h
  rw [U_sum _ q 0 (q/2) le_rfl,full_H x] at h
  simp only [FaceWeights.weighted,Nat.zero_add,one_degree,← Finset.mul_sum] at h
  unfold prescribed
  linarith only [h]

theorem raw_bound (x : Input q d) (unit : ∀ i, Bend.energy (x i)=1) :
    prescribed x ≤ (∑ r ∈ Finset.range (q/2+1), (Threshold.pathCoeff q r : ℝ) *
      Z (Closures.crossGram x x) r) - MatchingFine.fine x := by
  rw [raw_identity x unit]
  exact le_add_of_nonneg_right (div_nonneg (FacePropagationSquares.propagation_nonneg x (by omega)) (by norm_num))

theorem four_exact (x : Input 4 d) (unit : ∀ i, Bend.energy (x i)=1) :
    (∑ r ∈ Finset.range (4/2+1), (Threshold.pathCoeff 4 r : ℝ) * Z (Closures.crossGram x x) r) -
      MatchingFine.fine x = prescribed x := by
  simpa only [FacePropagationSquares.propagation, zero_div, add_zero] using raw_identity x unit

end
end BlockPermanents.RawFaceCertificate
