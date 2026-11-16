import BlockPermanents.FacePropagationSquares
import BlockPermanents.FaceTradeSquares

/-! The propagated four-face certificate, with one free positive parameter at
each matching degree. -/
namespace BlockPermanents.FaceCoarseCertificate
open FaceMeans FaceSlacks FacePeel Closures CycleMatching Threshold
noncomputable section

variable {m d : ℕ}

def gain (z : ℕ → ℝ) (m : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m+1), (spectator m r : ℝ)*((1-u r)*z (r+1)+(1-1/u r)*z (r+2))

/-- The deleted face squares and the signed four-label squares at every depth. -/
def remainder (x : Input m d) (u : ℕ → ℝ) : ℝ :=
  FacePropagationSquares.propagation x m 0 / 4 +
  (∑ r ∈ Finset.range (m+1), (spectator m r : ℝ)*FaceTradeSquares.remainder x r (u r)) / 4

theorem remainder_nonneg (x : Input m d) (u : ℕ → ℝ) (hu : ∀ r, 0 < u r) :
    0 ≤ remainder x u := by
  apply add_nonneg (div_nonneg (FacePropagationSquares.propagation_nonneg x (by omega)) (by norm_num))
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro r _
  by_cases fit : 2*r+4 ≤ m
  · exact mul_nonneg (Nat.cast_nonneg _) (FaceTradeSquares.remainder_nonneg x fit (hu r))
  · simp [FaceWeights.spectator_outside (show m < 4+2*r by omega)]

open private U_sum full_H from BlockPermanents.RefinedCoarse in
/-- The difference left over in the parameter trade in the proof of Lemma
7D.3 is the sum of the physical four-face and deletion remainders. -/
theorem coarse_identity (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1)
    (u : ℕ → ℝ) (hu : ∀ r, 0 < u r) :
    let z := Z (crossGram x x)
    (∑ r ∈ Finset.range (m/2+1), (pathCoeff m r : ℝ)*z r) =
      MatchingFine.fine x + gain z m u + remainder x u := by
  let z := Z (crossGram x x)
  have defn := FacePropagationSquares.propagate_squares (q:=m) (r:=0) (R:=m) x unit (by omega) le_rfl
  change 4*(U z m 0 - H x 0 m) = _ at defn
  rw [U_sum z m 0 (m/2) le_rfl,full_H x] at defn
  simp only [FaceWeights.weighted,Nat.zero_add] at defn
  have one (r : ℕ) : (spectator m r : ℝ)*S x 4 r =
      4*((spectator m r : ℝ)*((1-u r)*z (r+1)+(1-1/u r)*z (r+2))) +
      (spectator m r : ℝ)*FaceTradeSquares.remainder x r (u r) := by
    by_cases fit : 2*r+4 ≤ m
    · rw [FaceTradeSquares.four_identity x unit fit (u r) (hu r)]
      dsimp only [z]
      ring
    · simp [FaceWeights.spectator_outside (show m < 4+2*r by omega)]
  simp_rw [one] at defn
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at defn
  dsimp only
  change (∑ r ∈ Finset.range (m/2+1), (pathCoeff m r : ℝ)*z r) = _
  unfold gain remainder
  linear_combination defn / 4

end
end BlockPermanents.FaceCoarseCertificate
