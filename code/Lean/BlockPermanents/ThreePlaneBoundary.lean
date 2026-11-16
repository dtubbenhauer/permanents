import BlockPermanents.ThreePlanePullback

/-! The three clasped boundary maps for the bare partially transposed transfer. -/
namespace BlockPermanents.ThreePlane
open ThreeGeneralOpen Bend BendCoordinates
open scoped Matrix
noncomputable section

/-- Both upright factors carry their packet clasps. The marked factor carries
the dual of its symmetric inclusion into the ambient word coordinates. -/
def symmetricBoundary (d k : ℕ) {J : Type*} (V : Matrix (K d k) J ℂ) :=
  tensor (legs (symClasp d k) (symClasp d k)) (conjugate (symClasp d k * V))

open private legs_right from BlockPermanents.ThreePlanePullback in
/-- One may apply the three packet clasps on the boundary and then evaluate
the original partially transposed transfer directly on those columns. -/
theorem bare_compression (d k : ℕ) {J : Type*} [Fintype J] (V : Matrix (K d k) J ℂ) :
    (symmetricBoundary d k V)ᴴ * partialTranspose (original d k) * symmetricBoundary d k V =
      (markedBoundary d k V)ᴴ * partialTranspose ((internal d k)ᴴ * original d k * internal d k) *
        markedBoundary d k V := by
  let C := symClasp d k
  let P := legs C C
  let Q := original d k
  change (tensor P (conjugate (C * V)))ᴴ * partialTranspose Q * tensor P (conjugate (C * V)) =
    (tensor 1 (conjugate V))ᴴ * partialTranspose ((tensor P C)ᴴ * Q * tensor P C) *
      tensor 1 (conjugate V)
  rw [← partial_congr, ← partial_congr]
  have h : tensor P (C * V) = tensor P C * tensor 1 V := legs_right P C V
  rw [h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end
end BlockPermanents.ThreePlane
