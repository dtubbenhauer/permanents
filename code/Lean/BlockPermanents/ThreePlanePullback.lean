import BlockPermanents.ThreeOriginal
import BlockPermanents.BendCoordinates

/-! Changing the marked input of the original three-packet transfer. -/
namespace BlockPermanents.ThreePlane
open ThreeGeneralOpen Bend BendCoordinates
open scoped Matrix BigOperators
noncomputable section

private theorem legs_right {A B I J L : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (X : Matrix A I ℂ) (N : Matrix B J ℂ) (V : Matrix J L ℂ) :
    legs X (N * V) = legs X N * tensor (1 : Matrix I I ℂ) V := by
  classical
  ext ⟨a,b⟩ ⟨i,l⟩
  simp [legs, tensor, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
    ite_mul, mul_ite, mul_assoc, Finset.mul_sum]

/-- Pulling back the unbent transfer along a map on the marked input
replaces every marked foot N by N times that map. -/
theorem corrected_pullback {d k : ℕ} {I J L : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (X : K d k → Matrix (K d k) I ℂ) (Y : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (V : Matrix J L ℂ) :
    (tensor (1 : Matrix I I ℂ) V)ᴴ * corrected X Y N * tensor 1 V =
      corrected X Y (N * V) := by
  simp only [corrected, coarse, opened, straight, mixed, Support.reflected, legs_right,
    Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

/-- The ordinary pair stays upright, while the marked boundary map acts
by its entrywise conjugate on the bent packet. -/
def markedBoundary (d k : ℕ) {J : Type*} (V : Matrix (K d k) J ℂ) :=
  tensor (1 : Matrix (K d k × K d k) (K d k × K d k) ℂ) (conjugate V)

/-- The compression of the actual bent operator is obtained by placing
the supplied rectangular map underneath the symmetric marked clasp. -/
theorem original_pullback (d k : ℕ) {J : Type*} [Fintype J] (V : Matrix (K d k) J ℂ) :
    (markedBoundary d k V)ᴴ *
        partialTranspose ((internal d k)ᴴ * original d k * internal d k) *
        markedBoundary d k V =
      partialTranspose (corrected (M d k) (P d k) (symClasp d k * V)) := by
  rw [markedBoundary, ← partial_congr, original_corrected, corrected_pullback]

end
end BlockPermanents.ThreePlane
