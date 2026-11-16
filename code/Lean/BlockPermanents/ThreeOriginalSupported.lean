import BlockPermanents.ThreeOriginal
import BlockPermanents.ThreeGeneralSupported

/-! The supported coordinate compression of the original three-packet operator. -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend SchurNormalization
open scoped Matrix ComplexOrder BigOperators
noncomputable section

def includeMark {d k : ℕ} (S : Finset (Fin d))
    (i : (K d k × K d k) × {w : K d k // ∀ t,w t∈S}) : ThreeWords d k := (i.1,i.2.val)

theorem restrict_corrected {d k : ℕ} (S : Finset (Fin d)) :
    (partialTranspose (corrected (M d k) (P d k) (symClasp d k))).submatrix (includeMark S) (includeMark S) =
      partialTranspose (corrected (M d k) (P d k) (ThreeLastRouted.markedColumns S)) := by
  ext ⟨i,j⟩ ⟨a,b⟩
  simp only [Matrix.submatrix_apply,includeMark,partialTranspose,corrected,coarse,opened,straight,mixed,
    Support.reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.add_apply,Matrix.sub_apply,legs,ThreeLastRouted.markedColumns]

/-- Theorem 3D.2 in original word coordinates: positivity after bending
the marked packet and restricting its dual to the chosen support. -/
theorem original_supported {d k : ℕ} (hk : 2≤k)
    (hs : HomogeneousSchur d k k) (hb : HomogeneousSchur d (k+k) k)
    (S : Finset (Fin d)) (hS : 0<S.card) (hSk : S.card≤k) :
    ((partialTranspose ((internal d k)ᴴ*original d k*internal d k)).submatrix
      (includeMark S) (includeMark S)).PosSemidef := by
  rw [original_corrected,restrict_corrected]
  exact canonical_supported_psd hk hs hb S hS hSk

end
end BlockPermanents.ThreeGeneralOpen
