import BlockPermanents.PairSeamCut

/-! The dashed seam in Lemma 7A.1 projects onto the kernel of the closing cap. -/
namespace BlockPermanents.PairResidual
open Bend SupportCup
open scoped Matrix
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Reclosing the residual projector gives zero. -/
theorem cap_J (W : Submodule ℂ (I → ℂ)) (hd : 0 < Rank W) : cap W * J W = 0 := by
  have hn : (Rank W : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  rw [J, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    bubble, Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hn, one_smul, sub_self]

/-- The residual projector fixes precisely those seam vectors whose cap is zero. -/
theorem J_fixes_iff (W : Submodule ℂ (I → ℂ)) (hd : 0 < Rank W) (z : Seam W → ℂ) :
    (J W).mulVec z = z ↔ (cap W).mulVec z = 0 := by
  constructor
  · intro hz
    rw [← hz, Matrix.mulVec_mulVec, cap_J W hd, Matrix.zero_mulVec]
  · intro hz
    rw [J, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
      ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, smul_zero, sub_zero]

/-- In particular the actual residual halfweb closes to zero on every input. -/
theorem residual_closes_to_zero {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (H : Word d k → ℂ) (r : CutIndex k k) (hr : 0 < rank x r) :
    (cap (space x r)).mulVec (residual a x H r) = 0 := by
  rw [residual, Matrix.mulVec_mulVec, cap_J _ hr, Matrix.zero_mulVec]

end
end BlockPermanents.PairResidual
