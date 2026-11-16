import BlockPermanents.GramInverse
import Mathlib.Data.Matrix.Block

/-! # Applying the inverse separately on each routed-cap occupation sector -/
namespace BlockPermanents.GramInverse
open Matrix
open scoped Matrix
noncomputable section
variable {ι b κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b] [Fintype κ]

/-- The index b ranges over an orthonormal output basis. All basis vectors
in a common sector select the same Gram matrix, so that repeated diagonal
blocks give the tensor factor with the identity on that sector. -/
theorem sector_projection {L : Type*} (sector : b → L) (C : Matrix (ι × b) κ ℂ)
    (G : L → Matrix ι ι ℂ) (hg : ∀ l,(G l).IsHermitian)
    (h : C*Cᴴ = blockDiagonal (fun t => G (sector t))) :
    let D := blockDiagonal (fun t => inverse (hg (sector t)))
    let P := Cᴴ*D*C
    P.IsHermitian ∧ P*P=P ∧ Set.range P.mulVec=Set.range Cᴴ.mulVec := by
  apply sandwich_projection
  · change (blockDiagonal (fun t => inverse (hg (sector t))))ᴴ=_
    rw [blockDiagonal_conjTranspose]
    exact congrArg blockDiagonal (funext fun t => hermitian (hg (sector t)))
  · rw [h,← blockDiagonal_mul,← blockDiagonal_mul]
    exact congrArg blockDiagonal (funext fun t => sandwich (hg (sector t)))

end
end BlockPermanents.GramInverse
