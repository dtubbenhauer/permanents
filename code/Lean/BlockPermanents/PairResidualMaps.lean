import BlockPermanents.PairSeamCut
import BlockPermanents.BendCoordinates

/-! # Fixed matrices for the residual halfwebs in Lemma 7A.1 -/

namespace BlockPermanents.PairResidual
open Closures Bend
open scoped BigOperators Matrix
noncomputable section

/-- Attach the fixed positive input to the word on the marked input. -/
private def attach {I : Type*} [DecidableEq I] (F : I → ℂ) :
    Matrix (I × I) I ℂ := fun u j => if u.2 = j then F u.1 else 0

private theorem attach_apply {I : Type*} [Fintype I] [DecidableEq I] (F H : I → ℂ) :
    (attach F).mulVec H = product F H := by
  funext u
  simp [attach, Matrix.mulVec, dotProduct, ite_mul, product]

/-- Read the positive cable in its orthonormal basis and keep the dual index. -/
private def readSeam {I : Type*} [Fintype I] [DecidableEq I] (W : Submodule ℂ (I → ℂ)) :
    Matrix (SupportCup.Seam W) (I × I) ℂ := fun z u =>
      if z.2 = u.2 then star (SupportCup.basisColumn W z.1 u.1) else 0

private theorem readSeam_apply {I : Type*} [Fintype I] [DecidableEq I]
    (W : Submodule ℂ (I → ℂ)) (v : I × I → ℂ) :
    (readSeam W).mulVec v = SupportCup.coords W (fun i j => v (i,j)) := by
  funext z
  simp [readSeam, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, SupportCup.coords]

/-- The matrix of the conjugated residual halfweb in the second input H.
Its factors, from right to left, attach F, open the r-cut, read the seam,
and remove the trace cup. Entrywise conjugation turns the marked action linear. -/
def residualMatrix {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :
    Matrix (SupportCup.Seam (space x r)) (Word d k) ℂ :=
  BendCoordinates.conjugate
    (SupportCup.J (space x r) * readSeam (space x r) * wordCap d k k r * attach (scaled a x))

/-- The matrix acts on every second input, with no symmetry assumption. -/
theorem residualMatrix_apply {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) (r : CutIndex k k)
    (H : Word d k → ℂ) :
    (residualMatrix a x r).mulVec H = fun i => star (residual a x H r i) := by
  let T := SupportCup.J (space x r) * readSeam (space x r) * wordCap d k k r * attach (scaled a x)
  have hd := BendCoordinates.dual_action T (fun i => star (H i))
  simp only [star_star] at hd
  change (BendCoordinates.conjugate T).mulVec H = _
  rw [hd]
  simp only [T, ← Matrix.mulVec_mulVec, attach_apply, readSeam_apply]
  rfl

/-- Reading the residual in the conjugate output basis preserves its squared norm. -/
theorem residualMatrix_energy {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) (r : CutIndex k k)
    (H : Word d k → ℂ) :
    energy ((residualMatrix a x r).mulVec H) = energy (residual a x H r) := by
  rw [residualMatrix_apply]
  simp [energy, Complex.star_def]

end
end BlockPermanents.PairResidual
