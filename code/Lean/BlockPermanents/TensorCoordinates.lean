import BlockPermanents.Transfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.ConjTranspose

/-! # Tensor powers of coordinate maps and naturality under thin-slot permutations -/
namespace BlockPermanents.TensorCoordinates
open scoped BigOperators Matrix
noncomputable section
variable {α β γ : Type*}

/-- Coordinate matrix of the same linear change of basis in every thin slot. -/
def power (ι : Type*) [Fintype ι] (A : Matrix β α ℂ) : Matrix (ι → β) (ι → α) ℂ :=
  fun v w => ∏ t, A (v t) (w t)

theorem power_mul (ι : Type*) [Fintype ι] [DecidableEq ι] [Fintype β] (A : Matrix γ β ℂ) (B : Matrix β α ℂ) :
    power ι (A*B) = power ι A * power ι B := by
  classical
  ext v w
  simp only [power,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i j => A (v i) j * B j (w i))

theorem power_one (ι α : Type*) [Fintype ι] [DecidableEq α] :
    power ι (1 : Matrix α α ℂ) = 1 := by
  classical
  ext v w
  simp only [power,Matrix.one_apply,Fintype.prod_boole,funext_iff]

theorem power_star (ι : Type*) [Fintype ι] (A : Matrix β α ℂ) :
    power ι A.conjTranspose = (power ι A).conjTranspose := by
  classical
  ext v w
  simp [power,Matrix.conjTranspose_apply]

theorem naturality (ι : Type*) [Fintype ι] [DecidableEq ι] [Fintype α] (A : Matrix β α ℂ)
    (p : Equiv.Perm ι) (y : (ι → α) → ℂ) :
    Transfer.tensorAction ι β p ((power ι A).mulVec y) =
      (power ι A).mulVec (Transfer.tensorAction ι α p y) := by
  classical
  funext v
  let e := p.symm.arrowCongr (Equiv.refl α)
  change (∑ w : ι → α, (∏ i, A (v (p i)) (w i)) * y w) =
    ∑ w : ι → α, (∏ i, A (v i) (w i)) * y (w ∘ p)
  rw [← e.sum_comp (fun w => (∏ i,A (v (p i)) (w i)) * y w)]
  apply Finset.sum_congr rfl
  intro w _
  change (∏ i, A (v (p i)) (w (p i))) * y (w ∘ p) = _
  exact congrArg (fun z => z * y (w ∘ p)) (Equiv.prod_comp p (fun i => A (v i) (w i)))

end
end BlockPermanents.TensorCoordinates
