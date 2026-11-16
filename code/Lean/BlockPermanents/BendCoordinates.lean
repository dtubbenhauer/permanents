import BlockPermanents.Bridges
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Partial transpose under arbitrary rectangular changes of coordinates -/
namespace BlockPermanents.BendCoordinates
open Matrix Bend
open scoped BigOperators Matrix
noncomputable section
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]

/-- Tensor product of two rectangular coordinate matrices. -/
def tensor (U : Matrix A I ℂ) (V : Matrix B J ℂ) : Matrix (A×B) (I×J) ℂ :=
  fun p q => U p.1 q.1 * V p.2 q.2

def conjugate (V : Matrix B J ℂ) : Matrix B J ℂ := fun x y => star (V x y)

private def crossed : (A×B)×(A×B) ≃ (A×B)×(A×B) where
  toFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  invFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis change on the dual marked factor is entrywise conjugated.
No isometry or squareness is required of either factor here. -/
theorem partial_congr (M : Matrix (A×B) (A×B) ℂ) (U : Matrix A I ℂ) (V : Matrix B J ℂ) :
    partialTranspose ((tensor U V)ᴴ * M * tensor U V) =
      (tensor U (conjugate V))ᴴ * partialTranspose M * tensor U (conjugate V) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  let f (p : (A×B)×(A×B)) :=
    star (U p.2.1 i*star (V p.2.2 j)) * M (p.2.1,p.1.2) (p.1.1,p.2.2) *
    (U p.1.1 k*star (V p.1.2 l))
  have h := (crossed (A:=A) (B:=B)).sum_comp f
  simp only [Fintype.sum_prod_type,f,crossed,Equiv.coe_fn_mk] at h
  simp only [partialTranspose,tensor,conjugate,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Finset.sum_mul,Fintype.sum_prod_type,star_mul',star_star]
  simp only [star_mul',star_star] at h
  convert h using 1
  · apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    ring

theorem tensor_product (U : Matrix A I ℂ) (V : Matrix B J ℂ) (u : I → ℂ) (v : J → ℂ) :
    (tensor U V).mulVec (product u v) = product (U.mulVec u) (V.mulVec v) := by
  funext p
  simp only [mulVec,dotProduct,tensor,product,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (s:=Finset.univ (α:=J))]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem dual_action (V : Matrix B J ℂ) (v : J → ℂ) :
    (conjugate V).mulVec (fun t => star (v t)) = fun s => star (V.mulVec v s) := by
  funext s; simp [conjugate,Matrix.mulVec,dotProduct,star_sum,star_mul',mul_comm]

end
end BlockPermanents.BendCoordinates
