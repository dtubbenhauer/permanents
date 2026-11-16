import BlockPermanents.BendCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The range of a tensor boundary contains the entire span of products. -/
namespace BlockPermanents.ThreePlane
open Bend BendCoordinates
noncomputable section

variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

private theorem column_mem {D L : Type*} [Fintype L] (M : Matrix D L ℂ) (i : L) :
    M.col i ∈ LinearMap.range M.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem tensor_range (U : Matrix A I ℂ) (V : Matrix B J ℂ) :
    LinearMap.range (tensor U V).mulVecLin = Submodule.span ℂ
      {z | ∃ f ∈ LinearMap.range U.mulVecLin, ∃ h ∈ LinearMap.range V.mulVecLin,
        product f h = z} := by
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact Submodule.subset_span ⟨_,column_mem U i,_,column_mem V j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨f,rfl⟩,_,⟨h,rfl⟩,rfl⟩
    exact ⟨product f h, tensor_product U V f h⟩

/-- Bending the last factor conjugates its entire range; the ordinary and
marked inputs in the resulting span may have arbitrary correlations. -/
theorem bent_tensor_range (U : Matrix A I ℂ) (V : Matrix B J ℂ) :
    LinearMap.range (tensor U (conjugate V)).mulVecLin = Submodule.span ℂ
      {z | ∃ f ∈ LinearMap.range U.mulVecLin, ∃ h ∈ LinearMap.range V.mulVecLin,
        product f (fun w => star (h w)) = z} := by
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact Submodule.subset_span ⟨_,column_mem U i,_,column_mem V j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨f,rfl⟩,_,⟨h,rfl⟩,rfl⟩
    refine ⟨product f (fun j => star (h j)), ?_⟩
    rw [Matrix.mulVecLin_apply,tensor_product,dual_action]
    rfl

end
end BlockPermanents.ThreePlane
