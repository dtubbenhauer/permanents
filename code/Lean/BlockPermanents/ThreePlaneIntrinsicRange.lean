import BlockPermanents.ThreePlaneTensorRange
import BlockPermanents.ThreePlaneBoundary
import BlockPermanents.ThreePlaneSpan
import BlockPermanents.ThreePlaneWords

/-! The range of the three clasped columns as a subspace of the original boundary. -/
namespace BlockPermanents.ThreePlane
open ThreeGeneralOpen Bend BendCoordinates TensorCoordinates
noncomputable section

/-- The tensor product of the two upright symmetric word spaces. -/
def symmetricPairSpace (d k : ℕ) : Submodule ℂ (K d k × K d k → ℂ) :=
  Submodule.span ℂ {z | ∃ f h : K d k → ℂ, Symmetric f ∧ Symmetric h ∧ product f h = z}

theorem symmetricPair_range (d k : ℕ) :
    LinearMap.range (legs (symClasp d k) (symClasp d k)).mulVecLin = symmetricPairSpace d k := by
  change LinearMap.range (tensor (symClasp d k) (symClasp d k)).mulVecLin = _
  rw [tensor_range, symmetricPairSpace]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨_,⟨f,rfl⟩,_,⟨h,rfl⟩,rfl⟩
    exact ⟨_,_,PairBound.projected_symmetric d k f,PairBound.projected_symmetric d k h,rfl⟩
  · rintro ⟨f,h,hf,hh,rfl⟩
    exact ⟨f,⟨f,hf⟩,h,⟨h,hh⟩,rfl⟩

/-- The whole ordinary pair tensored with the dual symmetric power of S. -/
def intrinsicBoundary {d : ℕ} (k : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    Submodule ℂ (ThreeWords d k → ℂ) :=
  Submodule.span ℂ {z | ∃ f ∈ symmetricPairSpace d k, ∃ h ∈ symmetricPower k S,
    product f (fun w => star (h w)) = z}

/-- The original boundary map ranges over precisely the full intrinsic
subspace in Theorem 3D.2, for arbitrary k and subspace dimension. -/
theorem symmetricBoundary_range {d : ℕ} (k : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    LinearMap.range (symmetricBoundary d k (power (Fin k) (basisMatrix S))).mulVecLin =
      intrinsicBoundary k S := by
  rw [symmetricBoundary, bent_tensor_range, symmetricPair_range, clasp_power, symmetricPower_range]
  rfl

end
end BlockPermanents.ThreePlane
