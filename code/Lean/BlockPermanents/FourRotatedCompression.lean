import BlockPermanents.FourBendCovariance
import BlockPermanents.FourCompressionPSD

/-! Compression of the quadratic marked bend on a rotated support plane. -/
namespace BlockPermanents.FourCovariance
open FourCompression FourSupportedTensor FourRoutes FourCapOrbit FourFullValues
open Bend BendCoordinates SchurNormalization
open scoped BigOperators Matrix ComplexOrder
noncomputable section

/-- Rotate the space of supported tensors, including its sums of products. -/
def rotatedSupport {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) (S : Finset (Fin d)) :
    Submodule ℂ (Boundary e) :=
  (Submodule.span ℂ (simple S)).map (bentChange A).mulVecLin

/-- Generators can be specified on the two factors independently. The marked
factor has the dual action; its unbent packet transforms by the ordinary power. -/
theorem rotatedSupport_eq {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) (S : Finset (Fin d)) :
    rotatedSupport A S = Submodule.span ℂ
      {z | ∃ (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ),
        Inner F ∧ Symmetric H ∧ Supported S H ∧
        product ((ordinaryChange A).mulVec F)
          (fun w => star (((TensorCoordinates.power (Fin 2) A).mulVec H) w)) = z} := by
  rw [rotatedSupport,Submodule.map_span]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨_,⟨F,H,hF,hH,hS,rfl⟩,rfl⟩
    refine ⟨F,H,hF,hH,hS,?_⟩
    rw [Matrix.mulVecLin_apply,bentChange,tensor_product,dual_action]
  · rintro ⟨F,H,hF,hH,hS,rfl⟩
    refine ⟨_,⟨F,H,hF,hH,hS,rfl⟩,?_⟩
    rw [Matrix.mulVecLin_apply,bentChange,tensor_product,dual_action]

/-- The bent quadratic form is nonnegative at every vector in the rotated span. -/
theorem rotated_nonnegative {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    (hA : Aᴴ * A = 1) (S : Finset (Fin d)) (hc : S.card ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2)
    (h₆ : HomogeneousSchur d 6 2) {z : Boundary e} (hz : z ∈ rotatedSupport A S) :
    0 ≤ (quadratic (partialTranspose (markedMatrix e)) z).re := by
  obtain ⟨x,hx,rfl⟩ := hz
  let T := bentChange A
  let M := partialTranspose (markedMatrix e)
  let N := partialTranspose (markedMatrix d)
  have cov : Tᴴ * M * T = N := bent_covariance A hA
  have eqn : quadratic M (T.mulVec x) = quadratic N x := by
    simp only [Bridges.quadratic_bracket]
    change star (T.mulVec x) ⬝ᵥ (M.mulVec (T.mulVec x)) = star x ⬝ᵥ (N.mulVec x)
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, cov]
  change 0 ≤ (quadratic M (T.mulVec x)).re
  rw [eqn]
  exact nonnegative_of_card_le S hc h₂ h₄ h₆ hx

/-- Compress to arbitrary generators of the rotated support. The columns may
be dependent and the number of upright generators is unrestricted. -/
theorem rotated_compression_psd {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    (hA : Aᴴ * A = 1) (S : Finset (Fin d)) (hc : S.card ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2)
    (h₆ : HomogeneousSchur d 6 2)
    {J : Type*} [Fintype J] (B : Matrix (Index e) J ℂ)
    (hs : ∀ j, (fun i => B i j) ∈ rotatedSupport A S) :
    (Bᴴ * partialTranspose (markedMatrix e) * B).PosSemidef := by
  classical
  let T := bentChange A
  let M := partialTranspose (markedMatrix e)
  let N := partialTranspose (markedMatrix d)
  have lifted (j : J) : ∃ x ∈ Submodule.span ℂ (simple S), T.mulVec x = fun i => B i j :=
    hs j
  choose x hx hB using lifted
  let C : Matrix (Index d) J ℂ := fun i j => x j i
  have cols : ∀ v, C.mulVec v ∈ Submodule.span ℂ (simple S) := by
    intro v
    have e : C.mulVec v = ∑ j, v j • x j := by
      ext i
      simp [C,Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]
    rw [e]
    exact (Submodule.span ℂ (simple S)).sum_mem fun j _ =>
      (Submodule.span ℂ (simple S)).smul_mem _ (hx j)
  have matrix_eq : T * C = B := by
    ext i j
    exact congrFun (hB j) i
  have cov : Tᴴ * M * T = N := bent_covariance A hA
  have eqn : Bᴴ * M * B = Cᴴ * N * C := by
    rw [← matrix_eq, Matrix.conjTranspose_mul]
    calc
      _ = Cᴴ * (Tᴴ * M * T) * C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [cov]
  change (Bᴴ * M * B).PosSemidef
  rw [eqn]
  exact compression_psd S hc h₂ h₄ h₆ C cols

end
end BlockPermanents.FourCovariance
