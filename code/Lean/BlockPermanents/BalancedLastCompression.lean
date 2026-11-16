import BlockPermanents.BalancedLastForm
import BlockPermanents.Bridges

/-! The positive semidefinite compression in Lemma 6B.3 on any finite
family of four-packet boundary tensors with the two specified marked planes. -/
namespace BlockPermanents.BalancedLast
open Bend BalancedPairTrace BalancedAssembly BalancedPacket SchurNormalization Matrix Closures
open scoped Matrix ComplexOrder
noncomputable section

/-- Every term in the opening of the balanced partial transpose is a real
multiple of a reflected halfweb. -/
theorem marked_hermitian {d k : ℕ} (hk : 0 < k) :
    (partialTranspose (marked d k)).IsHermitian := by
  rw [BalancedAssembly.opening hk (homogeneousSchur d k k) (homogeneousSchur d (k+k) (k+k))
    (homogeneousSchur _ 2 2)]
  simp [Matrix.IsHermitian, fineProper, edgeProper, BalancedCorners.weighted, a, Support.reflected,
    conjTranspose_sub, conjTranspose_smul, conjTranspose_sum, conjTranspose_mul,
    star_mul', mul_comm (Bend.weight _ _ _ : ℂ) (Bend.weight _ _ _ : ℂ)]

private theorem slice_sum {I J : Type*} [Fintype J] (W : Submodule ℂ (I → ℂ))
    (f : J → I → ℂ) (x : J → ℂ) (hf : ∀ j, f j ∈ W) :
    (fun i => ∑ j, f j i * x j) ∈ W := by
  rw [show (fun i => ∑ j, f j i * x j) = ∑ j, x j • f j by
    ext i; simp [mul_comm]]
  exact W.sum_mem (fun j _ => W.smul_mem _ (hf j))

/-- All linear combinations of columns satisfy the same six slice conditions. -/
theorem supported_mulVec {d k : ℕ} (U V : Matrix (Fin d) (Fin k) ℂ)
    {J : Type*} [Fintype J] (B : Matrix (Boundary (Word d k)) J ℂ)
    (hB : ∀ j, Supported U V (fun i => B i j)) (x : J → ℂ) :
    Supported U V (B.mulVec x) := by
  constructor
  · intro b c e; exact slice_sum _ _ x fun j => (hB j).sym0 b c e
  · intro a c e; exact slice_sum _ _ x fun j => (hB j).sym1 a c e
  · intro a b e; exact slice_sum _ _ x fun j => (hB j).sym2 a b e
  · intro a b c; exact slice_sum _ _ x fun j => (hB j).sym3 a b c
  · intro a b e; exact slice_sum _ _ x fun j => (hB j).plane2 a b e
  · intro a b c; exact slice_sum _ _ x fun j => (hB j).plane3 a b c

/-- The compression of the balanced marked partial transpose to any finite
supported family is positive semidefinite, including dependent columns. -/
theorem marked_compression_psd {d k : ℕ} (hk : 4 ≤ k)
    (U V : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    {J : Type*} [Fintype J] (B : Matrix (Boundary (Word d k)) J ℂ)
    (hB : ∀ j, Supported U V (fun i => B i j)) :
    (Bᴴ * partialTranspose (marked d k) * B).PosSemidef := by
  let M := partialTranspose (marked d k)
  have hM : M.IsHermitian := marked_hermitian (by omega)
  refine ⟨isHermitian_conjTranspose_mul_mul B hM,fun x => ?_⟩
  let y := B.mulVec x
  have q := marked_nonnegative hk U V hU hV y (supported_mulVec U V B hB x)
  rw [Bridges.quadratic_bracket] at q
  have real : star (bracket y (M.mulVec y)) = bracket y (M.mulVec y) := by
    change star (dotProduct (star y) (M.mulVec y)) = dotProduct (star y) (M.mulVec y)
    calc
      _ = dotProduct (star (M.mulVec y)) y := (star_dotProduct (M.mulVec y) y).symm
      _ = _ := by rw [star_mulVec,← dotProduct_mulVec,hM.eq]
  have im := congrArg Complex.im real
  simp only [Complex.star_def,Complex.conj_im] at im
  have pos : 0 ≤ dotProduct (star y) (M.mulVec y) := by
    refine Complex.nonneg_iff.mpr ⟨q,?_⟩
    change 0 = (bracket y (M.mulVec y)).im
    linarith
  simpa only [y,M,star_mulVec,dotProduct_mulVec,vecMul_vecMul] using pos

end
end BlockPermanents.BalancedLast
