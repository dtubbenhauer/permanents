import BlockPermanents.HomogeneousSchurProof
import BlockPermanents.FourPlaneMarcus
import BlockPermanents.Paper

/-! # Matrix endpoints with the homogeneous Schur relation discharged -/
namespace BlockPermanents.VerifiedPaper
open SchurNormalization
open scoped Matrix ComplexOrder

/-- The matrix inequality throughout the parameter range of Theorem 1A.1. -/
theorem manuscript : ManuscriptTheorem := manuscript_theorem homogeneousSchur

/-- The logarithmic sufficient condition of Section 7. -/
theorem logarithmic {m k : ℕ} (hm : 2 ≤ m) (hk : 2 * Real.logb 2 m ≤ k) : MarcusAt m k :=
  MatchingThreshold.marcus_logarithmic hm hk (homogeneousSchur (m*k))

/-- Theorem 5D.1 for the full tensor space supported on a marked subspace K. -/
theorem plane_compression {d : ℕ} (K : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hK : Module.finrank ℂ K ≤ 2) {J : Type*} [Fintype J]
    (B : Matrix (FourCompression.Index d) J ℂ)
    (hs : ∀ j, (fun i => B i j) ∈ FourPlaneCompression.planeSupport K) :
    (Bᴴ * Bend.partialTranspose (FourCompression.markedMatrix d) * B).PosSemidef :=
  FourPlaneCompression.compression_psd K hK (homogeneousSchur d 2 2)
    (homogeneousSchur d 4 2) (homogeneousSchur d 6 2) B hs

/-- The four-quadratic inequality obtained by averaging the plane-supported cuts. -/
theorem four_quadratic : MarcusAt 4 2 :=
  FourPlaneCompression.marcus_four_quadratic (homogeneousSchur 8 2 2)
    (homogeneousSchur 8 4 2) (homogeneousSchur 8 6 2)

end BlockPermanents.VerifiedPaper
