import BlockPermanents.BalancedLastPlanes
import BlockPermanents.BalancedLastCompression

/-! Last-cap weights and the marked quadratic form on actual subspaces. -/
namespace BlockPermanents.BalancedLast
open Bend BalancedOpen BalancedRoutes BalancedEvaluation BalancedPairTrace
open BalancedLastDifferences BalancedSupport ThreePlane SchurNormalization
open scoped Matrix ComplexOrder
noncomputable section

/-- The ordinary legs are symmetric. The two turned legs are supported on
the dual symmetric powers of S and T. The joint coefficients are unrestricted. -/
def OnPlanes {d k : ℕ} (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (z : Boundary (Word d k) → ℂ) : Prop :=
  (∀ b c e, Symmetric (fun a => z ((a,b),(c,e)))) ∧
  (∀ a c e, Symmetric (fun b => z ((a,b),(c,e)))) ∧
  (∀ a b e, (fun c => star (z ((a,b),(c,e)))) ∈ symmetricPower k S) ∧
  (∀ a b c, (fun e => star (z ((a,b),(c,e)))) ∈ symmetricPower k T)

/-- Lemma 6B.1 on the two named planes. -/
theorem subspace_last_cap_weight {d k : ℕ} (hk : 0 < k)
    (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (hT : Module.finrank ℂ T = k)
    (z : Boundary (Word d k) → ℂ) (hz : OnPlanes S T z) :
    let U := turnedFrame S hS
    let V := turnedFrame T hT
    (edgeEnergy false z + edgeEnergy true z)/2 =
      lastWeight k/2 * edgeDiagonal z + lastWeight k * matchingDiagonal z +
      (borderRemainder false U V z + borderRemainder true U V z)/2 :=
  last_cap_weight hk _ _ (turnedFrame_isometry S hS) (turnedFrame_isometry T hT)
    z ((supported_iff S T hS hT z).mpr hz)

/-- The balanced marked operator evaluated on every joint state in the
two ordinary symmetric powers and the two specified dual symmetric powers. -/
theorem subspace_marked_decomposition {d k : ℕ} (hk : 0 < k)
    (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (hT : Module.finrank ℂ T = k)
    (z : Boundary (Word d k) → ℂ) (hz : OnPlanes S T z) :
    let U := turnedFrame S hS
    let V := turnedFrame T hT
    (quadratic (partialTranspose (BalancedAssembly.marked d k)) z).re =
      ((k+k).choose k : ℝ)^2 * fineEnergy z +
        (borderRemainder false U V z + borderRemainder true U V z)/2 +
        sixDifferences (L00 z) (L01 z) (L10 z) (L11 z) +
        Complex.normSq (Ndirect z - Ncross z) +
        (lastWeight k/2 - 4) * edgeDiagonal z + (lastWeight k - 2) * matchingDiagonal z :=
  marked_decomposition hk _ _ (turnedFrame_isometry S hS) (turnedFrame_isometry T hT)
    z ((supported_iff S T hS hT z).mpr hz)

/-- Lemma 6B.3 on any choices of the two planes of dimension k. -/
theorem subspace_marked_nonnegative {d k : ℕ} (hk : 4 ≤ k)
    (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (hT : Module.finrank ℂ T = k)
    (z : Boundary (Word d k) → ℂ) (hz : OnPlanes S T z) :
    0 ≤ (quadratic (partialTranspose (BalancedAssembly.marked d k)) z).re :=
  marked_nonnegative hk _ _ (turnedFrame_isometry S hS) (turnedFrame_isometry T hT)
    z ((supported_iff S T hS hT z).mpr hz)

/-- The compressed Hermitian matrix is positive semidefinite on every finite
family of joint inputs supported on the two chosen planes. -/
theorem subspace_compression_psd {d k : ℕ} (hk : 4 ≤ k)
    (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (hT : Module.finrank ℂ T = k)
    {J : Type*} [Fintype J] (B : Matrix (Boundary (Word d k)) J ℂ)
    (hB : ∀ j, OnPlanes S T (fun i => B i j)) :
    (Bᴴ * partialTranspose (BalancedAssembly.marked d k) * B).PosSemidef :=
  marked_compression_psd hk _ _ (turnedFrame_isometry S hS) (turnedFrame_isometry T hT)
    B (fun j => (supported_iff S T hS hT _).mpr (hB j))

end
end BlockPermanents.BalancedLast
