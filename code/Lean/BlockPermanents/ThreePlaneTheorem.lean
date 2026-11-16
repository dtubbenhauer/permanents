import BlockPermanents.ThreePlaneBasis
import BlockPermanents.ThreePlaneRouted
import BlockPermanents.ThreePlaneBoundary
import BlockPermanents.ThreeGeneralSupported
import BlockPermanents.HomogeneousSchurProof

/-! # The supported three-packet decomposition on an arbitrary marked subspace -/
namespace BlockPermanents.ThreePlane
open Bend ThreeGeneralOpen ThreeLastRouted Support SchurNormalization
open scoped Matrix BigOperators ComplexOrder
noncomputable section

/-- The marked columns in the ambient word coordinates. Every slot takes
values in S and the k strands are symmetrized. -/
def marked {d : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d)) (k : ℕ) :=
  symClasp d k * TensorCoordinates.power (Fin k) (basisMatrix S)

/-- Restrict the original bent three-packet operator to the marked subspace.
The boundary acts by the conjugate inclusion on the dual packet. -/
def compression {d : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d)) (k : ℕ) :=
  let B := symmetricBoundary d k (TensorCoordinates.power (Fin k) (basisMatrix S))
  Bᴴ * partialTranspose (original d k) * B

theorem compression_eq_internal {d : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d)) (k : ℕ) :
  let T := markedBoundary d k (TensorCoordinates.power (Fin k) (basisMatrix S))
  compression S k = Tᴴ * partialTranspose ((internal d k)ᴴ * original d k * internal d k) * T :=
  bare_compression d k _

private theorem marked_symmetric {d : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (k : ℕ) (j : Word (Module.finrank ℂ S) k) : Symmetric (fun w => marked S k w j) :=
  PairBound.projected_symmetric d k _

private theorem subspace_last_cut {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 1 ≤ k) (hs : 0 < Module.finrank ℂ S) :
    ∑ t, reflected (routed (M d k) (marked S k) (ThreeSupport.lastProper k) t) =
      reflected (perpendicular (basisMatrix S) (stackLast hk (M d k) (marked S k))) +
      (Module.finrank ℂ S : ℂ)⁻¹ • reflected (terminal (stack (M d k)) (marked S k)) :=
  routed_resolution (basisMatrix S) (basis_isometry S) hs hk (M d k) (marked S k)
    (symClasp (Module.finrank ℂ S) k) (clasp_power k (basisMatrix S))
    (pair_symmetric d k) (marked_symmetric S k)

/-- The five reflected-halfweb terms of Theorem 3D.2 on any nonzero marked
subspace. The exact identity itself has no upper bound on its dimension. -/
theorem subspace_decomposition {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 2 ≤ k) (hs : 0 < Module.finrank ℂ S) :
    let a : ℂ := (k+k).choose k
    let N := marked S k
    let v := terminal (stackedFine (P d k)) N
    let u := terminal (stack (M d k)) N
    let perp := perpendicular (basisMatrix S) (stackLast (show 1 ≤ k by omega) (M d k) N)
    compression S k =
      (2 : ℂ) • earlySquares (M d k) N +
      a • properSquares (by omega) (fun _ : Unit => P d k) N +
      (2*(k : ℂ)^2) • reflected perp + reflected (a • v - (1/2 : ℂ) • u) +
      (2*(k : ℂ)^2/(Module.finrank ℂ S : ℂ) - 9/4) • reflected u := by
  dsimp only
  rw [compression_eq_internal, original_pullback]
  exact resolve_raw hk (homogeneousSchur d k k) (homogeneousSchur d (k+k) k)
    (M d k) (P d k) (marked S k) (pair_symmetric d k)
    (fun i => column_symmetric d (k+k) (Fin.append i.1 i.2)) (marked_symmetric S k)
    _ (subspace_last_cut S (by omega) hs)

/-- The coefficient of the completed cap is strictly positive on the
dimension range of Theorem 3D.2. -/
theorem full_cap_weight_pos {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 2 ≤ k) (hs : 0 < Module.finrank ℂ S) (hsk : Module.finrank ℂ S ≤ k) :
    0 < 2*(k : ℝ)^2/(Module.finrank ℂ S : ℝ) - 9/4 :=
  three_full_cap_weight _ _ hk hs hsk

/-- The whole supported tensor space has a positive semidefinite compression.
The two ordinary packets and the dual marked packet may be entangled. -/
theorem subspace_compression_psd {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 2 ≤ k) (hs : 0 < Module.finrank ℂ S) (hsk : Module.finrank ℂ S ≤ k) :
    (compression S k).PosSemidef := by
  rw [compression_eq_internal, original_pullback]
  exact resolved_psd hk hs hsk (homogeneousSchur d k k) (homogeneousSchur d (k+k) k)
    (M d k) (P d k) (marked S k) (pair_symmetric d k)
    (fun i => column_symmetric d (k+k) (Fin.append i.1 i.2)) (marked_symmetric S k)
    _ (subspace_last_cut S (by omega) hs)

end
end BlockPermanents.ThreePlane
