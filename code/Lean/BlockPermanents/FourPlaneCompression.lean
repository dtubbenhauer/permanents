import BlockPermanents.FourPlaneBasis
import BlockPermanents.FourPlaneTensor

/-! # The marked compression on an arbitrary complex plane

The marked subspace is given in the original ambient coordinates. Products of
symmetrized atom pairs in this subspace generate its symmetric square. Taking
the joint span with arbitrary symmetric ordinary packets also allows
ordinary–marked entanglement.
-/

namespace BlockPermanents.FourPlaneCompression
open FourPlaneBasis FourCovariance FourCompression FourSupportedTensor
open FourRoutes FourCapOrbit Closures Bend SchurNormalization
open scoped Matrix ComplexOrder
noncomputable section

/-- Tensor product of the ordinary packet subspace with the conjugate of the
symmetric square of the actual marked subspace. -/
def planeSupport {d : ℕ} (K : Submodule ℂ (Ambient d)) : Submodule ℂ (Boundary d) :=
  Submodule.span ℂ {z | ∃ (F : Triple d 2 → ℂ) (x : Fin 2 → Ambient d),
    Inner F ∧ (∀ i, x i ∈ K) ∧
    product F (fun w => star (packet (fun i j => x i j) w)) = z}

/-- Rotating coordinates adapted to the marked atoms contains their entire joint
span with the ordinary symmetric triples. -/
theorem planeSupport_le_rotatedSupport {d : ℕ} (K : Submodule ℂ (Ambient d))
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ * A = 1) (S : Finset (Fin d))
    (hcoords : ∀ x ∈ K, ∃ c : Fin d → ℂ,
      (∀ j ∉ S, c j = 0) ∧ A.mulVec c = fun i => x i) :
    planeSupport K ≤ rotatedSupport A S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨F, x, hF, hx, rfl⟩
  exact rotatedSupport_packet A hA S hF (fun i j => x i j)
    (fun i => hcoords _ (hx i))

/-- Theorem 5D.1 for an arbitrary marked subspace of dimension at most two. -/
theorem nonnegative {d : ℕ} (K : Submodule ℂ (Ambient d))
    (hK : Module.finrank ℂ K ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2)
    (h₆ : HomogeneousSchur d 6 2) {z : Boundary d} (hz : z ∈ planeSupport K) :
    0 ≤ (quadratic (partialTranspose (markedMatrix d)) z).re := by
  obtain ⟨A, S, hA, hS, hcoords⟩ := exists_plane_coordinates K
  exact rotated_nonnegative A hA S (hS.trans_le hK) h₂ h₄ h₆
    (planeSupport_le_rotatedSupport K A hA S (fun x => (hcoords x).mp) hz)

/-- Any finite system of columns supported on one marked subspace of dimension
at most two yields a positive semidefinite compression of the partial transpose. -/
theorem compression_psd {d : ℕ} (K : Submodule ℂ (Ambient d))
    (hK : Module.finrank ℂ K ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2)
    (h₆ : HomogeneousSchur d 6 2)
    {J : Type*} [Fintype J] (B : Matrix (Index d) J ℂ)
    (hs : ∀ j, (fun i => B i j) ∈ planeSupport K) :
    (Bᴴ * partialTranspose (markedMatrix d) * B).PosSemidef := by
  obtain ⟨A, S, hA, hS, hcoords⟩ := exists_plane_coordinates K
  exact rotated_compression_psd A hA S (hS.trans_le hK) h₂ h₄ h₆ B
    (fun j => planeSupport_le_rotatedSupport K A hA S (fun x => (hcoords x).mp) (hs j))

end
end BlockPermanents.FourPlaneCompression
