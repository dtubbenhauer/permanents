import BlockPermanents.ThreePlaneTheorem
import BlockPermanents.ThreePlaneIntrinsicRange

/-! Testing the bare partial transpose on arbitrary families in the intrinsic
tensor product of the two ordinary packets and the dual marked packet. -/
namespace BlockPermanents.ThreePlane
open ThreeGeneralOpen Bend TensorCoordinates
open scoped Matrix ComplexOrder
noncomputable section

/-- A finite family is supported exactly when it lifts through the three
clasped boundary maps. The columns can be dependent. -/
theorem family_lifts_iff {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    {J : Type*} (B : Matrix (ThreeWords d k) J ℂ) :
    (∀ j, (fun i => B i j) ∈ intrinsicBoundary k S) ↔
      ∃ D, symmetricBoundary d k (power (Fin k) (basisMatrix S)) * D = B := by
  rw [← symmetricBoundary_range k S]
  constructor
  · intro h
    choose v hv using h
    refine ⟨fun i j => v j i, ?_⟩
    ext i j
    exact congrFun (hv j) i
  · rintro ⟨D,rfl⟩ j
    exact ⟨fun i => D i j, rfl⟩

/-- Evaluating on a supported family is a congruence of the five-term
decomposition. This applies also to the mixed entries between the columns. -/
theorem family_pullback {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    {J : Type*} (B : Matrix (ThreeWords d k) J ℂ)
    (hB : ∀ j, (fun i => B i j) ∈ intrinsicBoundary k S) :
    ∃ D : Matrix ((Word d k × Word d k) × (Fin k → Fin (Module.finrank ℂ S))) J ℂ,
      symmetricBoundary d k (power (Fin k) (basisMatrix S)) * D = B ∧
      Bᴴ * partialTranspose (original d k) * B = Dᴴ * compression S k * D := by
  obtain ⟨D,rfl⟩ := (family_lifts_iff S B).mp hB
  exact ⟨D, rfl, by simp only [compression, Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩

/-- Theorem 3D.2 on arbitrary columns from the intrinsic supported space. -/
theorem intrinsic_compression_psd {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 2 ≤ k) (hs : 0 < Module.finrank ℂ S) (hsk : Module.finrank ℂ S ≤ k)
    {J : Type*} [Fintype J] (B : Matrix (ThreeWords d k) J ℂ)
    (hB : ∀ j, (fun i => B i j) ∈ intrinsicBoundary k S) :
    (Bᴴ * partialTranspose (original d k) * B).PosSemidef := by
  obtain ⟨D, _, h⟩ := family_pullback S B hB
  rw [h]
  exact (subspace_compression_psd S hk hs hsk).conjTranspose_mul_mul_same D

/-- At fixed k the full-cap coefficient is smallest when the support has
dimension k. This is the lower bound stated below equation (3D.2). -/
theorem full_cap_weight_lower {k s : ℕ} (hs : 0 < s) (hsk : s ≤ k) :
    2*(k : ℝ) - 9/4 ≤ 2*(k : ℝ)^2/s - 9/4 := by
  apply sub_le_sub_right
  apply (le_div_iff₀ (by exact_mod_cast hs : 0 < (s : ℝ))).mpr
  have h : (s : ℝ) ≤ k := by exact_mod_cast hsk
  nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) k)]

/-- Both proper-cut weights in (3D.2) are positive throughout their
respective summation ranges. -/
theorem proper_weights_pos {k r : ℕ} (hr : r ≤ k) :
    0 < 2*(k.choose r : ℝ)^2 ∧
    0 < ((k+k).choose k : ℝ) * ((k+k).choose r : ℝ) * (k.choose r : ℝ) := by
  have h₁ : (0 : ℝ) < k.choose r := by exact_mod_cast Nat.choose_pos hr
  have h₂ : (0 : ℝ) < (k+k).choose r := by
    exact_mod_cast Nat.choose_pos (show r ≤ k+k by omega)
  have h₃ : (0 : ℝ) < (k+k).choose k := by
    exact_mod_cast Nat.choose_pos (show k ≤ k+k by omega)
  constructor <;> positivity

end
end BlockPermanents.ThreePlane
