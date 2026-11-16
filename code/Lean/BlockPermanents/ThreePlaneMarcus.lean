import BlockPermanents.ThreePlaneRestriction
import BlockPermanents.ThreeSupportedMarcus

/-! Averaging the intrinsic supported decompositions back to three block permanents. -/
namespace BlockPermanents.ThreePlane
open Bend Closures ThreeGeneralOpen ThreeMarkedAverage
open scoped Matrix ComplexOrder BigOperators
noncomputable section

private theorem supported_expectation {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hk : 2 ≤ k) (hs : 0 < Module.finrank ℂ S) (hsk : Module.finrank ℂ S ≤ k)
    {z : ThreeWords d k → ℂ} (hz : z ∈ intrinsicBoundary k S) :
    0 ≤ (quadratic (partialTranspose (original d k)) z).re := by
  let B : Matrix (ThreeWords d k) Unit ℂ := fun i _ => z i
  let v : Unit → ℂ := fun _ => 1
  have hv : B.mulVec v = z := by ext i; simp [B, v, Matrix.mulVec, dotProduct]
  have hp := (intrinsic_compression_psd S hk hs hsk B (fun _ => hz)).re_dotProduct_nonneg v
  rw [Bridges.quadratic_bracket]
  change 0 ≤ (dotProduct (star z) ((partialTranspose (original d k)).mulVec z)).re
  rw [← hv]
  simpa only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul] using hp

/-- For the current mark, take the subspace spanned by its k atom vectors. -/
theorem packet_expectation {d k : ℕ} (hk : 2 ≤ k) (x : Fin 3 → Fin k → Fin d → ℂ) :
    0 ≤ (quadratic (original d k) (data x)).re := by
  classical
  let atoms (i : Fin k) : FourPlaneBasis.Ambient d := (WithLp.equiv 2 _).symm (x 2 i)
  let S := Submodule.span ℂ (Set.range atoms)
  have hS (i : Fin k) : atoms i ∈ S := Submodule.subset_span ⟨i,rfl⟩
  rw [productData]
  by_cases hpos : 0 < Module.finrank ℂ S
  · have hcard : Module.finrank ℂ S ≤ k := by
      simpa only [Fintype.card_fin] using finrank_range_le_card (R := ℂ) atoms
    rw [evaluate_bend]
    apply supported_expectation S hk hpos hcard
    apply Submodule.subset_span
    refine ⟨_, Submodule.subset_span ⟨_,_, Bridges.packet_symmetric _ _ _, Bridges.packet_symmetric _ _ _, rfl⟩,
      _, Submodule.subset_span ⟨fun i => ⟨atoms i, hS i⟩, rfl⟩, rfl⟩
  · have hbot : S = ⊥ := by
      by_contra h
      exact hpos (Submodule.one_le_finrank_iff.mpr h)
    have h0 (i : Fin k) (j : Fin d) : x 2 i j = 0 := by
      have h := hS i
      rw [hbot, Submodule.mem_bot] at h
      exact congrArg (fun y : FourPlaneBasis.Ambient d => y j) h
    have hp (w : Word d k) : packet (x 2) w = 0 :=
      packet_supported ∅ (x 2) (fun i j _ => h0 i j) w ⟨⟨0, by omega⟩, by simp⟩
    simp [quadratic, product, hp]

/-- The matrix consequence of Theorem 3D.2, using its intrinsic compression
inside the common Gram space independently for each of the packet orders. -/
theorem marcus_three {k : ℕ} (hk : 1 ≤ k) : MarcusAt 3 k := by
  by_cases h : k = 1
  · subst k; exact thickness_one 3
  apply MatchingThreshold.marcusAt_of_gram
  intro x
  have hm := gap_of_marked x (fun p => packet_expectation (by omega) (x ∘ p))
    (fun y => ThreeGram.target_gap y)
  change 0 ≤ (_ - _ : ℂ).re at hm
  exact sub_nonneg.mp (by simpa only [Complex.sub_re] using hm)

end
end BlockPermanents.ThreePlane
