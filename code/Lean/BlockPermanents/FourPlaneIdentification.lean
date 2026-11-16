import BlockPermanents.FourPlaneCompression
import BlockPermanents.FourPlaneSpan

/-! # Identification of the intrinsic and rotated marked support spaces -/
namespace BlockPermanents.FourPlaneCompression
open FourPlaneBasis FourCovariance FourCompression FourSupportedTensor FourRoutes
open FourCapOrbit FourFullValues Closures Bend TensorCoordinates
open scoped Matrix
noncomputable section

/-- In adapted unitary coordinates, the intrinsic marked support is exactly the
rotation of the full coordinate-supported tensor space, in every dimension. -/
theorem planeSupport_eq_rotatedSupport {d : ℕ} (K : Submodule ℂ (Ambient d))
    (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) (hA : Aᴴ * A = 1)
    (hx : ∀ x : Ambient d, x ∈ K ↔ ∃ c : Fin d → ℂ,
      (∀ j ∉ S, c j = 0) ∧ A.mulVec c = fun i => x i) :
    planeSupport K = rotatedSupport A S := by
  classical
  apply le_antisymm
  · exact planeSupport_le_rotatedSupport K A hA S (fun x => (hx x).mp)
  rw [rotatedSupport_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨G,H,hG,hH,hS,rfl⟩
  let F := (ordinaryChange A).mulVec G
  have hF : Inner F := ordinaryChange_inner A hG
  let P := power (Fin 2) A
  change product F (dual (P.mulVec H)) ∈ planeSupport K
  have hspan := supported_mem_packet_span S hH hS
  clear hH hS
  induction hspan using Submodule.span_induction with
  | mem H h =>
    obtain ⟨w, hw, rfl⟩ := h
    let c (i : Fin 2) (j : Fin d) : ℂ := if j = w i then 1 else 0
    let x (i : Fin 2) : Ambient d := (WithLp.equiv 2 _).symm (A.mulVec (c i))
    have hxK (i : Fin 2) : x i ∈ K := by
      apply (hx _).mpr
      refine ⟨c i, ?_, rfl⟩
      intro j hj
      exact if_neg (fun h : j = w i => hj (h.symm ▸ hw i))
    change product F (dual ((power (Fin 2) A).mulVec (packet c))) ∈ planeSupport K
    rw [power_packet]
    exact Submodule.subset_span ⟨F, x, hF, hxK, rfl⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    convert (planeSupport K).zero_mem using 1
    ext a
    simp [product, dual]
  | add u v _ _ hu hv =>
    rw [Matrix.mulVec_add, dual_add]
    convert (planeSupport K).add_mem hu hv using 1
    ext a
    exact mul_add _ _ _
  | smul a u _ hu =>
    rw [Matrix.mulVec_smul, dual_smul]
    convert (planeSupport K).smul_mem (star a) hu using 1
    ext b
    exact mul_left_comm _ _ _

end
end BlockPermanents.FourPlaneCompression
