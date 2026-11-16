import BlockPermanents.ThreePlaneBasis
import BlockPermanents.FourPlaneTensor

/-! The range of the marked boundary is the intrinsic symmetric power of S. -/
namespace BlockPermanents.ThreePlane
open Bend Closures TensorCoordinates
open scoped Matrix
noncomputable section

/-- Span of all normalized packets whose k atom vectors lie in S. -/
def symmetricPower {d : ℕ} (k : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    Submodule ℂ (Word d k → ℂ) :=
  Submodule.span ℂ {v | ∃ x : Fin k → S, packet (fun i j => (x i).val j) = v}

private theorem clasp_pure {s k : ℕ} (x : Fin k → Fin s → ℂ) :
    (symClasp s k).mulVec (pureWord x) =
      ((k.factorial : ℂ)⁻¹ * (packetScale (Fin k))⁻¹) • packet x := by
  have hn : packetScale (Fin k) ≠ 0 := by
    simp [packetScale, Real.sqrt_ne_zero', Nat.factorial_ne_zero]
  rw [Bridges.symClasp_action]
  funext w
  simp only [clasp, sumSlots_pure, Fintype.card_fin, packet, Pi.smul_apply, smul_eq_mul]
  rw [mul_assoc, ← mul_assoc (packetScale (Fin k))⁻¹, inv_mul_cancel₀ hn, one_mul]

/-- In any thickness and rank, the symmetrized basis columns span precisely
the packets on the marked subspace, including their arbitrary linear combinations. -/
theorem symmetricPower_range {d : ℕ} (k : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    LinearMap.range
        (power (Fin k) (basisMatrix S) * symClasp (Module.finrank ℂ S) k).mulVecLin =
      symmetricPower k S := by
  classical
  let s := Module.finrank ℂ S
  let E := basisMatrix S
  let T := power (Fin k) E * symClasp s k
  change LinearMap.range T.mulVecLin = _
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    let e (w : Word s k) (i : Fin k) (j : Fin s) := if j = w i then (1 : ℂ) else 0
    have basis (w v : Word s k) : pureWord (e w) v = if v = w then 1 else 0 := by
      simp only [pureWord, e, Fintype.prod_boole, funext_iff]
      split_ifs <;> simp_all
    have expand : z = ∑ w, z w • pureWord (e w) := by
      funext v
      simp [Finset.sum_apply, basis, mul_ite]
    have axis (w : Word s k) (i : Fin k) :
        E.mulVec (e w i) = fun j => (stdOrthonormalBasis ℂ S (w i)).val j := by
      funext j
      simp [E, e, Matrix.mulVec, dotProduct, mul_ite, basisMatrix]
    rw [expand, map_sum]
    apply Submodule.sum_mem
    intro w _
    rw [map_smul, Matrix.mulVecLin_apply]
    apply Submodule.smul_mem
    dsimp only [T]
    rw [← Matrix.mulVec_mulVec, clasp_pure, Matrix.mulVec_smul, FourCovariance.power_packet]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨fun i => stdOrthonormalBasis ℂ S (w i),
      congrArg packet (funext (fun i => (axis w i).symm))⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    choose c hc using fun i => (basis_range S (x i).val).mp (x i).property
    refine ⟨packet c, ?_⟩
    change (power (Fin k) E * symClasp s k).mulVec (packet c) = _
    rw [← Matrix.mulVec_mulVec, (Bridges.packet_symmetric s k c : (symClasp s k).mulVec _ = _),
      FourCovariance.power_packet]
    exact congrArg packet (funext hc)

end
end BlockPermanents.ThreePlane
