import BlockPermanents.FourPlaneTensor

/-! # Coordinate generators for the full supported symmetric square -/
namespace BlockPermanents.FourCovariance
open Closures Bend FourFullValues
open scoped BigOperators Matrix
noncomputable section

/-- A symmetric marked tensor supported on a coordinate set is a linear
combination of normalized two-letter packets of axes in that set. -/
theorem supported_mem_packet_span {d : ℕ} (S : Finset (Fin d)) {H : Word d 2 → ℂ}
    (h : Symmetric H) (hs : Supported S H) :
    H ∈ Submodule.span ℂ {z | ∃ w : Word d 2, (∀ i, w i ∈ S) ∧
      packet (fun i j => if j = w i then (1 : ℂ) else 0) = z} := by
  classical
  let e (w : Word d 2) (i : Fin 2) (j : Fin d) := if j = w i then (1 : ℂ) else 0
  have basis (w v : Word d 2) : pureWord (e w) v = if v = w then 1 else 0 := by
    simp only [pureWord, e, Fintype.prod_boole, funext_iff]
    split_ifs <;> simp_all
  have expand : H = ∑ w, H w • pureWord (e w) := by
    funext v
    simp [Finset.sum_apply, basis, mul_ite]
  have hc (w : Word d 2) :
      (symClasp d 2).mulVec (pureWord (e w)) =
        ((2 : ℂ)⁻¹ * (packetScale (Fin 2))⁻¹) • packet (e w) := by
    rw [Bridges.symClasp_action]
    have hn : packetScale (Fin 2) ≠ 0 := by
      simp [packetScale, Real.sqrt_ne_zero', Nat.factorial]
    funext v
    simp only [clasp, sumSlots_pure, packet, Pi.smul_apply, smul_eq_mul]
    norm_num [← mul_assoc, hn, Nat.factorial]
  have support (w : Word d 2) (hw : H w ≠ 0) : ∀ i, w i ∈ S := by
    intro i
    by_contra hi
    apply hw
    rw [Bend.Symmetric, Bridges.symClasp_action] at h
    let s := Equiv.swap i (0 : Fin 2)
    have eq : w ∘ s.symm = ![w i, w (s.symm 1)] := by
      funext t
      fin_cases t <;> simp [s]
    have heq := clasp_invariant H s w
    rw [h,eq] at heq
    exact heq.symm.trans (hs _ hi _)
  change (symClasp d 2).mulVec H = H at h
  rw [← h]
  convert_to (symClasp d 2).mulVecLin H ∈ _
  rw [expand, map_sum]
  apply Submodule.sum_mem
  intro w _
  rw [map_smul, Matrix.mulVecLin_apply, hc]
  by_cases hw : H w = 0
  · simp [hw]
  · apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨w, support w hw, rfl⟩

end
end BlockPermanents.FourCovariance
