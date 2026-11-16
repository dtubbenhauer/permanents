import BlockPermanents.FourPlaneBasis

/-! Orthonormal coordinate columns for the actual marked subspace. -/
namespace BlockPermanents.ThreePlane
open scoped Matrix InnerProductSpace
noncomputable section

/-- The orthonormal basis of the marked subspace, as columns in ambient coordinates. -/
def basisMatrix {d : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ :=
  fun i j => (stdOrthonormalBasis ℂ S j).val i

theorem basis_isometry {d : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    (basisMatrix S)ᴴ * basisMatrix S = 1 := by
  let b := stdOrthonormalBasis ℂ S
  ext i j
  calc
    _ = ⟪b i, b j⟫_ℂ := by
      rw [Submodule.coe_inner]
      simp only [basisMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        PiLp.inner_apply, RCLike.inner_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by rw [orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]

/-- A marked vector has coordinates in these columns exactly when it is in S. -/
theorem basis_range {d : ℕ} (S : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (x : EuclideanSpace ℂ (Fin d)) :
    x ∈ S ↔ ∃ c, (basisMatrix S).mulVec c = fun i => x i := by
  let b := stdOrthonormalBasis ℂ S
  have eval (c : Fin (Module.finrank ℂ S) → ℂ) (i : Fin d) :
      (∑ j, c j • (b j).val) i = (basisMatrix S).mulVec c i := by
    change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) i) (∑ j, c j • (b j).val) = _
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  constructor
  · intro hx
    let y : S := ⟨x,hx⟩
    refine ⟨fun j => b.repr y j, ?_⟩
    have h : ∑ j, b.repr y j • (b j).val = x := by
      simpa only [map_sum, map_smul] using congrArg S.subtype (b.sum_repr y)
    funext i
    rw [← eval, h]
  · rintro ⟨c,hc⟩
    have h : ∑ j, c j • (b j).val = x := by
      apply PiLp.ext
      intro i
      rw [eval, hc]
    rw [← h]
    exact S.sum_mem fun j _ => S.smul_mem _ (b j).property

end
end BlockPermanents.ThreePlane
