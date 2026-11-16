import BlockPermanents.SupportCoordinates

/-! # A square unitary adapted to an arbitrary marked subspace -/

namespace BlockPermanents.FourPlaneBasis
open scoped Matrix ComplexConjugate InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 300000

abbrev Ambient (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The adapted coordinates have exactly as many selected axes as the dimension of
the given subspace. In these coordinates membership is equivalent to support on
those axes, including for the zero subspace and the full space. -/
theorem exists_plane_coordinates {d : ℕ} (K : Submodule ℂ (Ambient d)) :
    ∃ (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)),
      Aᴴ * A = 1 ∧ S.card = Module.finrank ℂ K ∧
      ∀ x : Ambient d, x ∈ K ↔ ∃ c : Fin d → ℂ,
        (∀ j ∉ S, c j = 0) ∧ A.mulVec c = fun i => x i := by
  classical
  let b := stdOrthonormalBasis ℂ K
  let q := stdOrthonormalBasis ℂ Kᗮ
  let e : (Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ)) ≃ Fin d := Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    simpa only [finrank_euclideanSpace_fin] using K.finrank_add_finrank_orthogonal)
  let v : (Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ)) → Ambient d := Sum.elim (fun i => (b i : Ambient d)) (fun j => (q j : Ambient d))
  have hv : ∀ i j : Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ), ⟪v i, v j⟫_ℂ = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Sum.inl.injEq]
        exact (orthonormal_iff_ite.mp b.orthonormal i j)
      | inr j =>
        rw [if_neg Sum.inl_ne_inr]
        exact (Submodule.inner_right_of_mem_orthogonal (b i).property (q j).property)
    | inr i =>
      cases j with
      | inl j =>
        rw [if_neg Sum.inr_ne_inl]
        exact (Submodule.inner_left_of_mem_orthogonal (b j).property (q i).property)
      | inr j =>
        simp only [Sum.inr.injEq]
        exact (orthonormal_iff_ite.mp q.orthonormal i j)
  let A : Matrix (Fin d) (Fin d) ℂ := fun i j => v (e.symm j) i
  let emb : Fin (Module.finrank ℂ K) ↪ Fin d := ⟨fun j => e (.inl j),
    e.injective.comp Sum.inl_injective⟩
  let S := Finset.univ.map emb
  have eval (c : Fin d → ℂ) (i : Fin d) :
      (∑ j, c j • v (e.symm j)) i = A.mulVec c i := by
    change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin d => ℂ) i) (∑ j, c j • v (e.symm j)) = A.mulVec c i
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨A, S, ?_, by simp [S], ?_⟩
  · apply Matrix.ext
    intro i j
    calc
      (Aᴴ * A) i j = ⟪v (e.symm i), v (e.symm j)⟫_ℂ := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply, RCLike.inner_apply]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
        simp [hv, Matrix.one_apply]
  · intro x
    constructor
    · intro hx
      let y : K := ⟨x, hx⟩
      let g : (Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ)) → ℂ := Sum.elim (fun i => b.repr y i) (fun _ => 0)
      let c : Fin d → ℂ := g ∘ e.symm
      refine ⟨c, ?_, ?_⟩
      · intro j hj
        obtain ⟨t, rfl⟩ := e.surjective j
        cases t with
        | inl k => exact (hj (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩)).elim
        | inr k => simp [c, g]
      · have h : ∑ j, c j • v (e.symm j) = x := by
          rw [← e.sum_comp (fun j => c j • v (e.symm j))]
          simp only [c, Function.comp_apply, Equiv.symm_apply_apply, g, v,
            Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero,
            add_zero]
          simpa only [map_sum, map_smul] using congrArg (K.subtype) (b.sum_repr y)
        funext i
        rw [← eval, h]
    · rintro ⟨c, hc, hcx⟩
      have h : x = ∑ j, c j • v (e.symm j) := by
        apply PiLp.ext
        intro i
        rw [eval, hcx]
      rw [h]
      apply K.sum_mem
      intro j _
      obtain ⟨t, rfl⟩ := e.surjective j
      cases t with
      | inl i => simpa [v] using K.smul_mem (c (e (.inl i))) (b i).property
      | inr i =>
        have hj : e (.inr i) ∉ S := by
          rintro hj
          obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hj
          exact Sum.noConfusion (e.injective (show e (.inl k) = e (.inr i) from hk))
        simp [hc _ hj]

end
end BlockPermanents.FourPlaneBasis
