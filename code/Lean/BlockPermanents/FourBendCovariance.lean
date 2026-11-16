import BlockPermanents.FourCompression
import BlockPermanents.FourTransferNaturality
import BlockPermanents.BendCoordinates

/-! # Unitary covariance of the bent four-packet transfer -/
namespace BlockPermanents.FourCovariance
open FourTarget FourUpright FourRoutes FourCompression TensorCoordinates BendCoordinates
open scoped BigOperators Matrix
noncomputable section
attribute [local irreducible] FourTarget.Q

/-- Six ordinary slots, grouped into three packets of two. -/
def ordinaryChange {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Triple e 2) (Triple d 2) ℂ :=
  fun x y => ∏ i, ∏ j, A (x i j) (y i j)

private def unbentChange {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Index e) (Index d) ℂ :=
  tensor (ordinaryChange A) (power (Fin 2) A)

/-- The marked packet is dual, so both of its slots transform by conjugate entries. -/
def bentChange {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Index e) (Index d) ℂ :=
  tensor (ordinaryChange A) (conjugate (power (Fin 2) A))

theorem bentChange_apply {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) (x : Index e) (y : Index d) :
    bentChange A x y = (∏ i, ∏ j, A (x.1 i j) (y.1 i j)) *
      star (∏ j, A (x.2 j) (y.2 j)) := rfl

private theorem unbent_reindex {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) :
    unbentChange A = (power (Slot 2) A).submatrix (layout e).symm (layout d).symm := by
  ext x y
  obtain ⟨x,rfl⟩ := (layout e).surjective x
  obtain ⟨y,rfl⟩ := (layout d).surjective y
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  let f := fun i : Slot 2 => A (x i) (y i)
  let p := last.trans (wires 2 ori)
  change _ = ∏ t, f t
  rw [← Equiv.prod_comp p f, Fintype.prod_sum_type]
  rw [Fintype.prod_prod_type]
  rfl

private theorem marked_reindex (d : ℕ) :
    markedMatrix d = (LinearMap.toMatrix' (Q d 2)).submatrix (layout d).symm (layout d).symm := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [marked_action, Matrix.submatrix_mulVec_equiv, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

private theorem unbent_isometry {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) (hA : Aᴴ * A = 1) :
    (unbentChange A)ᴴ * unbentChange A = 1 := by
  rw [unbent_reindex, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← power_star, ← power_mul, hA, power_one, Matrix.submatrix_one_equiv]

private theorem marked_natural {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ) :
    markedMatrix e * unbentChange A = unbentChange A * markedMatrix d := by
  have eval {n : ℕ} (x : (Slot 2 → Fin n) → ℂ) :
      (LinearMap.toMatrix' (Q n 2)).mulVec x = Q n 2 x := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h : LinearMap.toMatrix' (Q e 2) * power (Slot 2) A =
      power (Slot 2) A * LinearMap.toMatrix' (Q d 2) := by
    apply Matrix.ext_of_mulVec_single
    intro i
    simp only [← Matrix.mulVec_mulVec, eval, transfer_natural]
  rw [marked_reindex, marked_reindex, unbent_reindex, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, h]

/-- Pulling the bent transfer back along an ambient isometry preserves its entire matrix. -/
theorem bent_covariance {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    (hA : Aᴴ * A = 1) :
    (bentChange A)ᴴ * Bend.partialTranspose (markedMatrix e) * bentChange A =
      Bend.partialTranspose (markedMatrix d) := by
  unfold bentChange
  rw [← partial_congr]
  change Bend.partialTranspose ((unbentChange A)ᴴ * markedMatrix e * unbentChange A) = _
  rw [Matrix.mul_assoc, marked_natural A, ← Matrix.mul_assoc, unbent_isometry A hA,
    Matrix.one_mul]

end
end BlockPermanents.FourCovariance
