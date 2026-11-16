import BlockPermanents.OccupationSeam
import BlockPermanents.RoutedSector

/-! The normalized occupation columns of the routed symmetric output cable. -/
namespace BlockPermanents.RoutedOccupationFrame
open Bend OccupationBasis OccupationSeam
open scoped Matrix
noncomputable section

abbrev Index (d N : ℕ) := Class (Fin N) (Fin d)

private def coeff {d N : ℕ} (n : Index d N) : ℂ :=
  (Real.sqrt (weight n.val N : ℝ) : ℂ)

/-- One unit column per realized occupation, in the ordinary word basis. -/
def B (d N : ℕ) : Matrix (Word d N) (Index d N) ℂ :=
  fun w n => if classify w = n then coeff n else 0

private theorem coeff_real {d N : ℕ} (n : Index d N) : star (coeff n) = coeff n := by
  simp [coeff]

private theorem coeff_sq {d N : ℕ} (n : Index d N) : coeff n * coeff n = (weight n.val N : ℂ) := by
  have h : 0 ≤ (weight n.val N : ℝ) := by exact_mod_cast (weight_pos n.val N).le
  simp only [coeff, ← Complex.ofReal_mul, Real.mul_self_sqrt h, Complex.ofReal_ratCast]

open private multiplicity from BlockPermanents.OccupationSeam in
theorem orthonormal (d N : ℕ) : (B d N)ᴴ * B d N = 1 := by
  classical
  ext n t
  by_cases h : n = t
  · subst t
    have hc := congrArg (fun z : ℚ => (z : ℂ)) (multiplicity n)
    simp only [Rat.cast_sum, apply_ite, Rat.cast_one, Rat.cast_zero, Rat.cast_inv, Fintype.card_fin] at hc
    have hz : (weight n.val N : ℂ) ≠ 0 := by exact_mod_cast (weight_pos n.val N).ne'
    have elem (w : Word d N) :
        star (B d N w n) * B d N w n =
          (if classify w = n then (1 : ℂ) else 0) * (weight n.val N : ℂ) := by
      by_cases hw : classify w = n <;> simp [B, hw, coeff_real, coeff_sq]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, elem, ← Finset.sum_mul,
      hc, inv_mul_cancel₀ hz, Matrix.one_apply_eq]
  · have elem (w : Word d N) : star (B d N w n) * B d N w t = 0 := by
      by_cases hw : classify w = n <;> simp [B, hw, h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, elem, Finset.sum_const_zero, Matrix.one_apply_ne h]

/-- The occupation columns span the entire symmetric output, including empty sectors. -/
theorem complete (d N : ℕ) : B d N * (B d N)ᴴ = symClasp d N := by
  classical
  ext v w
  have h (n : Index d N) : B d N v n * star (B d N w n) =
      if classify v = n then (if classify w = classify v then (weight (occ v) N : ℂ) else 0) else 0 := by
    by_cases hv : classify v = n
    · subst n
      by_cases hw : classify w = classify v
      · simp only [B, if_pos rfl, if_true, if_pos hw, coeff_real, coeff_sq]; rfl
      · simp only [B, if_pos rfl, if_true, if_neg hw, star_zero, mul_zero]
    · simp [B, hv]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← kernel_word, kernel_eq]
  have hc : classify w = classify v ↔ occ v = occ w := Subtype.ext_iff.trans eq_comm
  by_cases he : occ v = occ w <;> simp [hc, he]

theorem symmetric {d N : ℕ} (n : Index d N) : Symmetric (fun w => B d N w n) := by
  have h : symClasp d N * B d N = B d N := by rw [← complete, Matrix.mul_assoc, orthonormal, Matrix.mul_one]
  funext w
  exact congrArg (fun A : Matrix (Word d N) (Index d N) ℂ => A w n) h

/-- Total occupancy in the marked alphabet. -/
def sector {d N : ℕ} (S : Finset (Fin d)) (n : Index d N) := ∑ j ∈ S, n.val j

theorem sector_eq {d N : ℕ} (S : Finset (Fin d)) {w : Word d N} {n : Index d N}
    (hn : B d N w n ≠ 0) : (RoutedTrace.occupied S w).card = sector S n := by
  have h : classify w = n := by by_contra he; exact hn (by simp [B, he])
  subst n
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ S w).symm

end
end BlockPermanents.RoutedOccupationFrame
