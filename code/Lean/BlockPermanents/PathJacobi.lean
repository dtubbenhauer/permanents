import BlockPermanents.Threshold
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The Jacobi path determinant for Theorem 7C.1 -/
namespace BlockPermanents.PathJacobi
open Polynomial Matrix Threshold
noncomputable section

/-- The real symmetric path matrix, with edge weights 1 through m−1. -/
def J (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if i.val + 1 = j.val then j.val else if j.val + 1 = i.val then i.val else 0

theorem symmetric (m : ℕ) : (J m).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, J]
  split_ifs <;> first | rfl | omega

private def P (m : ℕ) := (J m).charmatrix

private theorem diag (m : ℕ) (i : Fin m) : P m i i = X := by
  simp [P, charmatrix_apply_eq, J]

private theorem castEntry (m : ℕ) (i j : Fin m) :
    P (m+1) i.castSucc j.castSucc = P m i j := by
  by_cases h : i = j
  · subst j; rw [diag, diag]
  · simp [P, charmatrix_apply_ne, h, J]

private theorem last_far (m : ℕ) (i : Fin m) :
    P (m+2) (Fin.last (m+1)) i.castSucc.castSucc = 0 := by
  have ne : Fin.last (m+1) ≠ i.castSucc.castSucc :=
    fun h => by have he := congrArg Fin.val h; simp at he; omega
  rw [P, charmatrix_apply_ne _ _ _ ne]
  simp [J, show ¬ m + 1 + 1 = i.val by omega, show ¬ i.val + 1 = m + 1 by omega, show i.val ≠ m by omega]

private theorem far_last (m : ℕ) (i : Fin m) :
    P (m+2) i.castSucc.castSucc (Fin.last (m+1)) = 0 := by
  have ne : i.castSucc.castSucc ≠ Fin.last (m+1) :=
    fun h => by have he := congrArg Fin.val h; simp at he; omega
  rw [P, charmatrix_apply_ne _ _ _ ne]
  simp [J, show ¬ m + 1 + 1 = i.val by omega, show ¬ i.val + 1 = m+1 by omega, show i.val ≠ m by omega]

private theorem last_prev (m : ℕ) :
    P (m+2) (Fin.last (m+1)) (Fin.last m).castSucc = -C (m+1 : ℝ) := by
  rw [P, charmatrix_apply_ne _ _ _ (Ne.symm (Fin.castSucc_ne_last _))]
  simp [J, show ¬ m+1+1=m by omega]

private theorem prev_last (m : ℕ) :
    P (m+2) (Fin.last m).castSucc (Fin.last (m+1)) = -C (m+1 : ℝ) := by
  rw [P, charmatrix_apply_ne _ _ _ (Fin.castSucc_ne_last _)]
  simp [J]

private theorem even_sign (n : ℕ) : (-1 : ℝ[X])^(n+n) = 1 := by
  rw [show n+n=2*n by omega, pow_mul]
  norm_num

private theorem odd_sign (n : ℕ) : (-1 : ℝ[X])^(n+1+n) = -1 := by
  rw [show n+1+n=(n+n)+1 by omega, pow_succ, even_sign, one_mul]

private def skip (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ[X] :=
  (P (n+2)).submatrix Fin.castSucc (Fin.last n).castSucc.succAbove

private theorem det_skip (n : ℕ) : (skip n).det = -C (n+1 : ℝ) * (P n).det := by
  rw [det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc]
  have hz (i : Fin n) : skip n i.castSucc (Fin.last n) = 0 := by
    simpa [skip] using far_last n i
  have ha : skip n (Fin.last n) (Fin.last n) = -C (n+1 : ℝ) := by
    simpa [skip] using prev_last n
  have hm : (skip n).submatrix Fin.castSucc Fin.castSucc = P n := by
    ext i j : 1
    simp only [submatrix_apply, skip, Fin.castSucc_succAbove_castSucc, Fin.succAbove_last]
    rw [castEntry, castEntry]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, ha, Fin.val_last,
    even_sign, one_mul, Fin.succAbove_last, hm]

theorem charpoly_zero : (J 0).charpoly = 1 := by
  change (P 0).det = 1
  exact Matrix.det_isEmpty

theorem charpoly_one : (J 1).charpoly = X := by
  change (P 1).det = X
  rw [Matrix.det_fin_one, diag]

/-- Expanding the endpoint row of the characteristic matrix deletes either the
last vertex or the final edge. The edge term carries its squared weight. -/
theorem charpoly_step (n : ℕ) :
    (J (n+2)).charpoly = X * (J (n+1)).charpoly -
      C ((n+1 : ℝ)^2) * (J n).charpoly := by
  change (P (n+2)).det = X * (P (n+1)).det - C _ * (P n).det
  rw [det_succ_row _ (Fin.last (n+1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hm : (P (n+2)).submatrix Fin.castSucc Fin.castSucc = P (n+1) := by
    ext i j : 1
    exact castEntry _ _ _
  have hskip := det_skip n
  unfold skip at hskip
  simp only [last_far, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.coe_castSucc, Fin.val_last, last_prev, odd_sign, even_sign, diag, one_mul,
    Fin.succAbove_last, hm, hskip, map_pow]
  ring

end
end BlockPermanents.PathJacobi
