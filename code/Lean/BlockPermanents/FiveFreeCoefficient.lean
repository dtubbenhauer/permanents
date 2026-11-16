import BlockPermanents.FiveNumbers
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-! The contribution of all positive cuts in the free-cable test of Lemma 8A.5. -/
namespace BlockPermanents.FiveFreeCoefficient
open Finset
noncomputable section

/-- Each positive r-cut supplies choose(2k,r) copies of the full cap. -/
def coefficient (k : ℕ) : ℝ :=
  (∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ)) / ((k+k).choose k : ℝ)

private theorem central_pos (k : ℕ) : 0 < ((k+k).choose k : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : k ≤ k+k)

theorem coefficient_mul (k : ℕ) :
    coefficient k * ((k+k).choose k : ℝ) = ∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ) :=
  div_mul_cancel₀ _ (central_pos k).ne'

private theorem half_row (k : ℕ) :
    2 * (∑ i : Fin k, (k+k).choose (i.val+1)) + 2 = 4^k + (k+k).choose k := by
  have total := Nat.sum_range_choose_halfway k
  rw [two_mul, sum_range_succ'] at total
  simp only [Nat.choose_succ_succ, Nat.choose_zero_right, sum_add_distrib] at total
  have central := sum_range_succ (fun i => (k+k).choose i) k
  rw [sum_range_succ'] at central
  rw [Fin.sum_univ_eq_sum_range (fun i => (k+k).choose (i+1))]
  simp only [Nat.choose_zero_right] at central
  simp only [Nat.succ_eq_add_one] at total
  linarith only [total, central]

/-- Reflect the noncentral entries of the even Pascal row. -/
theorem closed_form (k : ℕ) :
    coefficient k = 1/2 + ((4:ℝ)^k/2 - 1) / ((k+k).choose k : ℝ) := by
  have h : 2 * (∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ)) + 2 =
      (4:ℝ)^k + ((k+k).choose k : ℝ) := by exact_mod_cast half_row k
  unfold coefficient
  field_simp [(central_pos k).ne']
  linear_combination ((k+k).choose k : ℝ) * h

private theorem central_recurrence (k : ℕ) :
    ((k:ℝ)+1) * (Nat.centralBinom (k+1) : ℝ) = 2 * (2*(k:ℝ)+1) * (Nat.centralBinom k : ℝ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

/-- The ratio of the whole Pascal row to its central entry grows by this factor. -/
theorem row_ratio (k : ℕ) :
    (4:ℝ)^(k+1) / (Nat.centralBinom (k+1) : ℝ) =
      (2*((k:ℝ)+1)/(2*(k:ℝ)+1)) * (4^k / (Nat.centralBinom k : ℝ)) := by
  have c : (0:ℝ) < Nat.centralBinom k := by exact_mod_cast Nat.centralBinom_pos k
  have c' : (0:ℝ) < Nat.centralBinom (k+1) := by exact_mod_cast Nat.centralBinom_pos (k+1)
  rw [pow_succ]
  field_simp [c.ne', c'.ne', show 2*(k:ℝ)+1 ≠ 0 by positivity]
  linear_combination -2*(4:ℝ)^k * central_recurrence k

theorem strictMono_coefficient : StrictMono coefficient := by
  apply strictMono_nat_of_lt_succ
  intro k
  have c : (0:ℝ) < Nat.centralBinom k := by exact_mod_cast Nat.centralBinom_pos k
  have c' : (0:ℝ) < Nat.centralBinom (k+1) := by exact_mod_cast Nat.centralBinom_pos (k+1)
  have inc : (Nat.centralBinom k : ℝ) ≤ Nat.centralBinom (k+1) := by
    apply le_of_mul_le_mul_left (a := (k:ℝ)+1) _ (by positivity)
    rw [central_recurrence]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) c.le]
  have ratio : (4:ℝ)^k / (Nat.centralBinom k : ℝ) < 4^(k+1) / (Nat.centralBinom (k+1) : ℝ) := by
    rw [row_ratio]
    have factor : (1:ℝ) < 2*((k:ℝ)+1)/(2*(k:ℝ)+1) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    simpa only [one_mul] using mul_lt_mul_of_pos_right factor (show 0 < (4:ℝ)^k / (Nat.centralBinom k : ℝ) by positivity)
  have inv := one_div_le_one_div_of_le c inc
  have expansion (n : ℕ) : coefficient n = 1/2 + (4^n / (Nat.centralBinom n : ℝ))/2 - 1 / (Nat.centralBinom n : ℝ) := by
    rw [closed_form, ← two_mul, ← Nat.centralBinom_eq_two_mul_choose]
    ring
  rw [expansion, expansion]
  linarith

theorem cubic : coefficient 3 = 41/20 := by
  norm_num [closed_form, Nat.choose]

theorem uniform {k : ℕ} (hk : 3 ≤ k) : 41/20 ≤ coefficient k :=
  cubic ▸ strictMono_coefficient.monotone hk

theorem uniform_eq_iff {k : ℕ} : coefficient k = 41/20 ↔ k = 3 := by
  rw [← cubic, strictMono_coefficient.injective.eq_iff]

end
end BlockPermanents.FiveFreeCoefficient
