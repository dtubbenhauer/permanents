import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
namespace BlockPermanents.FiveCycles
abbrev S := Equiv.Perm (Fin 5)
noncomputable section
def avg (f : S → ℝ) : ℝ := (∑ σ, f σ) / 120

theorem avg_relabel (τ : S) (f : S → ℝ) : avg (fun σ => f (σ*τ)) = avg f := by
  unfold avg
  rw [show (∑ σ, f (σ*τ)) = ∑ σ, f σ from Equiv.sum_comp (Equiv.mulRight τ) f]

theorem avg_add (f h : S → ℝ) : avg (fun σ => f σ + h σ) = avg f + avg h := by
  simp [avg, Finset.sum_add_distrib, add_div]

theorem avg_mul_left (a : ℝ) (f : S → ℝ) : avg (fun σ => a*f σ) = a * avg f := by
  simp [avg, ← Finset.mul_sum, mul_div_assoc]

theorem avg_const (a : ℝ) : avg (fun _ => a) = a := by
  simp [avg, Fintype.card_perm, Nat.factorial, nsmul_eq_mul]

theorem avg_mono {f h : S → ℝ} (hfh : ∀ σ, f σ ≤ h σ) : avg f ≤ avg h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => hfh σ) (by norm_num)

/-- An average of finite sums can be taken term by term. -/
theorem avg_sum {I : Type*} [Fintype I] (f : I → S → ℝ) :
    avg (fun σ => ∑ i, f i σ) = ∑ i, avg (f i) := by
  simp only [avg, ← Finset.sum_div]
  rw [Finset.sum_comm]


end
end BlockPermanents.FiveCycles
