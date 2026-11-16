import BlockPermanents.Threshold
import Mathlib.Tactic.Positivity

/-! # The coefficient of the free-cable test

The three highest positive cuts alone give the stated uniform coefficient.
At k=3 they are all positive cuts and give equality. -/
namespace BlockPermanents.FiveNumbers
open scoped BigOperators

theorem coefficient_lower {k : ℕ} (hk : 3 ≤ k) :
    41/20 * ((k+k).choose k : ℝ) ≤ ∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ) := by
  obtain ⟨n,rfl⟩ : ∃ n, k = n+3 := ⟨k-3, by omega⟩
  let N := n+3+(n+3)
  let c (r : ℕ) : ℝ := N.choose r
  have hc (r : ℕ) : 0 ≤ c r := Nat.cast_nonneg _
  have h₁ : c (n+3) * (n+3 : ℕ) = c (n+2) * (n+4 : ℕ) := by
    have h := Nat.choose_succ_right_eq N (n+2)
    rw [show N-(n+2)=n+4 by dsimp [N]; omega] at h
    dsimp only [c]
    exact_mod_cast h
  have h₂ : c (n+2) * (n+2 : ℕ) = c (n+1) * (n+5 : ℕ) := by
    have h := Nat.choose_succ_right_eq N (n+1)
    rw [show N-(n+1)=n+5 by dsimp [N]; omega] at h
    dsimp only [c]
    exact_mod_cast h
  push_cast at h₁ h₂
  have q₁ : 3/4 * c (n+3) ≤ c (n+2) := by
    apply le_of_mul_le_mul_right (a := (n:ℝ)+4) _ (by positivity)
    nlinarith only [h₁, mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (hc (n+3))]
  have q₂ : 2/5 * c (n+2) ≤ c (n+1) := by
    apply le_of_mul_le_mul_right (a := (n:ℝ)+5) _ (by positivity)
    nlinarith only [h₂, mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (hc (n+2))]
  change _ ≤ ∑ i : Fin (n+3), c (i.val+1)
  rw [Fin.sum_univ_eq_sum_range (fun i => c (i+1))]
  simp only [Finset.sum_range_succ]
  have hzero : 0 ≤ ∑ i ∈ Finset.range n, c (i+1) := Finset.sum_nonneg (fun i _ => hc _)
  change 41/20 * c (n+3) ≤ _
  linarith

end BlockPermanents.FiveNumbers
