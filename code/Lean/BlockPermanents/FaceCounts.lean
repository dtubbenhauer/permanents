import BlockPermanents.FaceWeights

/-! # Unnormalized prescribed-face coefficients

Writing the mean of labeled four-sets and unordered matchings as their
sum divides the coefficient h/4 by d, their multiplicity. This verifies
the two deletion ratios and the recursion for the individual coefficient c.
-/
namespace BlockPermanents.FaceCounts
open Threshold FaceWeights
noncomputable section

/-- Four unordered labels and r unordered unoriented edges off them. -/
def multiplicity (q r : ℕ) : ℝ :=
  if 4+2*r ≤ q then
    (q.factorial : ℝ)/(24*2^r*(r.factorial : ℝ)*((q-(4+2*r)).factorial : ℝ))
  else 0

/-- Coefficient per prescribed four-set and matching in the unaveraged sum. -/
def coeff (q r : ℕ) : ℝ := spectator q r/(4*multiplicity q r)

theorem multiplicity_pos {q r : ℕ} (fit : 4+2*r ≤ q) : 0 < multiplicity q r := by
  rw [multiplicity,if_pos fit]
  positivity

/-- The binomial-times-factorial expression for d in Appendix A.1. -/
theorem multiplicity_eq {q r : ℕ} (fit : 4+2*r ≤ q) :
    multiplicity q r = (q.choose 4 : ℝ) * ((q-4).factorial : ℝ) /
      (2^r*(r.factorial : ℝ)*((q-4-2*r).factorial : ℝ)) := by
  have hn := Nat.choose_mul_factorial_mul_factorial (n := q) (k := 4) (by omega)
  have h : (q.choose 4 : ℝ)*24*((q-4).factorial : ℝ) = (q.factorial : ℝ) := by
    exact_mod_cast (show q.choose 4 * 24 * (q-4).factorial = q.factorial from hn)
  rw [multiplicity,if_pos fit, Nat.sub_add_eq]
  rw [← h]
  ring

theorem counted (q r : ℕ) : 4*multiplicity q r*coeff q r = spectator q r := by
  by_cases fit : 4+2*r ≤ q
  · rw [coeff, mul_div_cancel₀ _ (by have := multiplicity_pos fit; positivity)]
  · simp [multiplicity, fit, spectator_outside (lt_of_not_ge fit)]

/-- Single deletion ratio, including the boundary with no free label. -/
theorem single_ratio {n r : ℕ} (fit : 4+2*r ≤ n+1) :
    ((n+1-(4+2*r) : ℕ) : ℝ)*multiplicity (n+1) r = (n+1 : ℝ)*multiplicity n r := by
  rw [multiplicity,if_pos fit,multiplicity]
  by_cases h : 4+2*r ≤ n
  · rw [if_pos h, show n+1-(4+2*r) = (n-(4+2*r))+1 by omega, Nat.factorial_succ,
      Nat.factorial_succ (n-(4+2*r))]
    generalize (n-(4+2*r)) = k
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    field_simp
    ring
  · rw [if_neg h, show n+1-(4+2*r) = 0 by omega]
    simp

/-- Double deletion ratio, accounting for both ends of each marked edge. -/
theorem pair_ratio {n r : ℕ} (fit : 4+2*r ≤ n) :
    2*(r+1 : ℝ)*multiplicity (n+2) (r+1) = (n+2 : ℝ)*(n+1 : ℝ)*multiplicity n r := by
  rw [multiplicity,if_pos (show 4+2*(r+1) ≤ n+2 by omega),multiplicity,if_pos fit,
    show n+2-(4+2*(r+1))= n-(4+2*r) by omega,
    Nat.factorial_succ (n+1), Nat.factorial_succ n, Nat.factorial_succ r, pow_succ]
  push_cast
  field_simp
  ring

theorem coeff_zero (n : ℕ) : coeff (n+4) 0 = 1/(n+1 : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := n+4) (k := 3) (by omega)
  have hn : (n+4).choose 3 * 6 * ((n+1)*n.factorial) = (n+4).factorial := by
    rw [← Nat.factorial_succ]
    exact h
  have hR : ((n+4).choose 3 : ℝ) * 6 * ((n+1 : ℝ)*(n.factorial : ℝ)) =
      ((n+4).factorial : ℝ) := by exact_mod_cast hn
  rw [coeff,spectator,if_pos (by omega),multiplicity,if_pos (by omega)]
  norm_num [show n+4-4=n by omega]
  field_simp
  nlinarith only [hR]

/-- The exact recurrence for c in Appendix A.1 with explicit per-face
multiplicity. Out-of-range weights vanish by their definitions. -/
theorem coeff_succ {n r : ℕ} (fit : 4+2*r ≤ n) :
    (n+2 : ℝ)*coeff (n+2) (r+1) =
      ((n+2-(4+2*(r+1)) : ℕ) : ℝ)*coeff (n+1) (r+1) +
        2*(r+1 : ℝ)*(n+1 : ℝ)*coeff n r := by
  let q := n+2
  have hs := single_ratio (n := n+1) (r := r+1) (by omega)
  have hp := pair_ratio fit
  have hr : (spectator (n+2) (r+1) : ℝ) =
      spectator (n+1) (r+1) + (n+1 : ℝ)^2*spectator n r := by
    exact_mod_cast spectator_step n r
  have h : 4*multiplicity (n+2) (r+1) ≠ 0 := by
    have := multiplicity_pos (q := n+2) (r := r+1) (by omega)
    positivity
  apply (mul_right_inj' h).mp
  rw [show (↑(n+1) : ℝ)+1 = (n+2 : ℝ) by push_cast; ring] at hs
  linear_combination
    (n+2 : ℝ)*(counted (n+2) (r+1)) -
    (n+2 : ℝ)*(counted (n+1) (r+1)) -
    (n+2 : ℝ)*(n+1 : ℝ)^2*(counted n r) +
    (n+2 : ℝ)*hr - 4*coeff (n+1) (r+1)*hs - 4*(n+1 : ℝ)*coeff n r*hp

end
end BlockPermanents.FaceCounts
