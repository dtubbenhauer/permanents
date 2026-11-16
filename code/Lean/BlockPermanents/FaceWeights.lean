import BlockPermanents.Threshold

/-! # The four-face spectator recurrence, Appendix A.1

The normalized average over the four-set and its spectator matching absorbs
the number of their labelings. Its coefficient is h(q,r)/4.
-/
namespace BlockPermanents.FaceWeights
open Threshold
noncomputable section

theorem spectator_outside {q r : ℕ} (h : q < 4+2*r) : spectator q r = 0 := by
  cases r with
  | zero => simp [spectator, show ¬ 4 ≤ q by omega]
  | succ r =>
      cases q with
      | zero => rfl
      | succ q =>
          cases q with
          | zero => rfl
          | succ q => simp [spectator, show ¬ 4+2*(r+1) ≤ q+2 by omega]

theorem spectator_step (n r : ℕ) :
    spectator (n+2) (r+1) = spectator (n+1) (r+1)+(n+1)^2*spectator n r := by
  by_cases h : 4+2*(r+1) ≤ n+2
  · simp [spectator, h]
  · rw [spectator_outside (by omega : n+2 < 4+2*(r+1)),
      spectator_outside (by omega : n+1 < 4+2*(r+1)),
      spectator_outside (by omega : n < 4+2*r)]
    simp

/-- Four times the face lower bound, truncating after R spectator edges.
The calling theorem uses R at least q so that every face occurs. -/
def weighted (q R d : ℕ) (Q : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (R+1), (spectator q r : ℝ)*Q (d+r)

private theorem collect {n R d : ℕ} (hn : 3 ≤ n) (Q : ℕ → ℝ) :
    weighted (n+2) (R+1) d Q = weighted (n+1) (R+1) d Q +
      (n+1 : ℝ)^2*weighted n R (d+1) Q + ((n+1).choose 2 : ℝ)*Q d := by
  unfold weighted
  rw [Finset.sum_range_succ' (f := fun i => (spectator (n+2) i : ℝ)*Q (d+i)),
    Finset.sum_range_succ' (f := fun i => (spectator (n+1) i : ℝ)*Q (d+i))]
  simp only [spectator_step, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Nat.add_zero]
  simp only [spectator, if_pos (show 4 ≤ n+2 by omega), if_pos (show 4 ≤ n+1 by omega)]
  rw [show (n+2).choose 3 = (n+1).choose 2 + (n+1).choose 3 from Nat.choose_succ_succ _ _]
  simp only [Nat.cast_add, show ∀ r, Q (d+(r+1)) = Q ((d+1)+r) from fun r => congrArg Q (by omega)]
  ring

private theorem four (R d : ℕ) (Q : ℕ → ℝ) : weighted 4 R d Q = 4*Q d := by
  unfold weighted
  rw [Finset.sum_eq_single 0]
  · norm_num [spectator, Nat.choose]
  · intro r _ hr
    simp [spectator_outside (by omega : 4 < 4+2*r)]
  · simp

private theorem small {q : ℕ} (hq : q < 4) (R d : ℕ) (Q : ℕ → ℝ) :
    weighted q R d Q = 0 := by
  unfold weighted
  exact Finset.sum_eq_zero fun r _ => by rw [spectator_outside (by omega : q < 4+2*r)]; simp

/-- The exact induction in the four-face argument. S(q,d) is the slack
at q remaining labels weighted by d marked edges, and Q(d) the averaged
slack of a prescribed four-set. The single new term in the recursive step
is the part supplied by the exit-face bound. -/
theorem propagate (m : ℕ) (S : ℕ → ℕ → ℝ) (Q : ℕ → ℝ)
    (small_nonneg : ∀ q d, 2*d+q ≤ m → q < 4 → 0 ≤ S q d)
    (base : ∀ d, 2*d+4 ≤ m → Q d ≤ S 4 d)
    (peel : ∀ n d, 2*d+(n+2) ≤ m → 3 ≤ n →
      4*S (n+1) d + (n+1 : ℝ)^2*(4*S n (d+1)) + ((n+1).choose 2 : ℝ)*Q d ≤ 4*S (n+2) d)
    (q R d : ℕ) (hR : q ≤ R) (fit : 2*d+q ≤ m) : weighted q R d Q ≤ 4*S q d := by
  by_cases h₁ : q < 4
  · rw [small h₁]
    linarith only [small_nonneg q d fit h₁]
  by_cases h₂ : q = 4
  · subst q
    rw [four]
    linarith only [base d fit]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ q by omega)
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have hn : 3 ≤ n := by omega
  rw [collect hn]
  exact le_trans (add_le_add_right (add_le_add (propagate m S Q small_nonneg base peel
    (n+1) (R+1) d (by omega) (by omega)) (mul_le_mul_of_nonneg_left
      (propagate m S Q small_nonneg base peel n R (d+1) (by omega) (by omega)) (by positivity))) _)
    (peel n d fit hn)
termination_by q

end
end BlockPermanents.FaceWeights
