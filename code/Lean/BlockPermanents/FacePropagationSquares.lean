import BlockPermanents.FaceMeanSquares

/-! # Exact four-face propagation through marked deletions

Every step retains one copy of the three-face cut remainder and three copies
of the four-face cut remainder. The terminal three-label exit is itself an
average of squared norms.
-/
namespace BlockPermanents.FacePropagationSquares
open FaceMeans FaceSlacks FaceMeanSquares
noncomputable section

variable {m d : ℕ}

/-- Four times the surplus after the weighted four-face slacks are collected. -/
def propagation (x : Input m d) : ℕ → ℕ → ℝ
  | 0, _ | 1, _ | 2, _ => 0
  | 3, r => 4 * mean x r 3 triple
  | 4, _ => 0
  | n+5, r => propagation x (n+4) r +
      (n+4 : ℝ)^2 * propagation x (n+3) (r+1) +
      ((n+4).choose 2 : ℝ) * (tripleRemainder x r (n+2) + 3 * quadRemainder x r (n+1))

private theorem peel_squares (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    {r n : ℕ} (fit : 2*r+(n+5) ≤ m) :
    4*S x (n+5) r = 4*S x (n+4) r + (n+4 : ℝ)^2 * (4*S x (n+3) (r+1)) +
      ((n+4).choose 2 : ℝ) * S x 4 r +
      ((n+4).choose 2 : ℝ) * (tripleRemainder x r (n+2) + 3 * quadRemainder x r (n+1)) := by
  have step := slack_step (n := n+2) x unit fit
  have h₃ := triple_identity (n := n+2) x unit fit
  have h₄ := quad_identity (n := n+1) x unit fit
  have hc : (((n+4).choose 2 : ℕ) : ℝ) = (n+4 : ℝ)*(n+3 : ℝ)/2 := by
    have h := Nat.succ_mul_choose_eq (n+3) 1
    simp only [Nat.choose_one_right] at h
    apply (eq_div_iff (by norm_num)).mpr
    exact_mod_cast h.symm
  rw [FaceSlacks.four x unit (by omega), hc]
  push_cast at step
  linear_combination 2*step + (n+4 : ℝ)*(n+3 : ℝ)/2*h₃ + 3*(n+4 : ℝ)*(n+3 : ℝ)/2*h₄

open private four from BlockPermanents.FaceWeights in
private theorem weighted_four (R r : ℕ) (Q : ℕ → ℝ) : FaceWeights.weighted 4 R r Q = 4 * Q r :=
  four R r Q

open private collect small from BlockPermanents.FaceWeights in
open private small_zero three from BlockPermanents.FaceSlacks in
/-- Exact form of the four-face propagation inequality for every deletion depth. -/
theorem propagate_squares (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    {r q R : ℕ} (fit : 2*r+q ≤ m) (hR : q ≤ R) :
    4*S x q r = FaceWeights.weighted q R r (S x 4) + propagation x q r := by
  by_cases hs : q < 4
  · rw [small hs, zero_add]
    by_cases hz : q ≤ 2
    · rw [small_zero x unit fit hz]
      interval_cases q <;> simp [propagation]
    · have ht : q = 3 := by omega
      subst q
      rw [three x unit fit, propagation]
  by_cases hf : q = 4
  · subst q
    simp only [weighted_four, propagation, add_zero]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' (show 5 ≤ q by omega)
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have h₁ := propagate_squares (q := n+4) (R := R+1) (r := r) x unit (by omega) (by omega)
  have h₂ := propagate_squares (q := n+3) (R := R) (r := r+1) x unit (by omega) (by omega)
  rw [peel_squares x unit fit, h₁, h₂, collect (n := n+3) (by omega), propagation]
  push_cast
  ring
termination_by q

open private mean_nonneg from BlockPermanents.FaceMeanSquares in
/-- Every summand in the propagated remainder is nonnegative. -/
theorem propagation_nonneg (x : Input m d) {r q : ℕ} (fit : 2*r+q ≤ m) :
    0 ≤ propagation x q r := by
  by_cases h : q ≤ 4
  · interval_cases q <;> simp only [propagation, le_refl]
    apply mul_nonneg (by norm_num)
    apply mean_nonneg x fit
    intro y
    unfold triple Bend.energy
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 5 ≤ q by omega)
  rw [propagation]
  have h₁ := propagation_nonneg (q := n+4) (r := r) x (by omega)
  have h₂ := propagation_nonneg (q := n+3) (r := r+1) x (by omega)
  have h₃ := tripleRemainder_nonneg (n := n+2) x fit
  have h₄ := quadRemainder_nonneg (n := n+1) x fit
  positivity
termination_by q

end
end BlockPermanents.FacePropagationSquares
