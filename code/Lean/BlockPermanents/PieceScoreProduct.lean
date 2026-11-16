import BlockPermanents.CycleParameters

/-! The real matching factors on disjoint sets multiply under uniform
relabeling, with zero top coefficient when an odd cycle uses every label. -/
namespace BlockPermanents.PieceScoreProduct
open CyclePlans CycleMatching CycleComposition CycleParameters Matchings
noncomputable section

variable {a b m : ℕ}

private theorem tail_score (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m)
    (i : ℕ) (hi : 2*i ≤ a) (p : List Piece) (u : ℕ → ℝ) (j : ℕ)
    (hj : 2*j+planSize p ≤ b) :
    average m (fun σ => Z (leftGram g e σ) i * score p u (Z (rightGram g e σ)) j) =
      score p u (Z g) (i+j) := by
  induction p generalizing j u with
  | nil => exact split_Z g e hi (by simpa [planSize] using hj)
  | cons t p ih =>
    have hsize : planSize (t::p) = t.size + planSize p := rfl
    rw [hsize] at hj
    cases t with
    | fixed n =>
      exact ih _ _ (by simp only [Piece.size] at hj; omega)
    | even r =>
      simp only [score,Nat.add_assoc]
      exact ih _ _ (by simp only [Piece.size] at hj; omega)
    | odd r s =>
      simp only [Piece.size] at hj
      cases s with
      | zero =>
        simp only [score,Nat.cast_zero,zero_div,zero_mul,add_zero,Nat.add_assoc]
        simp_rw [← mul_assoc, mul_comm _ ((u 0 / (0 + 1) + 1 / u 0) / 2),mul_assoc]
        rw [average_smul]
        rw [ih _ _ (by omega)]
      | succ s =>
        let c : ℝ := (u 0 / ((s+1:ℕ)+1 : ℝ) + 1 / u 0)/2
        let d : ℝ := ((s+1:ℕ):ℝ)/(2*u 0)
        change average m (fun σ => Z (leftGram g e σ) i *
          (c*score p _ (Z (rightGram g e σ)) (j+(r+1)) +
           d*score p _ (Z (rightGram g e σ)) (j+(r+2)))) =
           c*score p _ (Z g) (i+j+(r+1)) + d*score p _ (Z g) (i+j+(r+2))
        simp_rw [mul_add,mul_left_comm _ c,mul_left_comm _ d]
        rw [average_add,average_smul,average_smul,ih _ _ (by omega),ih _ _ (by omega)]
        simp only [Nat.add_assoc]

theorem score_split (t : Piece) (p : List Piece) (u : ℕ → ℝ) (g : Gram (planSize (t::p))) :
    let e : Fin t.size ⊕ Fin (planSize p) ≃ Fin (planSize (t::p)) := finSumFinEquiv
    average _ (fun σ => score [t] u (Z (leftGram g e σ)) 0 *
      score p (fun i => u (i+1)) (Z (rightGram g e σ)) 0) = score (t::p) u (Z g) 0 := by
  let e : Fin t.size ⊕ Fin (planSize p) ≃ Fin (planSize (t::p)) := finSumFinEquiv
  have splitAt (i : ℕ) (hi : 2*i ≤ t.size) :
      average _ (fun σ => Z (leftGram g e σ) i * score p (fun i => u (i+1)) (Z (rightGram g e σ)) 0) =
        score p (fun i => u (i+1)) (Z g) i := by
    simpa only [Nat.add_zero] using tail_score g e i hi p (fun i => u (i+1)) 0 (by omega)
  dsimp only
  cases t with
  | fixed n => exact splitAt 0 (by omega)
  | even r => simpa only [score,Nat.zero_add] using splitAt (r+1) (by simp only [Piece.size]; omega)
  | odd r s =>
    simp only [score,Nat.zero_add,add_mul,mul_assoc,average_add,average_smul]
    cases s with
    | zero =>
      simp only [Nat.cast_zero,zero_div,zero_mul,add_zero]
      rw [splitAt (r+1) (by simp only [Piece.size]; omega)]
    | succ s =>
      rw [splitAt (r+1) (by simp only [Piece.size]; omega),splitAt (r+2) (by simp only [Piece.size]; omega)]

open private score_sum score_smul from BlockPermanents.CycleParameters in
/-- Evaluating the real product at the actual moments equals its coefficient expansion. -/
theorem score_eq_sum (p : List Piece) (u : ℕ → ℝ) (g : Gram (planSize p)) :
    score p u (Z g) 0 = ∑ j ∈ Finset.range (planSize p/2+1), pcoeff p u j * Z g j := by
  have he : Z g = fun t => ∑ j ∈ Finset.range (planSize p/2+1),
      Z g j * (if t=j then 1 else 0) := by
    funext t
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_range]
    split_ifs with h
    · rfl
    · exact Z_outside g (by omega)
  conv_lhs => rw [he]
  rw [score_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (score_smul p u (fun a => if a=t then 1 else 0) 0 (Z g t)).trans (mul_comm ..)

end
end BlockPermanents.PieceScoreProduct
