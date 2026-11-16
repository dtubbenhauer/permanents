import BlockPermanents.PieceProductSquares

/-! The parity-filtered product formula in the proof of Lemma AC.1. -/
namespace BlockPermanents.PieceProductSquares
open ReflectedCycles CyclePlans CycleParameters CycleMatching CycleComposition Closures
noncomputable section

/-- On any fixed disjoint allocation, the product with either sign is the scaled
sum over precisely those local sign assignments with the prescribed parity.
The factor 2/2^v also covers the empty allocation. -/
theorem parity_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (A T : I → ℝ) (plus : Bool) :
    (∏ i, A i) + sign plus * (∏ i, T i) =
      (2 / (2 : ℝ) ^ Fintype.card I) *
      ∑ ε ∈ (Finset.univ : Finset (I → Bool)).filter (fun ε => (∏ i, sign (ε i)) = sign plus),
        ∏ i, (A i + sign (ε i) * T i) := by
  classical
  let v := (2 : ℝ) ^ Fintype.card I
  let χ (ε : I → Bool) := ∏ i, sign (ε i)
  let W (ε : I → Bool) := ∏ i, (A i + sign (ε i) * T i)
  have hA (i : I) : (∑ s : Bool, (A i + sign s * T i)) = 2 * A i := by
    simp [Fintype.sum_bool, sign]; ring
  have hT (i : I) : (∑ s : Bool, sign s * (A i + sign s * T i)) = 2 * T i := by
    simp [Fintype.sum_bool, sign]; ring
  have ha : (∑ ε, W ε) = v * ∏ i, A i := by
    change (∑ ε : I → Bool, ∏ i, (A i + sign (ε i)*T i)) = _
    rw [← Fintype.prod_sum (fun i s => A i + sign s * T i)]
    simp only [hA, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, v]
  have ht : (∑ ε, χ ε * W ε) = v * ∏ i, T i := by
    change (∑ ε : I → Bool, (∏ i, sign (ε i)) * (∏ i, (A i + sign (ε i)*T i))) = _
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i s => sign s * (A i + sign s * T i))]
    simp only [hT, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, v]
  have parity (ε : I → Bool) : χ ε = 1 ∨ χ ε = -1 := by
    apply sq_eq_one_iff.mp
    have h (s : Bool) : sign s ^ 2 = 1 := by cases s <;> norm_num [sign]
    simp [χ, ← Finset.prod_pow, h]
  have twice (ε : I → Bool) :
      2 * (if χ ε = sign plus then W ε else 0) = W ε + sign plus * (χ ε * W ε) := by
    rcases parity ε with hp | hp <;> cases plus <;> norm_num [hp, sign] <;> ring
  have eqn := Finset.sum_congr (s₁ := Finset.univ) rfl (fun ε _ => twice ε)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, ha, ht] at eqn
  change _ = 2 / v * ∑ ε ∈ Finset.univ.filter (fun ε => χ ε = sign plus), W ε
  rw [Finset.sum_filter, div_mul_eq_mul_div, eq_div_iff (by dsimp [v]; positivity)]
  linear_combination -eqn

/-- The unaveraged product on a fixed allocation of disjoint packets, with
its summands evaluated using the actual reflected halves on each piece. -/
theorem product_squares {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (a : I → Piece) (u : I → ℝ) (hu : ∀ i, 0 < u i)
    (x : (i : I) → Fin (a i).size → D → ℂ) (unit : ∀ i j, Bend.energy (x i j) = 1)
    (plus : Bool) :
    let g i := crossGram (x i) (x i)
    (∏ i, score [a i] (fun _ => u i) (Z (g i)) 0) +
      sign plus * (∏ i, (mean (g i) (piecePerm (a i))).re) =
      (2 / (2 : ℝ) ^ Fintype.card I) *
      ∑ ε ∈ (Finset.univ : Finset (I → Bool)).filter (fun ε => (∏ i, sign (ε i)) = sign plus),
        ∏ i, pieceEnergy (a i) (x i) (ε i) (u i) := by
  dsimp only
  rw [parity_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  exact Finset.prod_congr rfl (fun i _ => piece_identity (a i) (x i) (unit i) (ε i) (fun _ => u i) (hu i))

end
end BlockPermanents.PieceProductSquares
