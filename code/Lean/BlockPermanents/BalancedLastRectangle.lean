import BlockPermanents.BalancedBorder

/-! The four borders of the balanced cut square, with all residual energies retained. -/
namespace BlockPermanents.BalancedLastRectangle

open Bend BalancedSupport
noncomputable section

/-- The proper cuts leave their perpendicular components on the bottom, top,
left and right borders. Every interior cut contributes its whole energy. -/
def remainder (k : ℕ) (E R₁ R₂ : CutIndex k k → CutIndex k k → ℝ) : ℝ :=
  (∑ i ∈ mid k, (Bend.weight k k i : ℝ) *
    (R₁ i (zeroCut k) + R₁ i (fullCut k) + R₂ (zeroCut k) i + R₂ (fullCut k) i)) +
  ∑ i ∈ mid k, ∑ j ∈ mid k,
    (Bend.weight k k i : ℝ) * (Bend.weight k k j : ℝ) * E i j

theorem remainder_nonneg (k : ℕ) (E R₁ R₂ : CutIndex k k → CutIndex k k → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (h₁ : ∀ i j, 0 ≤ R₁ i j) (h₂ : ∀ i j, 0 ≤ R₂ i j) :
    0 ≤ remainder k E R₁ R₂ := by
  unfold remainder
  refine add_nonneg (Finset.sum_nonneg fun i _ => ?_) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => ?_)
  · exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (add_nonneg (add_nonneg (h₁ _ _) (h₁ _ _)) (h₂ _ _)) (h₂ _ _))
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hE i j)

private theorem sum_noncorners {k : ℕ} (hk : 0 < k)
    (W : CutIndex k k × CutIndex k k → ℝ) :
    ∑ u ∈ (BalancedCorners.corners k)ᶜ, W u =
      (∑ i ∈ mid k, ((W (i, zeroCut k) + W (i, fullCut k)) +
        (W (zeroCut k, i) + W (fullCut k, i)))) +
      ∑ i ∈ mid k, ∑ j ∈ mid k, W (i,j) := by
  have disjoint₁ : Disjoint (mid k ×ˢ ends k) (ends k ×ˢ mid k) := by
    refine Finset.disjoint_left.mpr fun u h₁ h₂ => ?_
    exact (Finset.mem_compl.mp (Finset.mem_product.mp h₁).1) (Finset.mem_product.mp h₂).1
  have disjoint₂ : Disjoint ((mid k ×ˢ ends k) ∪ (ends k ×ˢ mid k)) (mid k ×ˢ mid k) := by
    refine Finset.disjoint_left.mpr fun u h₁ h₂ => ?_
    rcases Finset.mem_union.mp h₁ with h | h
    · exact (Finset.mem_compl.mp (Finset.mem_product.mp h₂).2) (Finset.mem_product.mp h).2
    · exact (Finset.mem_compl.mp (Finset.mem_product.mp h₂).1) (Finset.mem_product.mp h).1
  have ne : zeroCut k ≠ fullCut k := fun h => hk.ne (congrArg Fin.val h)
  have sum_ends (g : CutIndex k k → ℝ) : ∑ i ∈ ends k, g i = g (zeroCut k) + g (fullCut k) := by
    rw [ends, Finset.sum_pair ne]
  rw [rectangle, Finset.sum_union disjoint₂, Finset.sum_union disjoint₁,
    Finset.sum_product, Finset.sum_product, Finset.sum_product, Finset.sum_comm (s := ends k)]
  simp_rw [sum_ends]
  simp only [Finset.sum_add_distrib]

/-- Summing the two trace-cup resolutions gives one full weight at each
single-edge exit and two full weights at the twice-completed exit. -/
theorem rectangle_exact {k : ℕ} (hk : 0 < k)
    (E R₁ R₂ : CutIndex k k → CutIndex k k → ℝ)
    (h₁ : ∀ r t, r ∈ mid k → t ∈ ends k →
      E r t = E (fullCut k) t / ((k + (k-r.val) - 1).choose (k-r.val) : ℝ) + R₁ r t)
    (h₂ : ∀ r t, r ∈ ends k → t ∈ mid k →
      E r t = E r (fullCut k) / ((k + (k-t.val) - 1).choose (k-t.val) : ℝ) + R₂ r t) :
    ∑ u ∈ (BalancedCorners.corners k)ᶜ,
      (Bend.weight k k u.1 : ℝ) * (Bend.weight k k u.2 : ℝ) * E u.1 u.2 =
    lastWeight k * (E (fullCut k) (zeroCut k) + E (zeroCut k) (fullCut k) +
      2 * E (fullCut k) (fullCut k)) + remainder k E R₁ R₂ := by
  rw [sum_noncorners hk, remainder, ← add_assoc]
  apply congrArg (· + _)
  rw [← middle_weight, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hzero : zeroCut k ∈ ends k := by simp [ends]
  have hfull : fullCut k ∈ ends k := by simp [ends]
  simp only [Prod.fst, Prod.snd]
  rw [h₁ i _ hi hzero, h₁ i _ hi hfull, h₂ _ i hzero hi, h₂ _ i hfull hi]
  simp only [Bend.weight, zeroCut, fullCut, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, Nat.cast_mul, one_mul, mul_one]
  unfold BalancedSupport.weight
  ring

end
end BlockPermanents.BalancedLastRectangle
