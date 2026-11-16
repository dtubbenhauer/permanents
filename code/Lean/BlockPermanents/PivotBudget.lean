import BlockPermanents.TradePivots
import BlockPermanents.FaceCoarseCertificate

/-! # Collecting the pivot trades by matching degree in Lemma 7D.3 -/
namespace BlockPermanents.PivotBudget
open Threshold TradePivots
noncomputable section

/-- Use the elimination parameter on each active link. Other links have zero spectator coefficient. -/
def choice (m b i : ℕ) : ℝ := if i+1 < m/2 then parameter m b i else 1

theorem choice_pos (m b : ℕ) (hp : (tradeMatrix m b).PosSemidef) (i : ℕ) : 0 < choice m b i := by
  unfold choice
  split_ifs with h
  · exact (trade_parameter m b i hp h).1
  · exact zero_lt_one

/-- The unspent final pivot, weighted by the highest matching moment. -/
def terminal (m b : ℕ) (z : ℕ → ℝ) :=
  if m/2 = 0 then 0 else tradePivot m b (m/2-1) * z (m/2)

theorem terminal_nonneg (m b : ℕ) (hp : (tradeMatrix m b).PosSemidef) (z : ℕ → ℝ)
    (hz : 0 ≤ z (m/2)) : 0 ≤ terminal m b z := by
  unfold terminal
  split_ifs with h
  · exact le_rfl
  · exact mul_nonneg (tradePivot_sign m b hp _ (by omega)).1 hz

private def incoming (h : ℕ → ℝ) (i : ℕ) : ℝ := if i=0 then 0 else h (i-1)

private theorem shift (n : ℕ) (h z : ℕ → ℝ) (hlast : ∀ i, i+1=n → h i=0) :
    ∑ i ∈ Finset.range n, h i*z (i+2) = ∑ i ∈ Finset.range n, incoming h i*z (i+1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ (f := fun i => h i*z (i+2)),
      Finset.sum_range_succ' (f := fun i => incoming h i*z (i+1))]
    simp [hlast n rfl, incoming]

private theorem collect_gain (m : ℕ) (u z : ℕ → ℝ) :
    FaceCoarseCertificate.gain z m u = ∑ i ∈ Finset.range (m/2),
      ((spectator m i:ℝ)*(1-u i) + incoming (fun j => (spectator m j:ℝ)*(1-1/u j)) i)*z (i+1) := by
  let a (i : ℕ) : ℝ := (spectator m i:ℝ)*(1-u i)
  let c (i : ℕ) : ℝ := (spectator m i:ℝ)*(1-1/u i)
  have hx (i) : (spectator m i : ℝ)*((1-u i)*z (i+1)+(1-1/u i)*z (i+2)) =
      a i*z (i+1) + c i*z (i+2) := by dsimp [a,c]; ring
  rw [FaceCoarseCertificate.gain]
  simp_rw [hx]
  calc
    _ = ∑ i ∈ Finset.range (m/2), (a i*z (i+1) + c i*z (i+2)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i _ hi
      simp only [Finset.mem_range] at hi
      simp [a,c, FaceWeights.spectator_outside (by omega : m < 4+2*i)]
    _ = _ := by
      rw [Finset.sum_add_distrib, shift (m/2) c z (fun i hi => by
        simp [c, FaceWeights.spectator_outside (by omega : m < 4+2*i)]), ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => (add_mul ..).symm)

private theorem collect_degree (m b i : ℕ) (hp : (tradeMatrix m b).PosSemidef) (hi : i < m/2) :
    (((m/2).choose (i+1)*b^(i+1) : ℕ):ℝ) - pathCoeff m (i+1) +
      ((spectator m i:ℝ)*(1-choice m b i) +
        incoming (fun j => (spectator m j:ℝ)*(1-1/choice m b j)) i) =
    if i+1 < m/2 then 0 else tradePivot m b i := by
  have h := degree_budget m b i hp hi
  have hh : (spectator m i:ℝ) * choice m b i =
      if i+1 < m/2 then (spectator m i:ℝ)*parameter m b i else 0 := by
    by_cases hnext : i+1<m/2
    · simp [choice,hnext]
    · simp [choice,hnext, FaceWeights.spectator_outside (by omega : m < 4+2*i)]
  have hb : incoming (fun j => (spectator m j:ℝ)*(1-1/choice m b j)) i =
      (if i=0 then 0 else (spectator m (i-1):ℝ)) -
      (if i=0 then 0 else (spectator m (i-1):ℝ) / parameter m b (i-1)) := by
    cases i with
    | zero => simp [incoming]
    | succ i => simp [incoming, choice,hi, mul_sub, div_eq_mul_inv]
  rw [hb, mul_sub, mul_one, hh]
  unfold tradeDiagonal at h
  linarith only [h]

/-- Collect the two adjacent matching moments of every trade. All interior
coefficients cancel; a chain of zero or one degree uses the same identity. -/
theorem identity (m b : ℕ) (hp : (tradeMatrix m b).PosSemidef) (z : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m/2+1), (((m/2).choose i*b^i:ℕ):ℝ)*z i) -
    (∑ i ∈ Finset.range (m/2+1), (pathCoeff m i:ℝ)*z i) +
      FaceCoarseCertificate.gain z m (choice m b) = terminal m b z := by
  rw [Finset.sum_range_succ' (f := fun i => (((m/2).choose i*b^i:ℕ):ℝ)*z i),
      Finset.sum_range_succ' (f := fun i => (pathCoeff m i:ℝ)*z i), collect_gain]
  simp only [Nat.choose_zero_right,pow_zero,one_mul,pathCoeff,Nat.cast_one]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ Finset.range (m/2), (if i+1 < m/2 then 0 else tradePivot m b i)*z (i+1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← sub_mul, ← add_mul, collect_degree _ _ _ hp (Finset.mem_range.mp hi)]
    _ = _ := by
      generalize hn : m/2 = n
      cases n with
      | zero => simp [terminal,hn]
      | succ n =>
        rw [Finset.sum_range_succ]
        have hz : (∑ i ∈ Finset.range n, (if i+1 < n+1 then 0 else tradePivot m b i)*z (i+1)) = 0 :=
          Finset.sum_eq_zero fun i hi => by simp [show i+1<n+1 from Nat.succ_lt_succ (Finset.mem_range.mp hi)]
        rw [hz]
        simp [terminal,hn]

end
end BlockPermanents.PivotBudget
