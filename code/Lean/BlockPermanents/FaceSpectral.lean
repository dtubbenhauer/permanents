import BlockPermanents.TradeMatrix
import BlockPermanents.FaceWeights
import BlockPermanents.Matchings

/-! # The four-face spectral criterion in matching coordinates -/
namespace BlockPermanents.FaceSpectral
open Threshold TradeMatrix
noncomputable section

private theorem link_row {m : ℕ} (w : ℕ → ℝ) (i : Fin (m/2)) :
    ∑ j : Fin (m/2), 2 * link m i j * w i * w j =
      2*(spectator m i:ℝ)*w i*w (i+1) := by
  by_cases hn : i.val+1 < m/2
  · let j : Fin (m/2) := ⟨i.val+1,hn⟩
    rw [Finset.sum_eq_single j]
    · simp [j,link]
    · intro k _ h
      have hk : i.val+1 ≠ k.val := by intro he; exact h (Fin.ext he.symm)
      simp [link,hk]
    · simp
  · have h := FaceWeights.spectator_outside (q := m) (r := i.val) (by omega)
    simp [link, h]

private theorem slide {m : ℕ} (w : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m/2), (if i=0 then 0 else (spectator m (i-1) : ℝ)) * w i =
    ∑ i ∈ Finset.range (m/2), (spectator m i : ℝ)*w (i+1) := by
  generalize hn : m/2 = n
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ' (f := fun i => (if i=0 then 0 else (spectator m (i-1) : ℝ)) * w i),
      Finset.sum_range_succ (f := fun i => (spectator m i : ℝ)*w (i+1))]
    simp [FaceWeights.spectator_outside (by omega : m < 4+2*n)]

private theorem truncate {m : ℕ} (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m+1), (spectator m i : ℝ)*f i =
    ∑ i ∈ Finset.range (m/2), (spectator m i : ℝ)*f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  simp only [Finset.mem_range] at hi
  simp [FaceWeights.spectator_outside (by omega : m < 4+2*i)]

/-- Positivity of the tridiagonal matrix tested on the square roots of all
positive-degree matching moments. The missing final edge has coefficient zero. -/
theorem compare {m b : ℕ} (z : ℕ → ℝ) (hz : ∀ s, 0 ≤ z s)
    (psd : (tradeMatrix m b).PosSemidef) :
    (∑ s ∈ Finset.range (m/2+1), (pathCoeff m s : ℝ) * z s) -
      (∑ s ∈ Finset.range (m+1), (spectator m s : ℝ) *
        (Real.sqrt (z (s+1)) - Real.sqrt (z (s+2)))^2) ≤
      ∑ s ∈ Finset.range (m/2+1), (((m/2).choose s * b^s : ℕ) : ℝ) * z s := by
  let w (j : ℕ) := Real.sqrt (z (j+1))
  let v : Fin (m/2) → ℝ := fun j => w j
  have he := psd.2 v
  change 0 ≤ dotProduct v ((tradeMatrix m b).mulVec v) at he
  rw [quadratic] at he
  simp only [v,link_row] at he
  have hs (j) : (w j)^2 = z (j+1) := Real.sq_sqrt (hz _)
  have hd (i : Fin (m/2)) : tradeMatrix m b i i * (w i)^2 =
      (((m/2).choose (i.val+1)*b^(i.val+1) : ℕ):ℝ) * z (i.val+1) -
      (pathCoeff m (i.val+1):ℝ)*z (i.val+1) + (spectator m i.val : ℝ)*z (i.val+1) +
      (if i.val=0 then 0 else (spectator m (i.val-1):ℝ))*z (i.val+1) := by
    rw [hs]
    simp [tradeMatrix,add_mul,sub_mul]
  simp_rw [hd] at he
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at he
  rw [Fin.sum_univ_eq_sum_range (fun i => (((m/2).choose (i+1)*b^(i+1) : ℕ):ℝ) * z (i+1)),
    Fin.sum_univ_eq_sum_range (fun i => (pathCoeff m (i+1):ℝ)*z (i+1)),
    Fin.sum_univ_eq_sum_range (fun i => (spectator m i:ℝ)*z (i+1)),
    Fin.sum_univ_eq_sum_range (fun i => (if i = 0 then 0 else (spectator m (i-1):ℝ)) * z (i+1)),
    Fin.sum_univ_eq_sum_range (fun i => 2*(spectator m i:ℝ)*w i*w (i+1))] at he
  rw [slide (fun i => z (i+1))] at he
  rw [Finset.sum_range_succ' (f := fun s => (pathCoeff m s:ℝ) * z s),
    Finset.sum_range_succ' (f := fun s => (((m/2).choose s * b^s : ℕ) : ℝ) * z s),truncate]
  simp only [pathCoeff, Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul]
  have hr (j : ℕ) : (spectator m j : ℝ)*(Real.sqrt (z (j+1))-Real.sqrt (z (j+2)))^2 =
      (spectator m j:ℝ)*z (j+1) + (spectator m j:ℝ)*z (j+2) -
      2*(spectator m j:ℝ)*w j*w (j+1) := by
    change _*(w j - w (j+1))^2 = _
    rw [sub_sq, mul_add, mul_sub, hs, hs]
    ring
  simp_rw [hr]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  linarith only [he]

end
end BlockPermanents.FaceSpectral
