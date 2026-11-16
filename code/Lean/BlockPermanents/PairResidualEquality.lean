import BlockPermanents.PairResidualSquares

/-! # Equality in the full-cap estimate -/
namespace BlockPermanents.PairResidual
open Closures Bend PairBound
open scoped BigOperators
noncomputable section

private theorem energy_eq_zero_iff {I : Type*} [Fintype I] (v : I → ℂ) :
    energy v = 0 ↔ v = 0 := by
  unfold energy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))]
  simp [funext_iff]

private theorem surplus_eq_zero_iff {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k)
    (hr : 0 < rank x r) :
    (k.choose r : ℝ)^2 / rank x r - (k.choose r : ℝ) = 0 ↔ rank x r = k.choose r := by
  have hc : (k.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (cut_le r)).ne'
  have hd : (rank x r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [sub_eq_zero, div_eq_iff hd, sq, mul_right_inj' hc]
  exact_mod_cast eq_comm

/-- The residual cut can vanish only if the halfweb is zero and either the
completed pairing vanishes or all of the possible survivor directions occur. -/
theorem summand_eq_zero_iff {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hx : packet x ≠ 0) (H : Word d k → ℂ) (r : CutIndex k k) :
    residualSummand a x H r = 0 ↔ residual a x H r = 0 ∧
      (bracket (scaled a x) H = 0 ∨ rank x r = k.choose r) := by
  have hc : 0 < (k.choose r : ℝ) := by exact_mod_cast Nat.choose_pos (cut_le r)
  have hr := rank_pos x hx r
  have he : 0 ≤ energy (residual a x H r) :=
    Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  rw [residualSummand, add_eq_zero_iff_of_nonneg (mul_nonneg (sq_nonneg _) he)
    (mul_nonneg (surplus_nonneg x r hr) (Complex.normSq_nonneg _))]
  simp only [mul_eq_zero, ne_of_gt (sq_pos_of_pos hc), false_or,
    energy_eq_zero_iff, surplus_eq_zero_iff x r hr, Complex.normSq_eq_zero]
  tauto

/-- Equality in Lemma 7A.1 is equivalent to the simultaneous vanishing
conditions on the nonzero cuts, with no condition on the straight cut. -/
theorem full_caps_eq_iff {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hunit : energy (scaled a x) = 1) {H : Word d k → ℂ} (hH : Symmetric H) :
    ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix (scaled a x)).mulVec H) =
      energy H + ((2 : ℝ)^k - 1) * Complex.normSq (bracket (scaled a x) H) ↔
    ∀ r : CutIndex k k, r ≠ zeroCut k → residual a x H r = 0 ∧
      (bracket (scaled a x) H = 0 ∨ rank x r = k.choose r) := by
  have hx := packet_ne_zero_of_unit hunit
  have total := full_caps_residual_squares a x hunit hH
  calc
    _ ↔ ∑ r ∈ Finset.univ.erase (zeroCut k), residualSummand a x H r = 0 := by
      constructor <;> intro h <;> linarith
    _ ↔ _ := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun r _ => summand_nonneg a x hx H r)]
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, summand_eq_zero_iff a x hx H]

end
end BlockPermanents.PairResidual
