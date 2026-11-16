import BlockPermanents.ThreePlaneMarcus
import BlockPermanents.BalancedLastMarcus
import BlockPermanents.FiveFullCertificate
import BlockPermanents.PathSpectrum
import BlockPermanents.MatchingFineSquares
import BlockPermanents.VerifiedPaper

/-! A single entry point for the manuscript's case-by-case proofs of Theorem
1A.1, using the weighted path matrix for the general threshold. -/
namespace BlockPermanents.PaperCertificate
open Closures Matchings MatchingThreshold SchurNormalization
noncomputable section

/-- The spectral proof of Theorem 7C.1, including singular and unnormalized
inputs, by comparing the coefficients against the actual matching moments. -/
theorem spectral_threshold {m k : ℕ} (hm : 2 ≤ m)
    (h : m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1)) : MarcusAt m k := by
  apply marcusAt_of_gram
  intro x
  let z := fun r => moment m r (packetEnergy x) (capWeight x)
  have hz (r) : 0 ≤ z r := moment_nonneg (fun i => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (fun i j => Complex.normSq_nonneg _)
  have low := MatchingFineSquares.average_bound x
  have high := MatchingUpper.permanent_le_upper (fun i => packet (x i))
  simp only [Coarse.bracket_self, Complex.ofReal_re] at high
  have hb : (((2^k-1:ℕ)):ℝ) = (2:ℝ)^k-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow k 2 (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have coeff (r) : (Threshold.pathCoeff m r : ℝ) ≤ ((m/2).choose r:ℝ) * ((2:ℝ)^k-1)^r := by
    rw [← hb, ← Nat.cast_pow, ← Nat.cast_mul]
    exact_mod_cast PathSpectrum.spectral_threshold m (2^k-1) r hm h
  exact high.trans ((Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (coeff r) (hz r)).trans low)

theorem logarithmic {m k : ℕ} (hm : 2 ≤ m) (h : 2*Real.logb 2 m ≤ k) : MarcusAt m k :=
  spectral_threshold hm (Threshold.threshold_of_square_le_pow _ _ hm
    ((square_le_pow_iff_log (by omega : 0 < m)).mpr h))

/-- The printed parameter range, assembled from the two-, three-, four- and
five-packet arguments and the spectral proof at general packet number. -/
theorem manuscript : ManuscriptTheorem := by
  intro m k hm hk conditions
  rcases conditions with h | ⟨rfl,h⟩ | ⟨h,ht⟩
  · interval_cases m
    · exact one_packet k
    · exact marcus_two hk (homogeneousSchur _ _ _)
    · exact ThreePlane.marcus_three hk
    · exact BalancedLast.marcus_four hk
  · exact FiveFullCertificate.marcus_five h
  · exact spectral_threshold h ht

end
end BlockPermanents.PaperCertificate
