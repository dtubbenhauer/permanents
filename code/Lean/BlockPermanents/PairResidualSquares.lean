import BlockPermanents.PairSeamCut
import BlockPermanents.HomogeneousSchurProof

/-! # The residual halfwebs in the full-cap estimate of Lemma 7A.1 -/
namespace BlockPermanents.PairResidual
open Bend Closures PairBound SchurNormalization
open scoped BigOperators Matrix
noncomputable section

/-- What remains of this cut after retaining one full-cap square for each
choice of its contracted slots. -/
def residualSummand {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (H : Word d k → ℂ) (r : CutIndex k k) : ℝ :=
  (k.choose r : ℝ)^2 * energy (residual a x H r) +
    ((k.choose r : ℝ)^2 / rank x r - (k.choose r : ℝ)) *
      Complex.normSq (bracket (scaled a x) H)

theorem summand_nonneg {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hx : packet x ≠ 0) (H : Word d k → ℂ) (r : CutIndex k k) :
    0 ≤ residualSummand a x H r :=
  add_nonneg (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
    (mul_nonneg (surplus_nonneg x r (rank_pos x hx r)) (Complex.normSq_nonneg _))

theorem packet_ne_zero_of_unit {d k : ℕ} {a : ℂ} {x : Fin k → Fin d → ℂ}
    (hunit : energy (scaled a x) = 1) : packet x ≠ 0 := by
  intro hx
  simp [scaled, hx, energy] at hunit

open private choose_sum_nonzero from BlockPermanents.PairBound in
/-- Lemma 7A.1 with the actual trace-cup complements on all nonzero cuts.
For fixed first packet the support and the projection in each summand are
the same for every symmetric second input. -/
theorem full_caps_residual_squares {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hunit : energy (scaled a x) = 1) {H : Word d k → ℂ} (hH : Symmetric H) :
    ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix (scaled a x)).mulVec H) -
        energy H - ((2 : ℝ)^k - 1) * Complex.normSq (bracket (scaled a x) H) =
      ∑ r ∈ Finset.univ.erase (zeroCut k), residualSummand a x H r := by
  let F := scaled a x
  let t := Complex.normSq (bracket F H)
  have hx := packet_ne_zero_of_unit hunit
  have total := congrArg Complex.re (closed_bent_schur d k k
    (homogeneousSchur_implies_unbent d k k (homogeneousSchur d k k)) F H)
  rw [product_quadratic_energy] at total
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at total
  change ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix F).mulVec H) =
    ∑ r, cutTerm F H r at total
  have straight : cutTerm F H (zeroCut k) = energy H := by
    rw [cutTerm, zero_cap_energy (scaled_symmetric a x) hH]
    simp only [F, hunit, one_mul, weight, zeroCut, Nat.choose_zero_right, Nat.cast_one]
  have split (r : CutIndex k k) : cutTerm F H r =
      residualSummand a x H r + (k.choose r : ℝ) * t := by
    rw [cut_resolution a x hH r (rank_pos x hx r)]
    dsimp only [residualSummand, F, t]
    ring
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (zeroCut k)), straight] at total
  simp_rw [split] at total
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, choose_sum_nonzero] at total
  change ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix F).mulVec H) -
    energy H - ((2 : ℝ)^k - 1) * t = _
  linarith

end
end BlockPermanents.PairResidual
