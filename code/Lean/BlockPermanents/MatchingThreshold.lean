import BlockPermanents.MatchingFine
import BlockPermanents.Threshold
import BlockPermanents.MatchingUpper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Passing from matching estimates to the block-matrix inequality

We retain all packet energies, including zero. A Gram factorization therefore
gives the conclusion directly for every PSD input, without normalizing columns.
-/
namespace BlockPermanents.MatchingThreshold
open Closures SchurNormalization
open scoped BigOperators ComplexOrder
noncomputable section

/-- Squared energy and pair weights of the normalized clasp images. -/
def packetEnergy {m k d : ℕ} (x : Fin m → Fin k → Fin d → ℂ) (i : Fin m) : ℝ :=
  Bend.energy (packet (x i))

def capWeight {m k d : ℕ} (x : Fin m → Fin k → Fin d → ℂ) (i j : Fin m) : ℝ :=
  Complex.normSq (bracket (packet (x i)) (packet (x j)))

private theorem weighted_lower {m k d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin m → Fin k → Fin d → ℂ)
    (h : m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1)) :
    ∑ r ∈ Finset.range (m/2+1), (Threshold.pathCoeff m r : ℝ) *
      Matchings.moment m r (packetEnergy x) (capWeight x) ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re := by
  have hn (r : ℕ) : 0 ≤ Matchings.moment m r (packetEnergy x) (capWeight x) :=
    Matchings.moment_nonneg (fun _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (fun _ _ => Complex.normSq_nonneg _)
  have hc := Threshold.matching_sum_le m k _ hn h
  have hl := MatchingFine.average_fine_bound schur x
  have hb : (((2^k - 1 : ℕ) : ℕ) : ℝ) = (2:ℝ)^k - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow k 2 (by decide)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simp only [Nat.cast_mul, Nat.cast_pow, hb] at hc
  exact hc.trans hl

/-- The coarse matrix is the actual Gram matrix of the packets in any dimension. -/
theorem coarseGram {m k d : ℕ} (x : Fin m → Fin k → Fin d → ℂ) :
    blockPermanentMatrix (crossGram (Function.uncurry x) (Function.uncurry x)) =
      crossGram (fun i => packet (x i)) (fun i => packet (x i)) := by
  funext i j
  exact (packet_gram (x i) (x j)).symm

private theorem real_gram {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (x : I → D → ℂ) : (crossGram x x).permanent = ((crossGram x x).permanent.re : ℂ) := by
  rw [← packet_gram, Coarse.bracket_self, Complex.ofReal_re]

/-- For a theorem at fixed m and k it is enough to compare the two Gram
permanents on m*k-dimensional column vectors. -/
theorem marcusAt_of_gram {m k : ℕ}
    (h : ∀ x : Fin m → Fin k → Fin (m*k) → ℂ,
      (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
        (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re) : MarcusAt m k := by
  intro A hA
  obtain ⟨B,hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  let e : Fin m × Fin k ≃ Fin (m*k) := finProdFinEquiv
  let x (i : Fin m) (j : Fin k) (t : Fin (m*k)) := B (e.symm t) (i,j)
  let f := Function.uncurry x
  let y := fun i => packet (x i)
  have ha : A = crossGram f f := by
    rw [hB]
    ext i j
    exact (e.symm.sum_comp (fun t => star (B t i) * B t j)).symm
  rw [ha, coarseGram x]
  refine ⟨_, sub_nonneg.mpr (h x), ?_⟩
  rw [Complex.ofReal_sub, ← real_gram f, ← real_gram y]

/-- The natural power comparison is equivalent to the manuscript's real
logarithmic sufficient condition. -/
theorem square_le_pow_iff_log {m k : ℕ} (hm : 0 < m) :
    m^2 ≤ 2^k ↔ 2 * Real.logb 2 m ≤ k := by
  have hm' : 0 < (m : ℝ)^2 := by positivity
  have he := Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (y := (k:ℝ)) hm'
  rw [Real.rpow_natCast, Real.logb_pow] at he
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  exact_mod_cast Iff.rfl

/-- The matching method applied to the actual two Gram permanents at arbitrary
packet number, thickness, and ambient dimension. -/
theorem gram_threshold {m k d : ℕ} (h : m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1))
    (schur : ∀ p q, HomogeneousSchur d p q) (x : Fin m → Fin k → Fin d → ℂ) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re := by
  have lower := weighted_lower schur x h
  have upper := MatchingUpper.permanent_le_upper (fun i => packet (x i))
  simp only [Coarse.bracket_self, Complex.ofReal_re] at upper
  exact upper.trans lower

/-- Theorem 7C.1, on every complex PSD matrix at the stated rational threshold. -/
theorem marcus_threshold {m k : ℕ} (h : m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1))
    (schur : ∀ p q, HomogeneousSchur (m*k) p q) : MarcusAt m k :=
  marcusAt_of_gram (gram_threshold h schur)

/-- The logarithmic sufficient condition, in base two and with real logarithm. -/
theorem marcus_logarithmic {m k : ℕ} (hm : 2 ≤ m) (hk : 2 * Real.logb 2 m ≤ k)
    (schur : ∀ p q, HomogeneousSchur (m*k) p q) : MarcusAt m k :=
  marcus_threshold (Threshold.threshold_of_square_le_pow m k hm
    ((square_le_pow_iff_log (by omega : 0 < m)).mpr hk)) schur

/-- At four blocks the coefficientwise matching argument reaches every k ≥ 3. -/
theorem four_blocks {k : ℕ} (hk : 3 ≤ k)
    (schur : ∀ p q, HomogeneousSchur (4*k) p q) : MarcusAt 4 k := by
  apply marcus_threshold _ schur
  have hp : 2^3 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
  norm_num at hp ⊢
  omega

/-- At five blocks the coefficientwise matching argument reaches every k ≥ 4. -/
theorem five_blocks {k : ℕ} (hk : 4 ≤ k)
    (schur : ∀ p q, HomogeneousSchur (5*k) p q) : MarcusAt 5 k := by
  apply marcus_threshold _ schur
  have hp : 2^4 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
  norm_num at hp ⊢
  omega

end
end BlockPermanents.MatchingThreshold
