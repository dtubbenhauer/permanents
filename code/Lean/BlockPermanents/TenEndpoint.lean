import BlockPermanents.CycleTen
import BlockPermanents.FiveProjection
import BlockPermanents.PacketScale
import BlockPermanents.MatchingThreshold

/-! The ten-block example of Appendix A, on arbitrary complex PSD matrices. -/
namespace BlockPermanents.TenEndpoint
open CycleMatching CyclePolynomial CycleTen Closures Bend SchurNormalization
noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem coefficients_fit : ∀ j : Fin 6, coeff fullPolynomial j ≤ ((5:ℕ).choose j : ℚ)*31^j.val := by
  decide +kernel

/-- A matching upper bound on all unit Grams yields the matrix inequality
whenever the fine matching coefficients dominate it, degree by degree. -/
theorem unit_of_matching_bound {m k d : ℕ} (c : ℕ → ℚ)
    (bound : ∀ g : Gram m, UnitGram g → (Matrix.permanent g).re ≤
      ∑ j ∈ Finset.range (m/2+1), (c j:ℝ)*Z g j)
    (fit : ∀ j ∈ Finset.range (m/2+1), (c j : ℝ) ≤ ((m/2).choose j:ℝ)*((2:ℝ)^k-1)^j)
    (schur : ∀ p q, HomogeneousSchur d p q) (x : Fin m → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      MatchingFine.fine (Function.uncurry x) := by
  let F := fun i => packet (x i)
  let g := crossGram F F
  have hg : UnitGram g := by
    constructor
    · intro i; simp [g,F,crossGram,Coarse.bracket_self,hu]
    · intro i j; simp [g,F,crossGram,bracket,star_sum,star_mul',mul_comm]
    · intro i j
      simpa [sqEdge,g,F,crossGram,hu] using FiveProjection.bracket_bound (packet (x i)) (packet (x j))
  have hc := bound g hg
  have hf := MatchingFine.average_fine_bound schur x
  simp only [hu] at hf
  apply hc.trans (le_trans (Finset.sum_le_sum ?_) hf)
  intro j hj
  exact mul_le_mul_of_nonneg_right (fit j hj) (CycleComposition.Z_nonneg _ _)

theorem unit_ten {k d : ℕ} (hk : 5 ≤ k) (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 10 → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      MatchingFine.fine (Function.uncurry x) := by
  apply unit_of_matching_bound _ ten_cycle_bound _ schur x hu
  intro j hj
  have hsmall : (coeff fullPolynomial j:ℝ) ≤ ((5:ℕ).choose j:ℝ) * 31^j := by
    exact_mod_cast coefficients_fit (⟨j,Finset.mem_range.mp hj⟩ : Fin 6)
  apply hsmall.trans (mul_le_mul_of_nonneg_left _ (by positivity))
  apply pow_le_pow_left₀ (by norm_num)
  have hp : (2:ℝ)^5 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hp
  linarith

/-- Ten blocks of any size k ≥ 5, singular PSD inputs included. -/
theorem marcus_ten {k : ℕ} (hk : 5 ≤ k) (schur : ∀ p q, HomogeneousSchur (10*k) p q) :
    MarcusAt 10 k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by omega) (unit_ten hk schur))

set_option maxRecDepth 100000 in
private theorem coeff_six : ∀ j : Fin 4,
    coeff (matchedPolynomial 6) j ≤ ((3:ℕ).choose j : ℚ)*15^j.val := by decide +kernel

/-- Six blocks of thickness at least four, from the actual alternating
cycle cuts and the normalized disjoint-pair lower bound. -/
theorem marcus_six {k : ℕ} (hk : 4 ≤ k) (schur : ∀ p q, HomogeneousSchur (6*k) p q) :
    MarcusAt 6 k := by
  apply MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by omega) ?_)
  intro x hx
  apply unit_of_matching_bound _ six_cycle_bound _ schur x hx
  intro j hj
  have hsmall : (coeff (matchedPolynomial 6) j : ℝ) ≤ ((3:ℕ).choose j:ℝ) * 15^j := by
    exact_mod_cast coeff_six (⟨j,Finset.mem_range.mp hj⟩ : Fin 4)
  apply hsmall.trans (mul_le_mul_of_nonneg_left _ (by positivity))
  apply pow_le_pow_left₀ (by norm_num)
  have hp : (2:ℝ)^4 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hp
  linarith

end
end BlockPermanents.TenEndpoint
