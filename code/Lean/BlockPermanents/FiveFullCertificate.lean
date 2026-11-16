import BlockPermanents.FiveOuterSquares
import BlockPermanents.FivePointwiseSquares
import BlockPermanents.MatchingThreshold
import BlockPermanents.PacketScale

/-! The five-packet identity with its cuts, mixed exits, and late cycle squares. -/
namespace BlockPermanents.FiveFullCertificate
open Bend Closures MatchingFine FiveCycles FiveEstimate FiveMixedAverageSquares FiveScalarSquares
open scoped ComplexConjugate
noncomputable section

/-- Equation (8B.1), the two applications of Lemma 8B.3, and the seven cycle
classes together express the entire normalized permanent difference. -/
theorem unit_identity {d k : ℕ} (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) :
    let F := fun i => packet (x i)
    let g := crossGram F F
    fine (Function.uncurry x) - g.permanent.re =
      avg (FiveOuterSquares.assignmentRemainder x) + avg (testSquares x) +
      avg (exits x l₀ 0 four) / 12 +
      avg (fun σ => 7 * p g σ 3 4 * exits x l₁ m₁ two σ) / 2 +
      11776/2009 * P g + 73895/247408 * U g + 47/164 * V g +
      15 * fourSquare g + 6 * fiveSquare g := by
  let F := fun i => packet (x i)
  let g := crossGram F F
  let R₀ := FiveAverage.residual (tests x l₀ 0) (remainders x)
  let R₁ := FiveAverage.residual (tests x l₁ m₁) (remainders x)
  let w := fun (i j : Fin 5) => 7 * Complex.normSq (g i j)
  have point (σ : S) :
      fine (Function.uncurry x) =
        scalarWeight g σ + R₀ σ + w (σ 3) (σ 4) * R₁ σ + testSquares x σ +
          FiveOuterSquares.assignmentRemainder x σ := by
    have h := FiveOuterSquares.outer_squares hk x hu σ
    have t := packet_tests x hu σ
    exact h.trans (congrArg (· + FiveOuterSquares.assignmentRemainder x σ) t)
  have mean := congrArg avg (funext point)
  rw [avg_const] at mean
  simp only [avg_add] at mean
  have plain := plain_squares hk x hu l₀ 0 (by norm_num) le_rfl
  have weighted := weighted_squares hk x hu l₁ m₁ (by norm_num) (by norm_num) w
  change avg R₀ = _ at plain
  change avg (fun σ => w (σ 3) (σ 4)*R₁ σ) = _ at weighted
  rw [plain,weighted] at mean
  have hd (i) : g i i = 1 := by simp [g,crossGram,Coarse.bracket_self,F,hu]
  have hc (i j) : conj (g i j) = g j i := by simp [g,crossGram,bracket,map_sum,mul_comm]
  have coarse := coarse_difference g hd hc
  change fine (Function.uncurry x) - g.permanent.re =
      avg (FiveOuterSquares.assignmentRemainder x) + avg (testSquares x) +
      avg (exits x l₀ 0 four) / 12 + avg (fun σ => w (σ 3) (σ 4)*exits x l₁ m₁ two σ)/2 +
      11776/2009 * P g + 73895/247408 * U g + 47/164 * V g +
      15*fourSquare g + 6*fiveSquare g
  linarith only [mean,coarse]

private theorem avg_nonnegative (f : S → ℝ) (h : ∀ σ, 0 ≤ f σ) : 0 ≤ avg f :=
  (avg_const 0).symm.trans_le (avg_mono h)

/-- The five-packet inequality follows by testing each summand of the
full physical certificate. Unit normalization is removed at the matrix endpoint. -/
theorem unit_five {d k : ℕ} (hk : 3 ≤ k) (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      fine (Function.uncurry x) := by
  let F := fun i => packet (x i)
  let g := crossGram F F
  have h₀ := avg_nonnegative _ (FiveOuterSquares.assignmentRemainder_nonneg hk x hu)
  have h₁ := avg_nonnegative _ (testSquares_nonneg x)
  have h₂ := avg_nonnegative _ (exits_nonneg hk x hu l₀ 0 (by norm_num) le_rfl (by norm_num) four)
  have h₃ := avg_nonnegative _ (fun σ => mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) (Complex.normSq_nonneg (edge g σ 3 4)))
    (exits_nonneg hk x hu l₁ m₁ (by norm_num) (by norm_num) (by norm_num) two σ))
  have hp : 0 ≤ P g := avg_nonnegative _ (fun σ => Complex.normSq_nonneg _)
  have hu' : 0 ≤ U g := avg_nonnegative _ (fun σ => mul_nonneg (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _))
  have hv : 0 ≤ V g := avg_nonnegative _ (fun σ => mul_nonneg (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _))
  have h₄ : 0 ≤ fourSquare g := avg_nonnegative _ (fun σ => Complex.normSq_nonneg _)
  have h₅ : 0 ≤ fiveSquare g := avg_nonnegative _ (fun σ => Complex.normSq_nonneg _)
  have cert := unit_identity hk x hu
  change 0 ≤ avg (fun σ => 7 * p g σ 3 4 * exits x l₁ m₁ two σ) at h₃
  change fine (Function.uncurry x) - g.permanent.re =
      avg (FiveOuterSquares.assignmentRemainder x) + avg (testSquares x) + avg (exits x l₀ 0 four)/12 +
      avg (fun σ => 7 * p g σ 3 4 * exits x l₁ m₁ two σ)/2 +
      11776/2009 * P g + 73895/247408 * U g + 47/164 * V g +
      15*fourSquare g + 6*fiveSquare g at cert
  change g.permanent.re ≤ _
  linarith only [cert,h₀,h₁,h₂,h₃,hp,hu',hv,h₄,h₅]

/-- Theorem 8A.1 for all complex PSD inputs, via the explicit five-packet certificate. -/
theorem marcus_five {k : ℕ} (hk : 3 ≤ k) : MarcusAt 5 k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by omega) (unit_five hk))

end
end BlockPermanents.FiveFullCertificate
