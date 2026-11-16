import BlockPermanents.FiveOuter
import BlockPermanents.FiveEstimate
import BlockPermanents.FiveAverage
import BlockPermanents.MatchingThreshold

/-! # Five packets of thickness at least three, Theorem 8A.1 -/
namespace BlockPermanents.FiveMain
open Closures Bend FiveCycles FiveProjection FiveEstimate FiveAverage MatchingFine SchurNormalization
open scoped ComplexConjugate ComplexOrder
noncomputable section

theorem unit_five {d k : ℕ} (hk : 3 ≤ k) (schur : ∀ a b, HomogeneousSchur d a b)
    (x : Fin 5 → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤ fine (Function.uncurry x) := by
  let F i := packet (x i)
  let g := crossGram F F
  let T h := remainderForm (F h) F
  let Y l m h := testForm l m (F h) F
  let w i j := 7*Complex.normSq (g i j)
  have psd (h) : (T h).PosSemidef := remainder_posSemidef hk (schur _ _) _ ⟨1,x h,by simp [F]⟩
    (hu h) _ (fun i => Bridges.packet_symmetric _ _ _)
  have yr (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (h) : (Y l m h).PosSemidef :=
    test_posSemidef l m hl hm (F h) F
  have cap (l m : ℝ) (hm : 0 ≤ m) (h i) : ((Y l m h) i i).re ≤ l+m :=
    test_diagonal_le l m hm _ (hu h) _ hu i
  have mean₀ := plain (Y l₀ 0) T (yr l₀ 0 (by norm_num [l₀]) le_rfl) psd
    (fun h i => (cap l₀ 0 le_rfl h i).trans (by norm_num [l₀]))
  have mean₁ := weighted (Y l₁ m₁) T (yr l₁ m₁ (by norm_num [l₁]) (by norm_num [m₁])) psd
    (fun h i => (cap l₁ m₁ (by norm_num [m₁]) h i).trans (by norm_num [l₁,m₁])) w
    (fun i j => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have upper (σ : S) : scalarWeight g σ + FiveAverage.residual (Y l₀ 0) T σ +
      w (σ 3) (σ 4)*FiveAverage.residual (Y l₁ m₁) T σ ≤ fine (Function.uncurry x) := by
    let t := T (σ 2) (σ 0) (σ 1)
    let td := (T (σ 2) (σ 1) (σ 1)).re
    have diag : (pairGram (F (σ 2)) (F (σ 1)) (F (σ 1))).re = 1+7*p g σ 1 2+td := by
      have h := remainder_diagonal (F (σ 2)) F hu (σ 1)
      change td = _-1-7*p g σ 1 2 at h
      linarith
    have off : pairGram (F (σ 2)) (F (σ 0)) (F (σ 1)) = edge g σ 0 1+7*viaH g σ+t := by
      dsimp [edge,viaH,t,T,g,crossGram,remainderForm]
      ring
    have ho := FiveOuter.outer hk schur x hu σ
    change (1+7*p g σ 3 4)*((pairGram (F (σ 2)) (F (σ 1)) (F (σ 1))).re+
      d₀*Complex.normSq (pairGram (F (σ 2)) (F (σ 0)) (F (σ 1)))) ≤ _ at ho
    rw [diag,off] at ho
    have v := two_tests g σ t td _ ho
    have y0 : Y l₀ 0 (σ 2) (σ 0) (σ 1) = (l₀:ℂ)*edge g σ 0 1 := by simp [Y,testForm,edge,g,crossGram]
    have y1 : Y l₁ m₁ (σ 2) (σ 0) (σ 1) = (l₁:ℂ)*edge g σ 0 1+(m₁:ℂ)*viaH g σ := by
      simp [Y,testForm,edge,g,crossGram,viaH,mul_assoc]
    simpa only [FiveAverage.residual,y0,y1] using v
  have hz := avg_mono upper
  rw [avg_add,avg_add,avg_const] at hz
  have hd (i) : g i i = 1 := by simp [g,crossGram,Coarse.bracket_self,F,hu]
  have hc (i j) : conj (g i j) = g j i := by simp [g,crossGram,bracket,map_sum,mul_comm]
  have h := permanent_le_mean g hd hc
  change g.permanent.re ≤ _
  linarith

/-- The five-packet theorem on the original PSD matrix, including singular
matrices and zero packets, with exactly the external Schur input. -/
theorem marcus_five {k : ℕ} (hk : 3 ≤ k) (schur : ∀ p q, HomogeneousSchur (5*k) p q) :
    MarcusAt 5 k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by omega) (unit_five hk schur))

end
end BlockPermanents.FiveMain
