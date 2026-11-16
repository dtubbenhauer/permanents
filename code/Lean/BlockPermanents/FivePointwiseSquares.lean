import BlockPermanents.FiveScalarSquares
import BlockPermanents.FiveMixedAverageSquares

/-! Retain both scalar squares before averaging over the five packet labels. -/
namespace BlockPermanents.FiveScalarSquares
open Closures Bend FiveProjection FiveCycles FiveEstimate FiveMixedAverageSquares
noncomputable section

def scalarTests (g : Gram) (σ : S) (t : ℂ) : ℝ :=
  scalarSquare d₀ 7 l₀ 0 (edge g σ 0 1) (viaH g σ) t +
    7*p g σ 3 4 * scalarSquare d₀ 7 l₁ m₁ (edge g σ 0 1) (viaH g σ) t

def testSquares {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : S) : ℝ :=
  let F i := packet (x i)
  scalarTests (crossGram F F) σ (remainders x (σ 2) (σ 0) (σ 1))

theorem testSquares_nonneg {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : S) :
    0 ≤ testSquares x σ := by
  unfold testSquares scalarTests scalarSquare
  exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) (by norm_num [d₀]))
    (mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
      (div_nonneg (Complex.normSq_nonneg _) (by norm_num [d₀])))

theorem two_test_resolution (g : Gram) (σ : S) (t : ℂ) (tD : ℝ) :
    (1+7*p g σ 3 4)*(1+7*p g σ 1 2+tD+d₀*Complex.normSq (edge g σ 0 1+7*viaH g σ+t)) =
      scalarWeight g σ + (tD+2*(star ((l₀:ℂ)*edge g σ 0 1)*t).re) +
      (7*p g σ 3 4)*(tD+2*(star ((l₁:ℂ)*edge g σ 0 1+(m₁:ℂ)*viaH g σ)*t).re) +
      scalarTests g σ t := by
  let z := edge g σ 0 1
  let v := viaH g σ
  have h₀ := scalar_resolution d₀ 7 l₀ 0 (by norm_num [d₀]) z v t
  have h₁ := congrArg ((7*p g σ 3 4) * ·) (scalar_resolution d₀ 7 l₁ m₁ (by norm_num [d₀]) z v t)
  simp only [Complex.ofReal_zero, Complex.ofReal_ofNat, zero_mul, add_zero] at h₀ h₁
  unfold scalarWeight scalarTests tri
  change (1+7*p g σ 3 4)*(1+7*p g σ 1 2+tD+d₀*Complex.normSq (z+7*v+t)) =
    1+7*p g σ 1 2+7*p g σ 3 4+49*(p g σ 3 4*p g σ 1 2)+
    a₀*Complex.normSq z+20*(star z*v).re+a₁*(p g σ 3 4*Complex.normSq z)+
    a₂*(p g σ 3 4*Complex.normSq v)+20*(p g σ 3 4*(star z*v).re)+_+_+_
  dsimp only [a₀,a₁,a₂,l₀,l₁,m₁,d₀] at *
  linear_combination h₀ + h₁

/-- Apply both scalar tests to the same assignment of actual Gram packets.
The triangle keeps its phase in each test. -/
theorem packet_tests {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ)
    (hu : ∀ i, energy (packet (x i)) = 1) (σ : S) :
    let X i := packet (x i)
    let g := crossGram X X
    let H := X (σ 2)
    let F := X (σ 1)
    let G := X (σ 0)
    (1+7*p g σ 3 4)*((pairGram H F F).re + 41/20*Complex.normSq (pairGram H G F)) =
      scalarWeight g σ + FiveAverage.residual (tests x l₀ 0) (remainders x) σ +
      7*p g σ 3 4 * FiveAverage.residual (tests x l₁ m₁) (remainders x) σ + testSquares x σ := by
  dsimp only
  let X i := packet (x i)
  let g := crossGram X X
  let H := X (σ 2)
  let t := remainders x (σ 2) (σ 0) (σ 1)
  let td := (remainders x (σ 2) (σ 1) (σ 1)).re
  have diag : (pairGram H (X (σ 1)) (X (σ 1))).re = 1 + 7*p g σ 1 2 + td := by
    have h := remainder_diagonal H X hu (σ 1)
    change td = _ - 1 - 7*p g σ 1 2 at h
    linarith
  have off : pairGram H (X (σ 0)) (X (σ 1)) = edge g σ 0 1 + 7*viaH g σ + t := by
    dsimp [t,remainders,H,X,g,edge,viaH,remainderForm,crossGram]
    ring
  have y0 : tests x l₀ 0 (σ 2) (σ 0) (σ 1) = (l₀:ℂ)*edge g σ 0 1 := by
    simp [tests,testForm,edge,g,crossGram,X]
  have y1 : tests x l₁ m₁ (σ 2) (σ 0) (σ 1) = (l₁:ℂ)*edge g σ 0 1+(m₁:ℂ)*viaH g σ := by
    simp [tests,testForm,edge,g,crossGram,viaH,X,mul_assoc]
  rw [diag,off]
  simpa only [FiveAverage.residual,y0,y1] using two_test_resolution g σ t td

end
end BlockPermanents.FiveScalarSquares
