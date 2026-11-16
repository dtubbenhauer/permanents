import BlockPermanents.FiveCycles
import BlockPermanents.FiveMixed

/-! # From the two mixed gluings to the coarse five-packet permanent -/
namespace BlockPermanents.FiveEstimate
open FiveCycles
open scoped ComplexConjugate
noncomputable section

abbrev l₀ : ℝ := 10/7
abbrev l₁ : ℝ := 451/2632
abbrev m₁ : ℝ := 1/4
abbrev d₀ : ℝ := 41/20
abbrev a₀ : ℝ := 2*l₀-l₀^2/d₀
abbrev a₁ : ℝ := 7*(2*l₁-l₁^2/d₀)
abbrev a₂ : ℝ := 7*(14*m₁-m₁^2/d₀)

def p (g : Gram) (σ : S) (i j : Fin 5) : ℝ := Complex.normSq (edge g σ i j)
def tri (g : Gram) (σ : S) : ℝ := (conj (edge g σ 0 1)*viaH g σ).re

def scalarWeight (g : Gram) (σ : S) : ℝ :=
  1+7*p g σ 1 2+7*p g σ 3 4+49*(p g σ 3 4*p g σ 1 2)+
  a₀*p g σ 0 1+20*tri g σ+a₁*(p g σ 3 4*p g σ 0 1)+
  a₂*(p g σ 3 4*Complex.normSq (viaH g σ))+20*(p g σ 3 4*tri g σ)

private def rotate : S := Equiv.swap 0 1 * Equiv.swap 1 2
private def exchange : S := Equiv.swap 0 3 * Equiv.swap 1 4

theorem permanent_le_mean (g : Gram) (hd : ∀ i, g i i = 1) (hc : ∀ i j, conj (g i j) = g j i) :
    g.permanent.re ≤ avg (scalarWeight g) := by
  have hs : avg (fun σ => p g σ 1 2) = P g := by
    simpa only [P,p,edge,Equiv.Perm.mul_apply, show rotate 0 = 1 by decide,
      show rotate 1 = 2 by decide] using avg_relabel rotate (fun σ => p g σ 0 1)
  have ht : avg (fun σ => p g σ 3 4) = P g := by
    simpa only [P,p,edge,Equiv.Perm.mul_apply, show exchange 0 = 3 by decide,
      show exchange 1 = 4 by decide] using avg_relabel exchange (fun σ => p g σ 0 1)
  have hu : avg (fun σ => p g σ 3 4 * p g σ 1 2) = U g := by
    simpa only [U,p,edge,Equiv.Perm.mul_apply, show rotate 0 = 1 by decide,
      show rotate 1 = 2 by decide, show rotate 3=3 by decide, show rotate 4=4 by decide] using
        avg_relabel rotate (fun σ => p g σ 3 4*p g σ 0 1)
  have avP : avg (fun σ => p g σ 0 1) = P g := rfl
  have avU : avg (fun σ => p g σ 3 4*p g σ 0 1) = U g := rfl
  have avV : avg (fun σ => p g σ 3 4*Complex.normSq (viaH g σ)) = V g := rfl
  have avT : avg (tri g) = theta g := rfl
  have avT' : avg (fun σ => p g σ 3 4*tri g σ) = thetaPair g := rfl
  have nn {f : S → ℝ} (hf : ∀ s, 0 ≤ f s) : 0 ≤ avg f :=
    (avg_const 0).symm.trans_le (avg_mono hf)
  have pp : 0 ≤ P g := nn (fun _ => Complex.normSq_nonneg _)
  have pu : 0 ≤ U g := nn (fun _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  have pv : 0 ≤ V g := nn (fun _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  obtain ⟨h₄,h₅⟩ := long_cycles g
  rw [permanent_cycles g hd hc]
  change _ ≤ avg (fun σ => scalarWeight g σ)
  simp only [scalarWeight,avg_add,avg_mul_left,avg_const,hs,ht,hu,avP,avU,avV,avT,avT']
  have h := FiveMixed.coefficient_balance (P g) (U g) (V g) (theta g) (thetaPair g) (C4 g) (C5 g) h₄ h₅
  dsimp [a₀,a₁,a₂,l₀,l₁,m₁,d₀] at *
  linarith

/-- Both completed squares combined pointwise. Averaging the last two terms
recovers the nonnegative residual trace from the choices q=4 and q=2. -/
theorem two_tests (g : Gram) (σ : S) (t : ℂ) (tD : ℝ) (N : ℝ)
    (h : (1+7*p g σ 3 4)*(1+7*p g σ 1 2+tD+
      d₀*Complex.normSq (edge g σ 0 1+7*viaH g σ+t)) ≤ N) :
    scalarWeight g σ +
    (tD+2*(star ((l₀:ℂ)*edge g σ 0 1)*t).re) +
    (7*p g σ 3 4)*(tD+2*(star ((l₁:ℂ)*edge g σ 0 1+(m₁:ℂ)*viaH g σ)*t).re) ≤ N := by
  let z := edge g σ 0 1
  let x := viaH g σ
  have s₀ := FiveMixed.subtract_square d₀ 7 l₀ 0 (by norm_num [d₀]) z x t
  have s₁ := FiveMixed.subtract_square d₀ 7 l₁ m₁ (by norm_num [d₀]) z x t
  have w := mul_le_mul_of_nonneg_left s₁ (show 0 ≤ 7*p g σ 3 4 by exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  simp only [Complex.ofReal_zero, zero_mul,add_zero,Complex.ofReal_ofNat] at s₀ w
  change _*(1+7*p g σ 1 2+tD+d₀*Complex.normSq (z+7*x+t)) ≤ N at h
  simp only [scalarWeight,tri]
  change 1+7*p g σ 1 2+7*p g σ 3 4+49*(p g σ 3 4*p g σ 1 2)+
    a₀*Complex.normSq z+20*(star z*x).re+a₁*(p g σ 3 4*Complex.normSq z)+
    a₂*(p g σ 3 4*Complex.normSq x)+20*(p g σ 3 4*(star z*x).re)+_+_ ≤ N
  dsimp only [a₀,a₁,a₂,l₀,l₁,m₁,d₀] at *
  linarith only [h,s₀,w]

end
end BlockPermanents.FiveEstimate
