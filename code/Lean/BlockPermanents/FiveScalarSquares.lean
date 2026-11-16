import BlockPermanents.FiveEstimate

/-! The scalar square in (8B.1) and the exact long-cycle squares of Lemma 8C.1. -/
namespace BlockPermanents.FiveScalarSquares
open Closures Bend FiveCycles FiveEstimate
open scoped ComplexConjugate
noncomputable section

/-- Multiply the manuscript's square by d before taking the squared modulus,
and divide by d afterwards. This avoids choosing a square root in coordinates. -/
def scalarSquare (d b l m : ℝ) (g x t : ℂ) : ℝ :=
  Complex.normSq ((d : ℂ) * (g + (b : ℂ) * x + t) - ((l : ℂ) * g + (m : ℂ) * x)) / d

theorem scalar_resolution (d b l m : ℝ) (hd : 0 < d) (g x t : ℂ) :
    d * Complex.normSq (g + (b : ℂ)*x + t) =
      (2*l-l^2/d)*Complex.normSq g + (2*b*m-m^2/d)*Complex.normSq x +
      2*(b*l+m-l*m/d)*(star g*x).re + 2*(star ((l:ℂ)*g+(m:ℂ)*x)*t).re +
      scalarSquare d b l m g x t := by
  simp only [scalarSquare, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp [hd.ne']
  ring

open private straight fourExit fiveExit from BlockPermanents.FiveCycles

/-- The two distinct exits of the four- and five-cycles. -/
def fourSquare (g : Gram) : ℝ := avg fun σ => Complex.normSq (straight g σ - fourExit g σ)

def fiveSquare (g : Gram) : ℝ := avg fun σ => Complex.normSq (straight g σ - 2 * fiveExit g σ)

private theorem scaled_difference (a b : ℂ) (h : ℝ) :
    Complex.normSq (a - (h : ℂ)*b) =
      Complex.normSq a + h^2 * Complex.normSq b - (2*h) * (conj a * b).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

open private straight_norm four_norm five_norm from BlockPermanents.FiveCycles in
/-- The two inequalities of Lemma 8C.1 with their full remainders. -/
theorem long_cycle_squares (g : Gram) :
    U g - C4 g = fourSquare g / 2 ∧
    6*U g + 24*V g - 24*C5 g = 6*fiveSquare g := by
  have subAvg (f h : S → ℝ) : avg (fun σ => f σ - h σ) = avg f - avg h := by
    simp [avg, Finset.sum_sub_distrib, mul_sub, sub_div]
  have four (σ) := scaled_difference (straight g σ) (fourExit g σ) 1
  have five (σ) := scaled_difference (straight g σ) (fiveExit g σ) 2
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at four
  simp only [Complex.ofReal_ofNat] at five
  constructor
  · simp only [fourSquare,four,subAvg,avg_add,avg_mul_left,straight_norm,four_norm,C4]
    ring
  · simp only [fiveSquare,five,subAvg,avg_add,avg_mul_left,straight_norm,five_norm,C5]
    ring

open private rotate exchange from BlockPermanents.FiveEstimate in
/-- After subtracting the coarse permanent, the two signed triangle means
cancel. The three printed positive moment coefficients and both cycle
squares remain. -/
theorem coarse_difference (g : Gram) (hd : ∀ i, g i i = 1) (hc : ∀ i j, conj (g i j) = g j i) :
    avg (scalarWeight g) - g.permanent.re =
      11776/2009 * P g + 73895/247408 * U g + 47/164 * V g +
      15 * fourSquare g + 6 * fiveSquare g := by
  have hs : avg (fun σ => p g σ 1 2) = P g := by
    simpa only [P,p,edge,Equiv.Perm.mul_apply, show rotate 0 = 1 by decide,
      show rotate 1 = 2 by decide] using avg_relabel rotate (fun σ => p g σ 0 1)
  have ht : avg (fun σ => p g σ 3 4) = P g := by
    simpa only [P,p,edge,Equiv.Perm.mul_apply, show exchange 0 = 3 by decide,
      show exchange 1 = 4 by decide] using avg_relabel exchange (fun σ => p g σ 0 1)
  have hu : avg (fun σ => p g σ 3 4 * p g σ 1 2) = U g := by
    simpa only [U,p,edge,Equiv.Perm.mul_apply, show rotate 0 = 1 by decide,
      show rotate 1 = 2 by decide, show rotate 3 = 3 by decide, show rotate 4 = 4 by decide] using
        avg_relabel rotate (fun σ => p g σ 3 4*p g σ 0 1)
  have avP : avg (fun σ => p g σ 0 1) = P g := rfl
  have avU : avg (fun σ => p g σ 3 4*p g σ 0 1) = U g := rfl
  have avV : avg (fun σ => p g σ 3 4*Complex.normSq (viaH g σ)) = V g := rfl
  have avT : avg (tri g) = theta g := rfl
  have avT' : avg (fun σ => p g σ 3 4*tri g σ) = thetaPair g := rfl
  rw [permanent_cycles g hd hc]
  change avg (fun σ => scalarWeight g σ) - _ = _
  simp only [scalarWeight,avg_add,avg_mul_left,avg_const,hs,ht,hu,avP,avU,avV,avT,avT']
  obtain ⟨h4,h5⟩ := long_cycle_squares g
  dsimp only [a₀,a₁,a₂,l₀,l₁,m₁,d₀]
  linarith only [h4,h5]

end
end BlockPermanents.FiveScalarSquares
