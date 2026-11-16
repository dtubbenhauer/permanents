import BlockPermanents.CycleParameters
import BlockPermanents.RawCycleClass

/-! # Six labels with a triangle, a transposition and a fixed point, Appendix AC -/
namespace BlockPermanents.SixCycleExample
open CycleMatching CycleComposition CyclePolynomial CycleParameters CyclePlans RawCycleSquares
noncomputable section

/-- The sole fixed point is assigned to the three-cycle. -/
def pieces : List Piece := [.odd 0 1, .even 0]

theorem triangle_score (z : ℝ) :
    score [.odd 0 1] (fun _ => 3/2) (fun j => z^j) 0 = z*(17/24+z/3) := by
  norm_num [score]
  ring

theorem transposition_score (z : ℝ) :
    score [.even 0] (fun _ => 3/2) (fun j => z^j) 0 = z := by norm_num [score]

/-- Coefficients of the product applied to arbitrary real matching moments. -/
theorem product_score (F : ℕ → ℝ) :
    score pieces (fun _ => 3/2) F 0 = (17/24)*F 2 + F 3/3 := by
  norm_num [pieces, score]
  ring

theorem polynomial (z : ℝ) :
    score pieces (fun _ => 3/2) (fun j => z^j) 0 = 17*z^2/24 + z^3/3 := by
  rw [product_score]
  ring

/-- Cardinality of the actual permutation fiber in S₆. -/
theorem class_card : (classSet 6 ({3,2} : Multiset ℕ)).card = 120 := by
  rw [classSet, Equiv.Perm.card_of_cycleType]
  decide

/-- The normalized estimate for any representative of the 120-element class. -/
theorem class_estimate (τ : S 6) (hτ : τ.cycleType = {3,2}) (g : Gram 6) (hg : UnitGram g) :
    |(mean g τ).re| ≤ (17/24)*Z g 2 + Z g 3/3 := by
  have hb := CycleParameters.class_bound pieces (fun _ => 3/2) (fun _ => by norm_num) τ hτ g hg
  rwa [product_score] at hb

/-- The unnormalized contribution sums the 120 actual permutation monomials. -/
theorem class_sum_estimate (g : Gram 6) (hg : UnitGram g) :
    |(classSum g {3,2}).re| ≤ 120*((17/24)*Z g 2 + Z g 3/3) := by
  obtain ⟨τ, hτ⟩ := Finset.card_pos.mp (show 0 < (classSet 6 {3,2}).card by rw [class_card]; decide)
  have he : τ.cycleType = {3,2} := (Finset.mem_filter.mp hτ).2
  have hc := class_average g τ
  rw [he, class_card] at hc
  rw [hc]
  norm_num [Complex.mul_re, abs_mul]
  exact class_estimate τ he g hg

end
end BlockPermanents.SixCycleExample
