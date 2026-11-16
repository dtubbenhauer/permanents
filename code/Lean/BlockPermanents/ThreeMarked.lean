import BlockPermanents.ThreeEvaluation
import BlockPermanents.ThreeWireGlue
import BlockPermanents.ThreeEndpoint

/-! # Positivity of the marked six-wire correction -/
namespace BlockPermanents.ThreeMarked
open ThreeWire ThreeWireGlue ThreeEndpoint Closures

theorem correction_nonneg {d : ℕ} (x y z : Fin 2 → Fin d → ℂ) :
    0 ≤ (evalTerms (evaluateWord (boundary (packet x) (packet y) (packet z))) correctionTerms).re := by
  let F := packet x
  let G := packet y
  let H := packet z
  let f := evaluateWord (boundary F G H)
  have h₁ := pair_estimate F G z (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)
  have h₂ := thin_positive F G H fourList valid_four
  have h₃ := full_difference_positive F G H fourList pairList valid_four valid_pair
  change 0 ≤ 8 * (glue f pairList thinSwap pairList).re - 9/4 * (glue f pairList fullSwap pairList).re at h₁
  change 0 ≤ (glue f fourList thinSwap fourList).re at h₂
  change 0 ≤ (glue f fourList fullSwap fourList - glue f fourList fullSwap pairList -
    glue f pairList fullSwap fourList + glue f pairList fullSwap pairList).re at h₃
  change 0 ≤ (evalTerms f correctionTerms).re
  rw [correction_eval, Complex.sub_re, Complex.add_re, Complex.add_re]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

theorem cyclic_nonneg {d : ℕ} (x : Fin 3 → Fin 2 → Fin d → ℂ) :
    0 ≤ (evalTerms (evaluateWord (bdy (fun i => packet (x i)))) cyclicTerms).re := by
  rw [cyclic_evaluation]
  change 0 ≤ Complex.reAddGroupHom (∑ p : Equiv.Perm (Fin 3), evalTerms (evaluateWord (bdy ((fun i => packet (x i)) ∘ p))) correctionTerms)
  rw [map_sum]
  apply Finset.sum_nonneg
  intro p _
  exact correction_nonneg (x (p 0)) (x (p 1)) (x (p 2))

end BlockPermanents.ThreeMarked
