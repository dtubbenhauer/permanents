import BlockPermanents.PairSquares
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The two mixed gluings in Section 8B

The labels need not give distinct vectors. Their distinctness in the sum is
distinctness of positions. -/
namespace BlockPermanents.FiveMixed
open scoped BigOperators Matrix ComplexOrder
open Closures Bend
noncomputable section

/-- Including equal labels gives the Hilbert–Schmidt pairing of two positive
forms. Factoring the first form expresses this pairing as a sum of positive
quadratic evaluations of the second. -/
theorem sum_mixed_nonneg {I : Type*} [Fintype I]
    {Y T : Matrix I I ℂ} (hY : Y.PosSemidef) (hT : T.PosSemidef) :
    0 ≤ ∑ i, ∑ j, (star (Y i j) * T i j).re := by
  obtain ⟨B,rfl⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hY
  have eqn : (∑ i, ∑ j, star ((Bᴴ * B) i j) * T i j) =
      ∑ a, dotProduct (star (fun i => star (B a i))) (T.mulVec (fun j => star (B a j))) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', star_star,
      Finset.sum_mul, Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
    conv_lhs => enter [2,i]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := congrArg Complex.re eqn
  simp only [Complex.re_sum] at h
  rw [h]
  exact Finset.sum_nonneg (fun a _ => hT.re_dotProduct_nonneg _)

/-- The first inequality of Lemma 8B.3, for arbitrary positive forms. -/
theorem mixed_trace {I : Type*} [Fintype I] [DecidableEq I]
    {Y T : Matrix I I ℂ} (hY : Y.PosSemidef) (hT : T.PosSemidef) :
    (∑ i, (((Fintype.card I : ℝ) - 1) * (T i i).re -
        2 * (star (Y i i) * T i i).re)) ≤
    ∑ i, ∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y i j) * T i j).re) := by
  classical
  by_cases e : IsEmpty I
  · letI := e
    simp
  haveI : Nonempty I := not_isEmpty_iff.mp e
  have card_eq : ((Fintype.card I - 1 : ℕ) : ℝ) = (Fintype.card I : ℝ) - 1 := by
    rw [Nat.cast_sub (Fintype.card_pos (α := I)), Nat.cast_one]
  have h := sum_mixed_nonneg hY hT
  have row (i : I) : (∑ j ∈ Finset.univ.erase i,
          ((T i i).re + 2 * (star (Y i j) * T i j).re)) =
      (((Fintype.card I : ℝ) - 1) * (T i i).re - 2 * (star (Y i i) * T i i).re) +
      2 * ∑ j, (star (Y i j) * T i j).re := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, nsmul_eq_mul, card_eq, ← Finset.mul_sum,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  simp_rw [row]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

/-- The pointwise subtraction of the square in equation (five-scalar). -/
theorem subtract_square (d b l m : ℝ) (hd : 0 < d) (g x t : ℂ) :
    (2*l-l^2/d)*Complex.normSq g + (2*b*m-m^2/d)*Complex.normSq x +
    2*(b*l+m-l*m/d)*(star g*x).re + 2*(star ((l:ℂ)*g+(m:ℂ)*x)*t).re ≤
    d * Complex.normSq (g+(b:ℂ)*x+t) := by
  have hs := Complex.normSq_nonneg ((d:ℂ)*(g+(b:ℂ)*x+t)-((l:ℂ)*g+(m:ℂ)*x))
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at *
  field_simp [hd.ne'] 
  apply (div_le_iff₀ hd).2
  nlinarith only [hs]

/-- The rational parameters preserve both triangle terms and leave positive
coefficients for the three unsigned moments (end of Section 8C). -/
theorem coefficient_balance (P U V θ θ' C₄ C₅ : ℝ) 
    (h₄ : C₄ ≤ U) (h₅ : 24*C₅ ≤ 6*U+24*V) :
    let b : ℝ := 7
    let d : ℝ := 41/20
    let l₀ : ℝ := 10/7
    let l₁ : ℝ := 451/2632
    let m₁ : ℝ := 1/4
    1+10*P+15*U+20*θ+20*θ'+30*C₄+24*C₅ +
      11776/2009*P + 73895/247408*U + 47/164*V ≤
    1+2*b*P+b^2*U + (2*l₀-l₀^2/d)*P+2*(b*l₀)*θ +
    b*((2*l₁-l₁^2/d)*U+(2*b*m₁-m₁^2/d)*V+2*(b*l₁+m₁-l₁*m₁/d)*θ') := by
  dsimp
  linarith

end
end BlockPermanents.FiveMixed
