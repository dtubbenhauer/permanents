import BlockPermanents.FiveProjection
import BlockPermanents.Quadratic

/-! # Four labels in a packet clasp

A division of the four labels into pairs uses the two internal edge magnitudes
as coefficients in the triangle and four-cycle bounds. Averaging the three
divisions gives the free parameter in Lemma 7D.1.
-/
namespace BlockPermanents.FourTrade
open Closures
open scoped ComplexConjugate
noncomputable section

/-- The six entries in lexicographic edge order. -/
def edges (g : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  Complex.normSq (g 0 1) + Complex.normSq (g 0 2) + Complex.normSq (g 0 3) +
  Complex.normSq (g 1 2) + Complex.normSq (g 1 3) + Complex.normSq (g 2 3)

/-- The three disjoint pairs of edges. -/
def matchings (g : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  Complex.normSq (g 0 1) * Complex.normSq (g 2 3) +
  Complex.normSq (g 0 2) * Complex.normSq (g 1 3) +
  Complex.normSq (g 0 3) * Complex.normSq (g 1 2)

private def polynomial (a b c d e f : ℝ) :=
  1 + a^2+b^2+c^2+d^2+e^2+f^2 + a^2*f^2+b^2*e^2+c^2*d^2 +
  2*(a*b*d+a*c*e+b*c*f+d*e*f) + 2*(a*b*e*f+a*c*d*f+b*c*d*e)

private def normalized (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,a,b,c; a,1,d,e; b,d,1,f; c,e,f,1]

private theorem permanent_polynomial (a b c d e f : ℝ) :
    (normalized a b c d e f).permanent = polynomial a b c d e f := by
  classical
  simp only [Quadratic.permanent_succ, Matrix.permanent_isEmpty, Matrix.of_apply,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
  norm_num [normalized, polynomial, Equiv.swap_apply_def, Fin.succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

private theorem permanent_bound {I : Type*} [Fintype I] [DecidableEq I] (g : Matrix I I ℂ) :
    g.permanent.re ≤ (Matrix.of fun i j => ‖g i j‖).permanent := by
  classical
  simp only [Matrix.permanent, Matrix.of_apply, Complex.re_sum]
  apply Finset.sum_le_sum
  intro σ _
  simpa only [norm_prod] using (Complex.re_le_norm (∏ i, g (σ i) i))

private theorem cross_square (s x y : ℝ) (hs : 0 ≤ s) :
    2*s*x*y ≤ s*(x^2+y^2) := by nlinarith only [mul_nonneg hs (sq_nonneg (x-y))]

private theorem fixed_division (a b c d e f u : ℝ) (hu : 0 < u)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) (he : e ∈ Set.Icc 0 1) (hf : f ∈ Set.Icc 0 1) :
    polynomial a b c d e f ≤
      1+a^2+f^2+a^2*f^2+2*(b^2*e^2+c^2*d^2) +
      (2+u)*(b^2+c^2+d^2+e^2) + 4/u*(a^2*f^2) := by
  let q := b^2+c^2+d^2+e^2
  have h₁ : polynomial a b c d e f ≤
      1+a^2+f^2+a^2*f^2+2*(b^2*e^2+c^2*d^2)+(1+a+f+a*f)*q := by
    unfold polynomial q
    nlinarith only [cross_square a b d ha.1, cross_square a c e ha.1,
      cross_square f b c hf.1, cross_square f d e hf.1,
      cross_square (a*f) b e (mul_nonneg ha.1 hf.1),
      cross_square (a*f) c d (mul_nonneg ha.1 hf.1),
      cross_square 1 (b*e) (c*d) zero_le_one]
  have hu' : 2*(a*f) ≤ u+(a^2*f^2)/u := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hu]
    nlinarith only [sq_nonneg (u-a*f)]
  have hk : 1+a+f+a*f ≤ 2+u+(a^2*f^2)/u := by
    nlinarith only [hu', mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hf.2)]
  have hs {t : ℝ} (h : t ∈ Set.Icc 0 1) : t^2 ≤ 1 := by
    simpa using (pow_le_one₀ h.1 h.2 (n := 2))
  have hq : q ≤ 4 := by dsimp [q]; linarith only [hs hb, hs hc, hs hd, hs he]
  have h₂ := mul_le_mul_of_nonneg_right hk (show 0 ≤ q by dsimp [q]; positivity)
  have h₃ := mul_le_mul_of_nonneg_left hq (show 0 ≤ (a^2*f^2)/u by positivity)
  change _ ≤ _ + (2+u)*q + _
  calc
    _ ≤ _ := h₁
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at h₂ h₃ ⊢
      linarith only [h₂, h₃]

private theorem three_divisions (a b c d e f u : ℝ) (hu : 0 < u)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) (he : e ∈ Set.Icc 0 1) (hf : f ∈ Set.Icc 0 1) :
    polynomial a b c d e f ≤
      1+(5+2*u)/3*(a^2+b^2+c^2+d^2+e^2+f^2) +
        (5+4/u)/3*(a^2*f^2+b^2*e^2+c^2*d^2) := by
  have h₁ := fixed_division a b c d e f u hu ha hb hc hd he hf
  have h₂ := fixed_division b a c d f e u hu hb ha hc hd hf he
  have h₃ := fixed_division c a b e f d u hu hc ha hb he hf hd
  unfold polynomial at *
  simp only [div_eq_mul_inv] at *
  linarith only [h₁, h₂, h₃]

/-- Lemma 7D.1 for the genuine Gram permanent in any coordinate dimension. -/
theorem gram_trade {D : Type*} [Fintype D] (x : Fin 4 → D → ℂ)
    (unit : ∀ i, Bend.energy (x i) = 1) (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    g.permanent.re ≤ 1 + (5+2*u)/3 * edges g + (5+4/u)/3 * matchings g := by
  let g := crossGram x x
  let t : Matrix (Fin 4) (Fin 4) ℝ := fun i j => ‖g i j‖
  have symm (i j) : t j i = t i j := by
    have h : conj (g i j) = g j i := by simp [g, crossGram, bracket, map_sum, mul_comm]
    simp [t, ← h]
  have diag (i) : t i i = 1 := by simp [t, g, crossGram, Coarse.bracket_self, unit]
  have hM : (t : Matrix (Fin 4) (Fin 4) ℝ) =
      normalized (t 0 1) (t 0 2) (t 0 3) (t 1 2) (t 1 3) (t 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [normalized, diag] <;> apply symm
  have ht (i j) : t i j ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨norm_nonneg _, ?_⟩
    have h := FiveProjection.bracket_bound (x i) (x j)
    change Complex.normSq (g i j) ≤ _ at h
    rw [Complex.normSq_eq_norm_sq, unit, unit, one_mul] at h
    change t i j ^ 2 ≤ 1 at h
    nlinarith only [h, norm_nonneg (g i j)]
  have h := permanent_bound g
  change g.permanent.re ≤ t.permanent at h
  rw [hM, permanent_polynomial] at h
  apply h.trans
  simpa only [edges, matchings, Complex.normSq_eq_norm_sq, t, g] using
    three_divisions (t 0 1) (t 0 2) (t 0 3) (t 1 2) (t 1 3) (t 2 3) u hu
      (ht _ _) (ht _ _) (ht _ _) (ht _ _) (ht _ _) (ht _ _)

end
end BlockPermanents.FourTrade
