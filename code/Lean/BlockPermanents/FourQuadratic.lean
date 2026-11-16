import BlockPermanents.Routings
import BlockPermanents.Bend
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The supported last-cap form on four quadratic packets (Section 5D)

`sectorForm` uses the three weighted projection norms after the last cap,
and the remaining full-cap terms. Calculations are homogeneous and apply to
all complex output vectors in each occupation sector.
-/
namespace BlockPermanents.FourQuadratic
open scoped BigOperators Matrix
noncomputable section

/-- Pairs of distinct thin slots in `n` quadratic packets. -/
def slotPairs (n : ℕ) := (Finset.univ : Finset (Fin (2*n))).powersetCard 2

/-- Both chosen slots come from one quadratic packet. -/
def samePair {n : ℕ} (u : Finset (Fin (2*n))) : Prop :=
  ∀ i ∈ u, ∀ j ∈ u, i.val / 2 = j.val / 2

instance {n : ℕ} (u : Finset (Fin (2*n))) : Decidable (samePair u) :=
  inferInstanceAs (Decidable (∀ i ∈ u, ∀ j ∈ u, i.val / 2 = j.val / 2))

/-- The full cut on two and three merged packets has respectively two out
of six, and three out of fifteen, same-packet choices. -/
theorem choice_counts :
    ((slotPairs 2).filter samePair).card = 2 ∧ (slotPairs 2).card = 6 ∧
    ((slotPairs 3).filter samePair).card = 3 ∧ (slotPairs 3).card = 15 := by decide

/-- Average the two possible gluings over the actual pairs of slots. -/
def fullCapMean (n : ℕ) (x y : ℂ) : ℂ :=
  (∑ u ∈ slotPairs n, if samePair u then x else y) / (slotPairs n).card

private theorem fullCapMean_eq (n : ℕ) (x y : ℂ) :
    fullCapMean n x y =
      ((((slotPairs n).filter samePair).card : ℂ) * x +
      ((slotPairs n).card - ((slotPairs n).filter samePair).card : ℂ) * y) / (slotPairs n).card := by
  unfold fullCapMean
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := slotPairs n) samePair
  have hc : ((((slotPairs n).filter samePair).card : ℂ) +
      (((slotPairs n).filter (fun u => ¬samePair u)).card : ℂ)) = (slotPairs n).card := by exact_mod_cast h
  rw [← hc]; ring

/-- The full-cap amplitudes `pw` and `v` including their normalization. -/
theorem fullCapMeans (x y : ℂ) :
    fullCapMean 2 x y = (x+2*y)/3 ∧ fullCapMean 3 x y = (x+4*y)/5 := by
  obtain ⟨h₂,t₂,h₃,t₃⟩ := choice_counts
  simp only [fullCapMean_eq, h₂, t₂, h₃, t₃]
  constructor <;> ring

/-- Two-port and one-port quadratic forms after inverting the last-cap Gram. -/
def q₂ (ρ a b x y : ℝ) : ℝ :=
  (a*x^2 + b*y^2 - ρ/(2+4*ρ)*(a*x+b*y)^2)/(2-ρ)

def q₁ (ρ a x : ℝ) : ℝ := (a*x^2 - ρ/(2+4*ρ)*(a*x)^2)/(2-ρ)

/-- Candidate inverse for the ambient last-cap Gram, in the convention that
`d i + 1` is the number of strands at port `i`. -/
private def inverseReal {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (ρ : ℝ) : Matrix ι ι ℝ := fun i j =>
  (((if i = j then (d i+1 : ℝ) else 0) -
     ρ/(2+4*ρ)*(d i+1)*(d j+1))/(2-ρ) : ℝ)

def inverseEntry {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (ρ : ℝ) : Matrix ι ι ℂ :=
  (inverseReal d ρ).map Complex.ofRealHom

private def gramReal {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (ρ : ℝ) : Matrix ι ι ℝ :=
  fun i j => ρ + (if i=j then 2-ρ else 0)/(d i+1)

private lemma lift_inverse {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ) (ρ : ℝ)
    (h : inverseReal d ρ * gramReal d ρ = 1) : (Routings.capGram d 2 ρ)⁻¹ = inverseEntry d ρ := by
  apply Matrix.inv_eq_left_inv
  change (inverseReal d ρ).map Complex.ofRealHom * (gramReal d ρ).map Complex.ofRealHom = _
  rw [← Matrix.map_mul, h]; ext i j; by_cases h : i=j <;> simp [Matrix.one_apply, h]

def d41 : Fin 2 → ℕ := ![3,0]
def d23 : Fin 2 → ℕ := ![1,2]
def d5 : Fin 1 → ℕ := fun _ => 4

/-- Directly invert the three actual last-cap Gram matrices. -/
theorem inverses {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    (Routings.capGram d41 2 ρ)⁻¹ = inverseEntry d41 ρ ∧
    (Routings.capGram d23 2 ρ)⁻¹ = inverseEntry d23 ρ ∧
    (Routings.capGram d5 2 ρ)⁻¹ = inverseEntry d5 ρ := by
  have h2 : (2:ℝ)-ρ ≠ 0 := by linarith
  have h4 : (2:ℝ)+4*ρ ≠ 0 := by linarith
  refine ⟨lift_inverse _ _ ?_, lift_inverse _ _ ?_, lift_inverse _ _ ?_⟩
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, inverseReal, gramReal, d41, d23, d5, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp [h2, h4] <;> ring

/-- The quadratic form for one real coordinate in a fixed output sector. -/
def sectorForm (ρ x y : ℝ) : ℝ :=
  let w := (x+2*y)/3
  let v := (x+4*y)/5
  24*q₂ ρ 4 1 y x + 144*q₂ ρ 2 3 y w + 1080*q₁ ρ 5 v +
    1350*(v-x/15)^2 + 108*w^2 - 36*x^2

private def den (ρ : ℝ) := (2-ρ)*(1+2*ρ)
def m₁₁ (ρ : ℝ) := 24*(2*(6-ρ))/den ρ
def m₁₂ (ρ : ℝ) := 24*(54-3*ρ-14*ρ^2)/den ρ
def m₂₂ (ρ : ℝ) := 24*(2*(122+17*ρ-38*ρ^2))/den ρ
def determinant (ρ : ℝ) := 576*(98*ρ^2+113*ρ+6)/den ρ

private theorem den_pos {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) : 0 < den ρ :=
  mul_pos (by linarith) (by linarith)

/-- The sector matrix is derived by substituting the full-cap amplitudes in
all three port forms and the remaining terms. -/
theorem sector_expansion {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (x y : ℝ) :
    sectorForm ρ x y = m₁₁ ρ*x^2 + 2*m₁₂ ρ*x*y + m₂₂ ρ*y^2 := by
  have ha : 2-ρ ≠ 0 := by linarith
  have hb : 1+2*ρ ≠ 0 := by linarith
  have hc : 2+4*ρ ≠ 0 := by linarith
  unfold sectorForm q₂ q₁ m₁₁ m₁₂ m₂₂ den
  field_simp; ring

theorem sector_determinant {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    m₁₁ ρ*m₂₂ ρ - (m₁₂ ρ)^2 = determinant ρ := by
  have ha : 2-ρ ≠ 0 := by linarith
  have hb : 1+2*ρ ≠ 0 := by linarith
  unfold m₁₁ m₂₂ m₁₂ determinant den
  field_simp; ring

/-- Explicit completion of the sector form into two reflected squares. -/
theorem sector_squares {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (x y : ℝ) :
    sectorForm ρ x y = m₁₁ ρ*(x+m₁₂ ρ*y/m₁₁ ρ)^2 + determinant ρ/m₁₁ ρ*y^2 := by
  have hA : 0 < m₁₁ ρ := div_pos (by linarith) (den_pos h₀ h₁)
  rw [sector_expansion h₀ h₁, ← sector_determinant h₀ h₁]
  field_simp [hA.ne']; ring

theorem sector_nonnegative {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (x y : ℝ) :
    0 ≤ sectorForm ρ x y := by
  have hA : 0 < m₁₁ ρ := div_pos (by linarith) (den_pos h₀ h₁)
  have hdet : 0 < determinant ρ := div_pos (by nlinarith [sq_nonneg ρ]) (den_pos h₀ h₁)
  rw [sector_squares h₀ h₁]
  exact add_nonneg (mul_nonneg hA.le (sq_nonneg _)) (mul_nonneg (div_pos hdet hA).le (sq_nonneg _))

private theorem re_real_matrix {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (z : ι → ℂ) :
    (Bend.quadratic (M.map Complex.ofRealHom) z).re =
      ∑ i, ∑ j, M i j * ((z i).re*(z j).re + (z i).im*(z j).im) := by
  simp only [Bend.quadratic, Complex.re_sum, Matrix.map_apply, Complex.ofRealHom_eq_coe,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intros
  ring

private lemma invTwo (d : Fin 2 → ℕ) (ρ : ℝ) (x y : ℂ) :
    (Bend.quadratic (inverseEntry d ρ) ![x,y]).re =
      q₂ ρ (d 0 + 1) (d 1 + 1) x.re y.re + q₂ ρ (d 0 + 1) (d 1 + 1) x.im y.im := by
  rw [inverseEntry, re_real_matrix]
  norm_num [inverseReal, q₂, Fin.sum_univ_two]
  ring

private lemma invOne (a : ℕ) (ρ : ℝ) (x : ℂ) :
    (Bend.quadratic (inverseEntry (fun _ : Fin 1 => a) ρ) (fun _ => x)).re =
      q₁ ρ (a + 1) x.re + q₁ ρ (a + 1) x.im := by
  rw [inverseEntry, re_real_matrix]
  norm_num [inverseReal, q₁, Fin.sum_univ_succ]
  ring

/-- The supported last-cap form, using the three actual inverse Gram
matrices, the full-cap averages over pairs of thin slots, and complex data. -/
def gramSector (ρ : ℝ) (x y : ℂ) : ℝ :=
  let w := fullCapMean 2 x y
  let v := fullCapMean 3 x y
  24*(Bend.quadratic (Routings.capGram d41 2 ρ)⁻¹ ![y,x]).re +
    144*(Bend.quadratic (Routings.capGram d23 2 ρ)⁻¹ ![y,w]).re +
    1080*(Bend.quadratic (Routings.capGram d5 2 ρ)⁻¹ (fun _ => v)).re +
    1350*Complex.normSq (v-x/15) + 108*Complex.normSq w - 36*Complex.normSq x

theorem gramSector_split {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (x y : ℂ) :
    gramSector ρ x y = sectorForm ρ x.re y.re + sectorForm ρ x.im y.im := by
  obtain ⟨ha,hb,hc⟩ := inverses h₀ h₁
  obtain ⟨hw,hv⟩ := fullCapMeans x y
  dsimp only [gramSector]
  have hone (z : ℂ) : (Bend.quadratic (inverseEntry d5 ρ) (fun _ => z)).re =
      q₁ ρ (4+1) z.re + q₁ ρ (4+1) z.im := invOne 4 ρ z
  rw [hw, hv, ha, hb, hc, invTwo, invTwo, hone]
  norm_num [sectorForm, d41, d23, d5, Complex.normSq_apply, Complex.div_re,
    Complex.div_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  unfold q₁ q₂
  ring

/-- Positivity for arbitrary complex output vectors and their genuine
last-cap occupation sectors, with no inequalities assumed on the data. -/
theorem supported_sector_pos {ι : Type*} [Fintype ι] (ρ : ι → ℝ)
    (h₀ : ∀ t, 0 ≤ ρ t) (h₁ : ∀ t, ρ t ≤ 1) (x y : ι → ℂ) :
    0 ≤ ∑ t, gramSector (ρ t) (x t) (y t) := by
  apply Finset.sum_nonneg
  intro i _
  rw [gramSector_split (h₀ i) (h₁ i)]
  exact add_nonneg (sector_nonnegative (h₀ i) (h₁ i) _ _) (sector_nonnegative (h₀ i) (h₁ i) _ _)

end
end BlockPermanents.FourQuadratic
