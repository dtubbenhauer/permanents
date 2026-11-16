import BlockPermanents.Threshold
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Positive semidefiniteness and adjacent matching degrees

Optimizing the adjacent parameters pointwise tests the paper's
tridiagonal matrix on the square roots of the matching moments.
This argument also handles vanishing moments.
-/
namespace BlockPermanents.TradeMatrix
open Threshold
noncomputable section

/-- The fine coefficient for manuscript degree i+1. -/
def fineCoeff (m b : ℕ) (i : Fin (m/2)) : ℝ :=
  (((m/2).choose (i.val+1) * b^(i.val+1) : ℕ) : ℝ)

/-- Oriented links carry the four-face spectator coefficient. -/
def link (m : ℕ) (i j : Fin (m/2)) : ℝ :=
  if i.val+1 = j.val then spectator m i.val else 0

private theorem entry (m b : ℕ) (i j : Fin (m/2)) :
    tradeMatrix m b i j =
      (if i = j then tradeMatrix m b i i else 0) - link m i j - link m j i := by
  by_cases h : i = j
  · subst j
    simp [link]
  · by_cases h₁ : i.val+1 = j.val
    · have h₂ : j.val+1 ≠ i.val := by omega
      simp [h,h₁,h₂,tradeMatrix, link]
    · by_cases h₂ : j.val+1 = i.val <;> simp [h,h₁,h₂,tradeMatrix,link]

/-- Evaluate the paper's actual matrix, retaining the positive orientation
of each off-diagonal link once. -/
theorem quadratic (m b : ℕ) (v : Fin (m/2) → ℝ) :
    dotProduct v ((tradeMatrix m b).mulVec v) =
      ∑ i, tradeMatrix m b i i * (v i)^2 -
      ∑ i, ∑ j, 2 * link m i j * v i * v j := by
  classical
  change (∑ i, v i * ∑ j, tradeMatrix m b i j * v j) = _
  conv_lhs =>
    enter [2, i, 2, 2, j, 1]
    rw [entry]
  simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_sub, Finset.mul_sum]
  have hs : (∑ i, ∑ j, v i * (link m j i * v j)) =
      ∑ i, ∑ j, v i * (link m i j * v j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp only [show ∀ i j, 2 * link m i j * v i * v j = 2 * (v i*(link m i j*v j)) by intros; ring,
    ← Finset.mul_sum]
  simp_rw [show ∀ i, v i * (tradeMatrix m b i i * v i) = tradeMatrix m b i i * v i ^ 2 by intros; ring]
  ring

private theorem choose_ratio {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ u : ℝ, 0 < u ∧ u*a + b/u ≤ 2*Real.sqrt a*Real.sqrt b+δ := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    refine ⟨(b+1)/δ, by positivity, ?_⟩
    simp only [mul_zero, zero_add, Real.sqrt_zero, mul_zero, zero_mul]
    rw [div_le_iff₀ (by positivity), mul_comm δ, div_mul_cancel₀ _ hδ.ne']
    linarith
  · rcases hb.eq_or_lt with hb | hb
    · subst b
      refine ⟨δ/a, by positivity, ?_⟩
      rw [div_mul_cancel₀ _ ha.ne', zero_div]
      simp
    · refine ⟨Real.sqrt b / Real.sqrt a, by positivity, ?_⟩
      have h₁ := Real.sq_sqrt (le_of_lt ha)
      have h₂ := Real.sq_sqrt (le_of_lt hb)
      have h : Real.sqrt b / Real.sqrt a * a + b/(Real.sqrt b/Real.sqrt a) =
          2*Real.sqrt a*Real.sqrt b := by
        field_simp
        nlinarith only [congrArg (fun x : ℝ => x*b) h₁, congrArg (fun x : ℝ => x*a) h₂,
          congrArg (fun x : ℝ => x*(Real.sqrt b)^2) h₁]
      linarith

/-- A parameter trade with nonnegative moments pays their full squared
square-root difference. The optimizing parameter may tend to zero or
infinity when one of the moments vanishes. -/
theorem optimize {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u : ℝ, 0 < u → 4*(1-u)*a + 4*(1-1/u)*b ≤ c) :
    4*(Real.sqrt a - Real.sqrt b)^2 ≤ c := by
  by_contra hn
  have hc := lt_of_not_ge hn
  let δ := (4*(Real.sqrt a - Real.sqrt b)^2-c)/8
  have hp : 0 < δ := div_pos (sub_pos.mpr hc) (by norm_num)
  obtain ⟨u,hu,hbnd⟩ := choose_ratio ha hb hp
  have hu' := h u hu
  simp only [div_eq_mul_inv] at hu' hbnd
  dsimp only [δ] at hbnd
  nlinarith only [hu',hbnd,Real.sq_sqrt ha,Real.sq_sqrt hb,hc]

/-- Spectral comparison in Proposition 7D.2. The parameter family is
written after collecting the diagonal terms: fine minus Mᵢᵢ equals the
old coarse coefficient minus the two incident spectator coefficients.
C denotes the positive-degree coarse value. -/
theorem compare (m b : ℕ) (psd : (tradeMatrix m b).PosSemidef)
    (z : Fin (m/2) → ℝ) (hz : ∀ i, 0 ≤ z i) (C : ℝ)
    (family : ∀ (u : Fin (m/2) → Fin (m/2) → ℝ), (∀ i j, 0 < u i j) →
      C ≤ ∑ i, (fineCoeff m b i - tradeMatrix m b i i) * z i +
        ∑ i, ∑ j, link m i j * (u i j * z i + z j / u i j)) :
    C ≤ ∑ i, fineCoeff m b i * z i := by
  classical
  let v := fun i => Real.sqrt (z i)
  have hq := psd.2 v
  change 0 ≤ dotProduct v ((tradeMatrix m b).mulVec v) at hq
  rw [quadratic] at hq
  simp only [v, Real.sq_sqrt (hz _)] at hq
  let L := ∑ i, ∑ j, link m i j
  have hl (i j) : 0 ≤ link m i j := by unfold link; split <;> positivity
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hl i j
  have near (δ : ℝ) (hδ : 0 < δ) : C ≤ (∑ i, fineCoeff m b i * z i) + δ*L := by
    choose u hu hb using fun i j => choose_ratio (hz i) (hz j) hδ
    have h := family u hu
    have he := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ =>
        mul_le_mul_of_nonneg_left (hb i j) (hl i j)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at he
    simp only [sub_mul, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib] at h
    have eq : (∑ i, ∑ j, link m i j * (2 * Real.sqrt (z i) * Real.sqrt (z j))) =
        ∑ i, ∑ j, 2 * link m i j * Real.sqrt (z i) * Real.sqrt (z j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [eq] at he
    change _ ≤ _ + L*δ at he
    linarith only [h, he, hq]
  by_contra hn
  have h := lt_of_not_ge hn
  let δ := (C - ∑ i, fineCoeff m b i * z i)/(L+1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr h) (by positivity)
  have he : δ*(L+1) = C - ∑ i, fineCoeff m b i * z i :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith only [near δ hδ, he, hδ]

end
end BlockPermanents.TradeMatrix
