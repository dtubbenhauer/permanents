import BlockPermanents.FiveProjection
import Mathlib.Tactic.Linarith

/-! # The two-step path in the threshold appendix

The matchings of sizes one and two are enumerated by distinct ordered
endpoints and divided by their orientation and ordering multiplicities.
The intervening label of the two-step path is summed before taking its norm.
-/
namespace BlockPermanents.TwoStep
open scoped ComplexConjugate
open Finset Closures
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
private theorem squared_sum (s : Finset I) (f : I → ℂ) :
    Complex.normSq (∑ v ∈ s, f v) = ∑ v ∈ s, ∑ w ∈ s, (conj (f v) * f w).re := by
  have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := ∑ v ∈ s, f v))
  rw [Finset.sum_comm]
  simpa only [Complex.ofReal_re, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum] using h

private theorem opposite (a b c d : ℂ) :
    Complex.normSq (a*conj d - c*conj b) =
      Complex.normSq a * Complex.normSq d + Complex.normSq c * Complex.normSq b -
        2*(conj (a*b)*(c*d)).re := by
  rw [Complex.normSq_sub]
  simp only [Complex.normSq_mul, Complex.normSq_conj, map_mul, Complex.conj_conj]
  have h : a * conj d * (conj c * b) = conj (conj (a*b)*(c*d)) := by simp; ring
  rw [h, Complex.conj_re, map_mul (starRingEnd ℂ) a b]

omit [Fintype I] [DecidableEq I] in
/-- Lagrange's identity at fixed endpoints. Opposite edges give the
two diagonal products and their uncrossing is a reflected scalar square. -/
theorem path_square (s : Finset I) (a b : I → ℂ) :
    2 * Complex.normSq (∑ v ∈ s, a v*b v) +
      (∑ v ∈ s, ∑ w ∈ s, Complex.normSq (a v*conj (b w) - a w*conj (b v))) =
    2 * ∑ v ∈ s, ∑ w ∈ s, Complex.normSq (a v) * Complex.normSq (b w) := by
  rw [squared_sum]
  simp only [opposite, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hc := Finset.sum_comm (s := s) (t := s) (f := fun i j => Complex.normSq (a j)*Complex.normSq (b i))
  rw [hc]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

def middles (i j : I) : Finset I := (univ.erase i).erase j

def edgeSq (g : Matrix I I ℂ) (i j : I) := Complex.normSq (g i j)

def path (g : Matrix I I ℂ) (i j : I) := ∑ v ∈ middles i j, g i v * g v j

/-- M₁, using two orientations per edge of the Hermitian Gram matrix. -/
def M₁ (g : Matrix I I ℂ) : ℝ := (∑ i, ∑ v ∈ univ.erase i, edgeSq g i v) / 2

/-- M₂, using eight choices to order and orient the two edges of a matching.
Here the edges are iv and wj. -/
def M₂ (g : Matrix I I ℂ) : ℝ :=
  (∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, ∑ w ∈ (middles i j).erase v,
    edgeSq g i v * edgeSq g w j) / 8

private theorem local_bound (g : Matrix I I ℂ) (bound : ∀ i j, edgeSq g i j ≤ 1) (i j : I) :
    Complex.normSq (path g i j) ≤ ∑ v ∈ middles i j, edgeSq g i v +
      ∑ v ∈ middles i j, ∑ w ∈ (middles i j).erase v, edgeSq g i v * edgeSq g w j := by
  let s := middles i j
  have hs := path_square s (fun v => g i v) (fun v => g v j)
  have hn : 0 ≤ ∑ v ∈ s, ∑ w ∈ s, Complex.normSq
      (g i v*conj (g w j) - g i w*conj (g v j)) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hp : Complex.normSq (path g i j) ≤ ∑ v ∈ s, ∑ w ∈ s, edgeSq g i v * edgeSq g w j := by
    unfold path edgeSq
    linarith only [hs, hn]
  refine hp.trans ?_
  rw [← Finset.sum_add_distrib]
  apply sum_le_sum
  intro v hv
  rw [← sum_erase_add s (fun w => edgeSq g i v * edgeSq g w j) hv]
  have h := mul_le_mul_of_nonneg_left (bound v j) (Complex.normSq_nonneg (g i v))
  change edgeSq g i v * edgeSq g v j ≤ edgeSq g i v * 1 at h
  linarith

private theorem sum_missing_middle (g : Matrix I I ℂ) (i : I) (hq : 2 ≤ Fintype.card I) :
    ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, edgeSq g i v =
    ((Fintype.card I : ℝ) - 2) * ∑ v ∈ univ.erase i, edgeSq g i v := by
  let s := univ.erase i
  have hs (j : I) (hj : j ∈ s) : ∑ v ∈ middles i j, edgeSq g i v =
      (∑ v ∈ s, edgeSq g i v) - edgeSq g i j := by
    have h := sum_erase_add s (edgeSq g i) hj
    unfold middles
    linarith
  rw [sum_congr rfl hs, sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) = (Fintype.card I : ℝ) - 1 := by
    rw [show s.card = Fintype.card I - 1 by simp [s], Nat.cast_sub (by omega : 1 ≤ Fintype.card I)]
    norm_num
  change (s.card : ℝ)*_ - _ = _
  rw [hcard]
  ring

/-- Lemma (th-path) on unit vectors in an arbitrary Gram dimension.
The left side is the sum over unordered pairs, expressed in both
orientations. Diagonal middle labels give (q−2)M₁ and opposite edges
give 4M₂. -/
theorem two_step_path {D : Type*} [Fintype D] (x : I → D → ℂ)
    (unit : ∀ i, Bend.energy (x i) = 1) (hq : 2 ≤ Fintype.card I) :
    let g := crossGram x x
    (∑ i, ∑ j ∈ univ.erase i, Complex.normSq (path g i j)) / 2 ≤
      ((Fintype.card I : ℝ) - 2)*M₁ g + 4*M₂ g := by
  dsimp only
  let g := crossGram x x
  have hb (i j : I) : edgeSq g i j ≤ 1 := by
    simpa [g, edgeSq, crossGram, unit] using FiveProjection.bracket_bound (x i) (x j)
  have h := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    sum_le_sum (s := univ.erase i) (fun j _ => local_bound g hb i j))
  simp only [sum_add_distrib, sum_missing_middle g _ hq] at h
  rw [← Finset.mul_sum] at h
  change (∑ i, ∑ j ∈ univ.erase i, Complex.normSq (path g i j)) / 2 ≤ _
  change _ ≤ ((Fintype.card I : ℝ) - 2)*M₁ g + 4*M₂ g
  unfold M₁ M₂
  linarith

end
end BlockPermanents.TwoStep
