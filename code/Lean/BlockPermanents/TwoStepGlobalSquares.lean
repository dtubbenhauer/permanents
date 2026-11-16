import BlockPermanents.TwoStepLocalSquares

/-! The global reflected-square identity in Lemma 7E.1. -/
namespace BlockPermanents.TwoStepSquares
open Finset Closures TwoStep
open scoped ComplexConjugate
noncomputable section

variable {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]

private theorem middles_swap (i j : I) : middles i j = middles j i := by
  ext v
  simp [middles, and_comm]

private theorem endpoints_reverse (f : I → I → ℝ) :
    (∑ i, ∑ j ∈ univ.erase i, f i j) = ∑ i, ∑ j ∈ univ.erase i, f j i := by
  simp_rw [sum_erase_eq_sub (mem_univ _), sum_sub_distrib]
  rw [sum_comm]

/-- Two orientations of each unordered incident-edge pair share its error
equally between the two exterior products. -/
def incidentSquares (x : I → D → ℂ) : ℝ :=
  (∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, (adjacent x i j v + adjacent x j i v)) / 4

/-- Opposite middles are distinct. The ordered list counts both endpoint
and middle reversals, giving the factor one quarter. -/
def fourCycleSquares (g : Matrix I I ℂ) : ℝ :=
  (∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, ∑ w ∈ (middles i j).erase v,
    opposite g i j v w) / 4

private theorem reverse_incident (x : I → D → ℂ) :
    (∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, adjacent x j i v) =
      ∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles i j, adjacent x i j v := by
  calc
    _ = ∑ i, ∑ j ∈ univ.erase i, ∑ v ∈ middles j i, adjacent x j i v := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [middles_swap i j]
    _ = _ := (endpoints_reverse (fun i j => ∑ v ∈ middles i j, adjacent x i j v)).symm

private theorem erase_same_middle (g : Matrix I I ℂ) (i j : I) {v : I} (hv : v ∈ middles i j) :
    (∑ w ∈ middles i j, opposite g i j v w) =
      ∑ w ∈ (middles i j).erase v, opposite g i j v w := by
  rw [sum_erase_eq_sub hv]
  simp [opposite]

open private sum_missing_middle from BlockPermanents.TwoStep in
/-- The exact difference in Lemma 7E.1 for an arbitrary finite set of
unit packets, with the two kinds of reflected halves kept separately. -/
theorem two_step_path_squares (x : I → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (hq : 2 ≤ Fintype.card I) :
    let g := crossGram x x
    ((Fintype.card I : ℝ)-2) * M₁ g + 4 * M₂ g -
      (∑ i, ∑ j ∈ univ.erase i, Complex.normSq (path g i j))/2 =
      incidentSquares x + fourCycleSquares g := by
  dsimp only
  let g := crossGram x x
  have localEq (i j : I) :
      (∑ v ∈ middles i j, edgeSq g i v) +
      (∑ v ∈ middles i j, ∑ w ∈ (middles i j).erase v, edgeSq g i v * edgeSq g w j) -
      Complex.normSq (path g i j) =
      (∑ v ∈ middles i j, adjacent x i j v) +
      (∑ v ∈ middles i j, ∑ w ∈ (middles i j).erase v, opposite g i j v w)/2 := by
    have h := local_squares x unit (middles i j) i j
    change _ = (∑ v ∈ middles i j, adjacent x i j v) +
      (∑ v ∈ middles i j, ∑ w ∈ middles i j, opposite g i j v w)/2 at h
    refine h.trans ?_
    congr 2
    exact sum_congr rfl fun v hv => erase_same_middle g i j hv
  have total := sum_congr (s₁ := (univ : Finset I)) rfl
    (fun i _ => sum_congr (s₁ := univ.erase i) rfl (fun j _ => localEq i j))
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_missing_middle _ _ hq] at total
  rw [← mul_sum] at total
  change ((Fintype.card I : ℝ)-2) * M₁ g + 4 * M₂ g - _ = incidentSquares x + fourCycleSquares g
  unfold M₁ M₂ incidentSquares fourCycleSquares
  simp only [sum_add_distrib, reverse_incident]
  linear_combination total / 2

/-- Each incident and four-cycle contribution is a sum of nonnegative reflected energies. -/
theorem global_squares_nonnegative (x : I → D → ℂ) :
    0 ≤ incidentSquares x ∧ 0 ≤ fourCycleSquares (crossGram x x) := by
  constructor
  · exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      add_nonneg (adjacent_nonneg ..) (adjacent_nonneg ..)) (by norm_num)
  · exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num)

/-- The Hermitian path energy agrees in the two orientations. -/
theorem path_energy_reverse (x : I → D → ℂ) (i j : I) :
    Complex.normSq (path (crossGram x x) i j) = Complex.normSq (path (crossGram x x) j i) := by
  have h (a b : I) : conj (crossGram x x a b) = crossGram x x b a := by
    simp [crossGram, bracket, map_sum, mul_comm]
  have hc : conj (path (crossGram x x) i j) = path (crossGram x x) j i := by
    rw [path, path, map_sum, middles_swap i j]
    simp only [map_mul, h, mul_comm]
  rw [← hc, Complex.normSq_conj]

private theorem sum_orientations {J : Type*} [Fintype J] [LinearOrder J]
    (f : J → J → ℝ) (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j ∈ univ.erase i, f i j)/2 = ∑ i, ∑ j ∈ univ.filter (i < ·), f i j := by
  let u (i j : J) : ℝ := if i < j then f i j else 0
  have pair (i j : J) (hj : j ∈ univ.erase i) : f i j = u i j + u j i := by
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with h | h
    · simp [u, h, h.asymm, hs i j]
    · simp [u, h, h.asymm]
  have split : (∑ i, ∑ j ∈ univ.erase i, f i j) =
      (∑ i, ∑ j ∈ univ.erase i, u i j) + ∑ i, ∑ j ∈ univ.erase i, u j i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j hj => pair i j hj
  rw [split, ← endpoints_reverse u, add_self_div_two]
  apply sum_congr rfl
  intro i _
  rw [sum_erase_eq_sub (mem_univ i), sum_filter]
  simp [u]

/-- The manuscript formula with each unordered endpoint pair i < j
appearing exactly once in the path-energy sum. -/
theorem unordered_path_squares {J : Type*} [Fintype J] [LinearOrder J]
    (x : J → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) (hq : 2 ≤ Fintype.card J) :
    let g := crossGram x x
    ((Fintype.card J : ℝ)-2) * M₁ g + 4 * M₂ g -
      (∑ i, ∑ j ∈ univ.filter (i < ·), Complex.normSq (path g i j)) =
      incidentSquares x + fourCycleSquares g := by
  have h := two_step_path_squares x unit hq
  dsimp only at h ⊢
  rwa [sum_orientations _ (path_energy_reverse x)] at h

end
end BlockPermanents.TwoStepSquares
