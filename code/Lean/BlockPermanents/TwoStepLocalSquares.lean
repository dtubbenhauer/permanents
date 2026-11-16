import BlockPermanents.BalancedCubicExterior

/-! The two local remainders in the two-step path of Lemma 7E.1. -/
namespace BlockPermanents.TwoStepSquares

open Finset Closures TwoStep BalancedCubicExterior
open scoped ComplexConjugate
noncomputable section

variable {I D : Type*} [DecidableEq I] [Fintype D]

/-- Squared difference of the two possible opposite-edge gluings. -/
def opposite (g : Matrix I I ℂ) (i j v w : I) : ℝ :=
  Complex.normSq (g i v * conj (g w j) - g i w * conj (g v j))

/-- The incident edge iv is paired with the exterior square on vj. -/
def adjacent (x : I → D → ℂ) (i j v : I) : ℝ :=
  edgeSq (crossGram x x) i v * wedgeEnergy (x v) (x j)

/-- Opposite middle labels are counted in both orders. -/
def remainder (x : I → D → ℂ) (s : Finset I) (i j : I) : ℝ :=
  (∑ v ∈ s, adjacent x i j v) + (∑ v ∈ s, ∑ w ∈ s, opposite (crossGram x x) i j v w) / 2

/-- Exact local form before specializing to a Gram matrix. -/
theorem local_matrix (g : Matrix I I ℂ) (s : Finset I) (i j : I) :
    (∑ v ∈ s, edgeSq g i v) +
      (∑ v ∈ s, ∑ w ∈ s.erase v, edgeSq g i v * edgeSq g w j) -
      Complex.normSq (∑ v ∈ s, g i v * g v j) =
    (∑ v ∈ s, edgeSq g i v * (1 - edgeSq g v j)) +
      (∑ v ∈ s, ∑ w ∈ s, opposite g i j v w) / 2 := by
  have h := path_square s (fun v => g i v) (fun v => g v j)
  change 2 * Complex.normSq (∑ v ∈ s, g i v * g v j) +
    (∑ v ∈ s, ∑ w ∈ s, opposite g i j v w) =
    2 * ∑ v ∈ s, ∑ w ∈ s, edgeSq g i v * edgeSq g w j at h
  have split (v : I) (hv : v ∈ s) :
      (∑ w ∈ s, edgeSq g i v * edgeSq g w j) =
        (∑ w ∈ s.erase v, edgeSq g i v * edgeSq g w j) + edgeSq g i v * edgeSq g v j :=
    (sum_erase_add s _ hv).symm
  rw [sum_congr rfl split, sum_add_distrib] at h
  simp only [mul_sub, mul_one, sum_sub_distrib]
  linarith only [h]

omit [DecidableEq I] in
theorem unit_wedge (x : I → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) (i j : I) :
    1 - edgeSq (crossGram x x) i j = wedgeEnergy (x i) (x j) := by
  simpa only [unit, one_mul, edgeSq, crossGram] using gram_determinant (x i) (x j)

/-- Exact local split on unit packets, with the deficit of the repeated
middle label itself given by a sum of squared coordinate minors. -/
theorem local_squares (x : I → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (s : Finset I) (i j : I) :
    let g := crossGram x x
    (∑ v ∈ s, edgeSq g i v) +
      (∑ v ∈ s, ∑ w ∈ s.erase v, edgeSq g i v * edgeSq g w j) -
      Complex.normSq (∑ v ∈ s, g i v * g v j) = remainder x s i j := by
  dsimp only
  rw [local_matrix, remainder]
  simp_rw [unit_wedge x unit]
  rfl

omit [DecidableEq I] in
private theorem flip (x : I → D → ℂ) (i j : I) :
    edgeSq (crossGram x x) j i = edgeSq (crossGram x x) i j := by
  have eq : (crossGram x x) j i = conj ((crossGram x x) i j) := by
    simp [crossGram, bracket, Complex.star_def, mul_comm]
  simp [edgeSq, eq]

/-- Symmetrizing the incident edges gives the two equal-weight terms
in the manuscript. The contribution of opposite edges keeps its orientation. -/
theorem local_squares_symmetric (x : I → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (s : Finset I) (i j : I) :
    let g := crossGram x x
    (∑ v ∈ s, (edgeSq g i v + edgeSq g v j)/2) +
      (∑ v ∈ s, ∑ w ∈ s.erase v, edgeSq g i v * edgeSq g w j) -
      Complex.normSq (∑ v ∈ s, g i v * g v j) =
    (∑ v ∈ s, (adjacent x i j v + adjacent x j i v)/2) +
      (∑ v ∈ s, ∑ w ∈ s, opposite g i j v w)/2 := by
  dsimp only
  let g := crossGram x x
  have h := local_squares x unit s i j
  dsimp only [remainder] at h
  have step (v : I) :
      (edgeSq g i v + edgeSq g v j)/2 - edgeSq g i v =
        (adjacent x i j v + adjacent x j i v)/2 - adjacent x i j v := by
    simp only [adjacent, ← unit_wedge x unit, g, flip x v j, flip x i v]
    ring
  have total := sum_congr (s₁ := s) rfl (fun v _ => step v)
  simp only [sum_sub_distrib] at total
  dsimp only [g] at total
  linarith only [h, total]

omit [DecidableEq I] in
theorem adjacent_nonneg (x : I → D → ℂ) (i j v : I) : 0 ≤ adjacent x i j v :=
  mul_nonneg (Complex.normSq_nonneg _)
    (div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num))

theorem remainder_nonneg (x : I → D → ℂ) (s : Finset I) (i j : I) : 0 ≤ remainder x s i j :=
  add_nonneg (sum_nonneg fun _ _ => adjacent_nonneg ..)
    (div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num))

end
end BlockPermanents.TwoStepSquares
