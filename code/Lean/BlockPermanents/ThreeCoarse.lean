import BlockPermanents.Quadratic
import BlockPermanents.Closures

/-!
# Three unit packets and the coarse matching estimate

For q = 3, the difference U − H in (th-peel) is one third of the sum
of three squared norms. Here H is the permanent of the Gram matrix and
the exits are actual vectors in the coordinate space of the packets.
-/

namespace BlockPermanents.ThreeCoarse
open scoped ComplexConjugate
open Closures

noncomputable section

variable {D : Type*} [Fintype D]

/-- Sum of the three one-edge matching weights. -/
def edgeSum (x : Fin 3 → D → ℂ) : ℝ :=
  Complex.normSq (bracket (x 0) (x 1)) + Complex.normSq (bracket (x 0) (x 2)) +
    Complex.normSq (bracket (x 1) (x 2))

/-- Squared distance between the two routes from the marked packet t. -/
def exitSquare (x : Fin 3 → D → ℂ) (t i j : Fin 3) : ℝ :=
  ∑ d, Complex.normSq
    (bracket (x t) (x i) * x j d - bracket (x t) (x j) * x i d)

private theorem conjugate_bracket (u v : D → ℂ) : conj (bracket u v) = bracket v u := by
  simp [bracket, map_sum, mul_comm]

private theorem difference_expansion (a b : ℂ) (u v : D → ℂ) :
    ((∑ d, Complex.normSq (a*u d - b*v d) : ℝ) : ℂ) =
    conj a * a * bracket u u + conj b * b * bracket v v -
    conj a * b * bracket u v - conj b * a * bracket v u := by
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, map_sub, map_mul,
    bracket, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem exit_expansion (x : Fin 3 → D → ℂ) (t i j : Fin 3)
    (g : Matrix (Fin 3) (Fin 3) ℂ) (hg : g = crossGram x x) :
    (exitSquare x t i j : ℂ) =
    g i t * g t i * g j j + g j t * g t j * g i i -
      g i t * g t j * g j i - g j t * g t i * g i j := by
  subst g
  simp only [exitSquare, difference_expansion, conjugate_bracket, crossGram]

private theorem permanent_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent =
      A 0 0*A 1 1*A 2 2 + A 0 0*A 1 2*A 2 1 +
      A 0 1*A 1 0*A 2 2 + A 0 2*A 2 0*A 1 1 +
      A 0 1*A 1 2*A 2 0 + A 0 2*A 2 1*A 1 0 := by
  classical
  simp only [Quadratic.permanent_succ, Matrix.permanent_isEmpty, Matrix.of_apply,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
  norm_num [Equiv.swap_apply_def, Fin.succ]
  simp only [show (2 : Fin 3) = ⟨2, by decide⟩ from rfl]
  ring

/-- Before normalizing: three times the Gram permanent plus the same exit
squares equals the diagonal term and five copies of each one-edge closure.
The leftover packet closes against itself, including when a packet vanishes. -/
theorem three_exit_identity_general (x : Fin 3 → D → ℂ) :
    let g := crossGram x x
    3 * g.permanent +
      ((exitSquare x 0 1 2 + exitSquare x 1 0 2 + exitSquare x 2 0 1 : ℝ) : ℂ) =
      3 * g 0 0 * g 1 1 * g 2 2 +
      5 * ((Complex.normSq (g 0 1) : ℂ) * g 2 2 +
           (Complex.normSq (g 0 2) : ℂ) * g 1 1 +
           (Complex.normSq (g 1 2) : ℂ) * g 0 0) := by
  dsimp only
  rw [permanent_three]
  simp only [Complex.ofReal_add, exit_expansion x _ _ _ (crossGram x x) rfl,
    Complex.normSq_eq_conj_mul_self, crossGram, conjugate_bracket]
  ring

/-- The exact three-packet instance of the marked-cap defect. Multiplication
by three clears the denominator introduced by averaging over the mark. -/
theorem three_exit_identity (x : Fin 3 → D → ℂ) (unit : ∀ i, bracket (x i) (x i) = 1) :
    3 * (crossGram x x).permanent +
      ((exitSquare x 0 1 2 + exitSquare x 1 0 2 + exitSquare x 2 0 1 : ℝ) : ℂ) =
      3 + 5 * (edgeSum x : ℂ) := by
  simpa [crossGram, unit, edgeSum] using three_exit_identity_general x

/-- Packet-closure bound on three unit vectors, for all finite
coordinate spaces. The scalar right side is 1 + 5 Z₁. -/
theorem permanent_le_matching (x : Fin 3 → D → ℂ) (unit : ∀ i, bracket (x i) (x i) = 1) :
    (crossGram x x).permanent.re ≤ 1 + (5/3) * edgeSum x := by
  have hid := congrArg Complex.re (three_exit_identity x unit)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hid
  norm_num at hid
  have hpos (t i j : Fin 3) : 0 ≤ exitSquare x t i j :=
    Finset.sum_nonneg (fun d _ => Complex.normSq_nonneg _)
  linarith [hpos 0 1 2, hpos 1 0 2, hpos 2 0 1]

end
end BlockPermanents.ThreeCoarse
