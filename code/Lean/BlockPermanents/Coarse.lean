import BlockPermanents.Bend
import BlockPermanents.Closures
import BlockPermanents.Quadratic

namespace BlockPermanents.Coarse
noncomputable section
open scoped BigOperators ComplexConjugate
open Closures

theorem permanent_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.permanent = A 0 0 * A 1 1 + A 0 1 * A 1 0 := by
  simp only [Quadratic.permanent_succ, Matrix.permanent_isEmpty, Matrix.of_apply,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
  norm_num [Equiv.swap_apply_def, Fin.succ]
  ring

variable {D K : Type*} [Fintype D] [Fintype K] [DecidableEq K]

theorem bracket_self {T : Type*} [Fintype T] (u : T → ℂ) :
    bracket u u = (Bend.energy u : ℂ) := by
  simp [bracket, Bend.energy, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

theorem two_gram {T : Type*} [Fintype T] (y : Fin 2 → T → ℂ) :
    (crossGram y y).permanent =
      ((Bend.energy (y 0) * Bend.energy (y 1) +
        Complex.normSq (∑ t, y 0 t * star (y 1 t)) : ℝ) : ℂ) := by
  rw [permanent_two]
  change bracket (y 0) (y 0) * bracket (y 1) (y 1) + bracket (y 0) (y 1) * bracket (y 1) (y 0) = _
  rw [bracket_self, bracket_self, Complex.ofReal_add, Complex.ofReal_mul]
  congr 1
  have h : (∑ t, y 0 t * star (y 1 t)) = bracket (y 1) (y 0) := by
    unfold bracket
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [h, Complex.normSq_eq_conj_mul_self]
  exact congrArg (fun z => z * bracket (y 1) (y 0)) (Quadratic.pair_conj (y 1) (y 0)).symm

/-- The two extreme cuts are precisely the permanent of the matrix of
block permanents, with the normalized packets of Section 2E. -/
theorem two_packet_permanent (x : Fin 2 → K → D → ℂ) :
    (Matrix.of (fun i j => (crossGram (x i) (x j)).permanent)).permanent =
      ((Bend.energy (packet (x 0)) * Bend.energy (packet (x 1)) +
        Complex.normSq (∑ t, packet (x 0) t * star (packet (x 1) t)) : ℝ) : ℂ) := by
  convert two_gram (fun i => packet (x i)) using 1
  congr 1
  ext i j
  exact (packet_gram (x i) (x j)).symm

end
end BlockPermanents.Coarse
