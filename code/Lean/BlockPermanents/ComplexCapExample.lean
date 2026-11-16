import BlockPermanents.Quadratic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Notation

/-! # The complex two-packet one-cap square, Example 1B.3 -/
namespace BlockPermanents.ComplexCapExample
open Quadratic Complex Matrix
open scoped Matrix ComplexConjugate
noncomputable section

/-- Coordinates of e, e+f, e+if and f in the given orthonormal basis. -/
def columns : Fin 4 → Fin 2 → ℂ := ![![1,0], ![1,1], ![1,I], ![0,1]]

private theorem c₀ : columns 0 = ![1,0] := rfl
private theorem c₁ : columns 1 = ![1,1] := rfl
private theorem c₂ : columns 2 = ![1,I] := rfl
private theorem c₃ : columns 3 = ![0,1] := rfl

def triangle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- Traverse the oriented three-cycle and close the fourth column on itself. -/
theorem matching_term : (∏ i, gram4 columns i (triangle i)) = 1+I := by
  rw [Fin.prod_univ_four]
  rw [show triangle 0 = 1 by decide, show triangle 1 = 2 by decide,
    show triangle 2 = 0 by decide, show triangle 3 = 3 by decide]
  norm_num [gram4, pair, c₀, c₁, c₂, c₃, Fin.sum_univ_two]

def scalar : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- Symmetrize a pair of columns and divide by √2. -/
def packet (x y : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => scalar*(x i*y j + y i*x j)

abbrev F := packet (columns 0) (columns 1)
abbrev H := packet (columns 2) (columns 3)

theorem first_packet : F = scalar • !![2,1;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [F, packet, c₀, c₁, c₂, c₃, smul_apply]

theorem second_packet : H = scalar • !![0,1;1,2*I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [H, packet, c₀, c₁, c₂, c₃, smul_apply]
  left
  ring

private theorem scalar_product : scalar * star scalar = (1/2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : 0 ≤ (2:ℝ))
  simp [scalar, ← mul_inv, hs]

/-- Contraction of the normalized packets is the project's single-cap matrix. -/
theorem product_is_cap : F * Hᴴ = Matrix.of (singleCap columns) := by
  ext i j
  simp only [F, H, packet, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    singleCap, Fin.sum_univ_two, Complex.star_def]
  simp only [map_mul (starRingEnd ℂ) scalar]
  have hs := scalar_product
  rw [Complex.star_def] at hs
  linear_combination ( (columns 0 i * columns 1 0 + columns 1 i * columns 0 0) *
    conj (columns 2 j * columns 3 0 + columns 3 j * columns 2 0) +
    (columns 0 i * columns 1 1 + columns 1 i * columns 0 1) *
    conj (columns 2 j * columns 3 1 + columns 3 j * columns 2 1) ) * hs

theorem single_cap : Matrix.of (singleCap columns) = !![1/2,1-I;0,1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.of_apply, singleCap, c₀, c₁, c₂, c₃, Fin.sum_univ_two, map_add, map_mul]
  ring

theorem packet_product : F * Hᴴ = !![1/2,1-I;0,1/2] := product_is_cap.trans single_cap

theorem cap_norm_sq : (∑ i, ∑ j, Complex.normSq (singleCap columns i j)) = 5/2 := by
  change (∑ i, ∑ j, Complex.normSq (Matrix.of (singleCap columns) i j)) = _
  rw [single_cap]
  norm_num [Fin.sum_univ_two, Complex.normSq_sub, Complex.normSq_div, Complex.normSq_ofNat]

/-- The one-cap identity evaluates the gap of the actual Gram permanents. -/
theorem permanent_gap : (gram4 columns).permanent - (blockMatrix (gram4 columns)).permanent = 10 := by
  rw [four_times_one_cap, cap_norm_sq]
  norm_num

end
end BlockPermanents.ComplexCapExample
