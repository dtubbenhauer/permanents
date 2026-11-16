import BlockPermanents.PairResidualExample

/-! # The middle cut for any orthonormal pair of atoms -/
namespace BlockPermanents.PairOrthonormalExample
open Bend Closures PairBound
open scoped BigOperators Matrix
noncomputable section

abbrev middle := PairResidualExample.middle

/-- Columns of the two atoms in the surviving single-letter word coordinates. -/
def columns {d : ℕ} (x : Fin 2 → Fin d → ℂ) : Matrix (Word d 1) (Fin 2) ℂ :=
  fun w i => x i (w 0)

private theorem gram {d : ℕ} (x : Fin 2 → Fin d → ℂ) :
    (columns x)ᴴ * columns x = crossGram x x := by
  ext i j
  exact ((Equiv.funUnique (Fin 1) (Fin d)).sum_comp
    (fun t => star (x i t) * x j t))

private def swap : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

private theorem swap_unit : swap * swapᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [swap, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.one_apply]

open private scale_sq from BlockPermanents.PairResidualExample in
/-- The one-cap half is half the orthogonal projection onto the span of the atoms. -/
theorem middle_matrix {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    cutMatrix (packet x) (packet x) middle = (2 : ℂ)⁻¹ • (columns x * (columns x)ᴴ) := by
  let X := columns x
  let Y : Matrix (Word d 1) (Word d 1) ℂ :=
    fun i t => packet x (splitWords d 2 middle (i,t))
  have hp : Y = packetScale (Fin 2) • (X * swap * Xᵀ) := by
    ext i j
    rw [Matrix.smul_apply]
    change packet x (splitWords d 2 middle (i,j)) = _
    rw [PairResidualExample.two_packet_entry]
    simp [X, swap, Matrix.mul_apply, Fin.sum_univ_two, columns]
    exact Or.inl (add_comm _ _)
  have hY : cutMatrix (packet x) (packet x) middle = Y * Yᴴ := by
    ext a b
    exact cutMatrix_entry (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _) _ _ _
  have hg : Xᴴ * X = 1 := (gram x).trans hx
  have ht : Xᵀ * (Xᵀ)ᴴ = 1 := by
    have h := congrArg Matrix.transpose hg
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using h
  rw [hY, hp, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, scale_sq]
  change (2 : ℂ)⁻¹ • (X * swap * Xᵀ * ((Xᵀ)ᴴ * (swapᴴ * Xᴴ))) = _
  congr 1
  calc
    _ = X * swap * (Xᵀ * (Xᵀ)ᴴ) * swapᴴ * Xᴴ := by simp only [Matrix.mul_assoc]
    _ = X * (swap * swapᴴ) * Xᴴ := by simp only [ht, Matrix.mul_one, Matrix.mul_assoc]
    _ = X * Xᴴ := by rw [swap_unit, Matrix.mul_one]

theorem middle_trace {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    (cutMatrix (packet x) (packet x) middle).trace = 1 := by
  rw [middle_matrix x hx, Matrix.trace_smul, Matrix.trace_mul_comm, gram, hx, Matrix.trace_one]
  norm_num

private theorem unit_energy {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    energy (packet x) = 1 := by
  have h := packet_gram x x
  rw [hx, Matrix.permanent_one, Coarse.bracket_self] at h
  exact_mod_cast h

private theorem frobenius {I : Type*} [Fintype I] (A : Matrix I I ℂ) :
    ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) = (A * Aᴴ).trace := by
  simp only [Complex.ofReal_sum, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem middle_energy {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    energy ((wordCap d 2 2 middle).mulVec (product (packet x) (fun i => star (packet x i)))) =
      1/2 := by
  rw [← cut_frobenius]
  apply Complex.ofReal_injective
  rw [frobenius, middle_matrix x hx]
  let X := columns x
  have hg : Xᴴ * X = 1 := (gram x).trans hx
  have hp : X * Xᴴ * (X * Xᴴ) = X * Xᴴ := by
    calc
      _ = X * (Xᴴ * X) * Xᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_one]
  change (((2 : ℂ)⁻¹ • (X * Xᴴ)) * ((2 : ℂ)⁻¹ • (X * Xᴴ))ᴴ).trace = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, hp, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_mul_comm, hg, Matrix.trace_one]
  norm_num

/-- The three actual cut terms have weights one, two, and one. -/
theorem cut_values {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    cutTerm (packet x) (packet x) (zeroCut 2) = 1 ∧
    cutTerm (packet x) (packet x) middle = 2 ∧
    cutTerm (packet x) (packet x) (fullCut 2) = 1 := by
  have hs := Bridges.packet_symmetric d 2 x
  have ht := cut_trace hs hs middle
  rw [middle_trace x hx] at ht
  constructor
  · rw [cutTerm, zero_cap_energy hs hs, unit_energy x hx]
    norm_num [weight, zeroCut]
  constructor
  · rw [cutTerm, middle_energy x hx]
    norm_num [weight, middle, PairResidualExample.middle, Nat.choose]
  · rw [cutTerm, full_cap_energy hs hs, ← ht]
    norm_num [weight, fullCut]

/-- The symmetric product of the orthogonal two-letter packet with itself
attains equality, with value four, in any ambient dimension. -/
theorem equality_four {d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    (Nat.choose 4 2 : ℝ) * energy ((symmetricProductMatrix (packet x)).mulVec (packet x)) = 4 := by
  have h := congrArg Complex.re (closed_bent_schur d 2 2
    (SchurNormalization.homogeneousSchur_implies_unbent d 2 2
      (SchurNormalization.homogeneousSchur d 2 2)) (packet x) (packet x))
  rw [product_quadratic_energy] at h
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at h
  change _ = ∑ r : Fin 3, cutTerm (packet x) (packet x) r at h
  obtain ⟨h₀,h₁,h₂⟩ := cut_values x hx
  rw [Fin.sum_univ_three, show (0 : CutIndex 2 2) = zeroCut 2 from rfl,
    show (2 : CutIndex 2 2) = fullCut 2 from rfl, h₀,h₁,h₂] at h
  linarith

end
end BlockPermanents.PairOrthonormalExample
