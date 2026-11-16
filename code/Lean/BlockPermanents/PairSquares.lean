import BlockPermanents.PairBound
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Sum of squares for the supported pair bound

A matrix square root supplies one fixed family of complex linear forms for
all second inputs once the first packet is fixed. The symmetric clasp allows
us to apply the argument on the full finite word space. -/

namespace BlockPermanents.PairSquares

open scoped BigOperators Matrix ComplexOrder
open Bend Closures

noncomputable section

theorem gram_eval {I J : Type*} [Fintype I] [Fintype J]
    (T : Matrix J I ℂ) (v : I → ℂ) :
    dotProduct (star v) ((Tᴴ * T).mulVec v) = (energy (T.mulVec v) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  simp [energy, dotProduct, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- The Hermitian difference matrix is positive semidefinite as soon as its
three energies satisfy the corresponding inequality on every input. -/
theorem difference_posSemidef {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix J I ℂ) (P : Matrix K I ℂ) (T : Matrix L I ℂ) (a b : ℝ)
    (bound : ∀ v, energy (P.mulVec v) + b * energy (T.mulVec v) ≤ a * energy (A.mulVec v)) :
    ((a : ℂ) • (Aᴴ * A) - Pᴴ * P - (b : ℂ) • (Tᴴ * T)).PosSemidef := by
  refine ⟨?_, fun v => ?_⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  · simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, dotProduct_sub,
      dotProduct_smul, gram_eval, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.zero_le_real]
    linarith [bound v]

/-- If a difference of three squared norms is nonnegative on all inputs,
there is a single matrix whose squared output norm is that difference. -/
theorem factor_difference {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix J I ℂ) (P : Matrix K I ℂ) (T : Matrix L I ℂ) (a b : ℝ)
    (bound : ∀ v, energy (P.mulVec v) + b * energy (T.mulVec v) ≤ a * energy (A.mulVec v)) :
    ∃ B : Matrix I I ℂ, ∀ v,
      a * energy (A.mulVec v) - energy (P.mulVec v) - b * energy (T.mulVec v) =
        energy (B.mulVec v) := by
  let M := (a : ℂ) • (Aᴴ * A) - Pᴴ * P - (b : ℂ) • (Tᴴ * T)
  have he (v : I → ℂ) :
      dotProduct (star v) (M.mulVec v) =
        ((a * energy (A.mulVec v) - energy (P.mulVec v) - b * energy (T.mulVec v) : ℝ) : ℂ) := by
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, dotProduct_sub,
      dotProduct_smul, gram_eval, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
  have hpsd : M.PosSemidef := difference_posSemidef A P T a b bound
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hpsd
  refine ⟨B, fun v => ?_⟩
  have hv := he v
  rw [hB, gram_eval] at hv
  exact Complex.ofReal_injective hv.symm

/-- The fixed linear functional H ↦ ⟨F,H⟩ as a one-row matrix. -/
def pairingRow {I : Type*} (F : I → ℂ) : Matrix Unit I ℂ :=
  fun _ i => star (F i)

theorem pairingEnergy {I : Type*} [Fintype I] (F H : I → ℂ) :
    energy ((pairingRow F).mulVec H) = Complex.normSq (bracket F H) := by
  simp [energy, Matrix.mulVec, dotProduct, pairingRow, bracket]

/-- Sum-of-squares clause of Lemma 7A.1. Once the first unit packet is
fixed, one matrix works for every symmetric second input. Each row of B
is a complex linear form in that input. -/
theorem full_caps_squares {d k : ℕ}
    (homogeneous : SchurNormalization.HomogeneousSchur d k k) {F : Word d k → ℂ}
    (hF : ∃ (a : ℂ) (x : Fin k → Fin d → ℂ), F = fun i => a * packet x i)
    (hunit : energy F = 1) :
    ∃ B : Matrix (Word d k) (Word d k) ℂ, ∀ H : Word d k → ℂ, Symmetric H →
      ((k+k).choose k : ℝ) * energy ((PairBound.symmetricProductMatrix F).mulVec H) -
        energy H - ((2:ℝ)^k - 1) * Complex.normSq (bracket F H) =
        ∑ i, Complex.normSq (B.mulVec H i) := by
  let P := symClasp d k
  let A := PairBound.symmetricProductMatrix F
  let T := pairingRow F
  have h (v : Word d k → ℂ) :
      energy (P.mulVec v) + ((2:ℝ)^k - 1) * energy ((T * P).mulVec v) ≤
        ((k+k).choose k : ℝ) * energy ((A * P).mulVec v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pairingEnergy]
    exact PairBound.full_caps_normalized homogeneous hF hunit (PairBound.projected_symmetric d k v)
  obtain ⟨B, hB⟩ := factor_difference (A * P) P (T * P) _ _ h
  refine ⟨B, fun H hH => ?_⟩
  have hh : P.mulVec H = H := hH
  simpa only [← Matrix.mulVec_mulVec, hh, T, pairingEnergy] using hB H

end
end BlockPermanents.PairSquares
