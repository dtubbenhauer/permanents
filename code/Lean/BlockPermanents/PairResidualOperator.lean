import BlockPermanents.PairResidualMaps
import BlockPermanents.PairResidualSquares
import BlockPermanents.PairSquares
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # The polarized residual-square identity for a pair of packets -/
namespace BlockPermanents.PairResidual
open Bend Closures PairBound PairSquares Support
open scoped BigOperators Matrix
noncomputable section

private def evalMatrix {I : Type*} [Fintype I] (v : I → ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun A := star v ⬝ᵥ (A.mulVec v)
  map_add' A B := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, RingHom.id_apply]

private theorem eval_reflected {I J : Type*} [Fintype I] [Fintype J] (v : I → ℂ)
    (A : Matrix J I ℂ) : evalMatrix v (reflected A) = (energy (A.mulVec v) : ℂ) :=
  gram_eval A v

private theorem ext_evalMatrix {I : Type*} [Fintype I] {A B : Matrix I I ℂ}
    (h : ∀ v, evalMatrix v A = evalMatrix v B) : A = B := by
  classical
  apply Matrix.toEuclideanLin.injective
  apply (ext_inner_map _ _).mp
  intro v
  apply (starRingEnd ℂ).injective
  rw [inner_conj_symm, inner_conj_symm]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.piLp_equiv_toEuclideanLin_apply]
  simpa only [evalMatrix, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_comm] using h ((WithLp.equiv 2 _) v)

/-- The residual halfwebs give the full Gram matrix on any finite family of
symmetric second inputs, including all mixed entries between its columns. -/
theorem full_caps_residual_operator {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hunit : energy (scaled a x) = 1) {I : Type*} [Fintype I]
    (B : Matrix (Word d k) I ℂ) (hB : ∀ j, Symmetric (fun w => B w j)) :
    let F := scaled a x
    let P := symmetricProductMatrix F * B
    let T := pairingRow F * B
    ((k+k).choose k : ℂ) • reflected P - reflected B - ((2 : ℂ)^k - 1) • reflected T =
      ∑ r ∈ Finset.univ.erase (zeroCut k),
        ((k.choose r : ℂ)^2 • reflected (residualMatrix a x r * B) +
        ((k.choose r : ℂ)^2 / (rank x r : ℂ) - k.choose r) • reflected T) := by
  have fixed : symClasp d k * B = B := by
    ext i j
    exact congrFun (hB j) i
  apply ext_evalMatrix
  intro v
  have sym : Symmetric (B.mulVec v) := by
    change (symClasp d k).mulVec (B.mulVec v) = _
    rw [Matrix.mulVec_mulVec, fixed]
  have h := congrArg Complex.ofReal (full_caps_residual_squares a x hunit sym)
  simp only [map_sub, map_sum, map_add, map_smul, eval_reflected, smul_eq_mul,
    ← Matrix.mulVec_mulVec, pairingEnergy, residualMatrix_energy]
  simpa only [residualSummand, Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_one] using h

end
end BlockPermanents.PairResidual
