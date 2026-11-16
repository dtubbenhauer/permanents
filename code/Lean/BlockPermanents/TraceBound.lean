import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Closing a pair of supported cables (Section 7A)

For a matrix whose columns are supported on a common subspace W, the squared
modulus of its trace is at most dim(W) times its squared Frobenius norm.
The proof expands each column in an orthonormal basis of W and applies
Cauchy–Schwarz to the resulting finite array. -/

namespace BlockPermanents.TraceBound

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

private theorem array_cauchy {β : Type*} [Fintype β] (f g : β → ℂ) :
    ‖∑ p, f p * g p‖ ^ 2 ≤ (∑ p, ‖f p‖ ^ 2) * ∑ p, ‖g p‖ ^ 2 := by
  have h : ‖∑ p, f p * g p‖ ≤ ∑ p, ‖f p‖ * ‖g p‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun p => f p * g p)
  have hn : 0 ≤ ∑ p, ‖f p‖ * ‖g p‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ((sq_le_sq₀ (norm_nonneg _) hn).mpr h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- Closing a matrix whose columns lie in `W` costs at most the support
dimension in squared norm. No assumptions on the rank or symmetry of the
matrix, or on nonzero support, are needed. -/
theorem trace_normSq_le (W : Submodule ℂ (ι → ℂ)) (A : Matrix ι ι ℂ)
    (hcol : ∀ j, (fun i => A i j) ∈ W) :
    Complex.normSq A.trace ≤ (Module.finrank ℂ W : ℝ) *
      ∑ i, ∑ j, Complex.normSq (A i j) := by
  classical
  let e := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let V : Submodule ℂ (EuclideanSpace ℂ ι) := W.map e.toLinearMap
  let col (j : ι) : V := ⟨e (fun i => A i j), ⟨_, hcol j, rfl⟩⟩
  let b := stdOrthonormalBasis ℂ V
  let coord (j : ι) (t : Fin (Module.finrank ℂ V)) : ℂ := b.repr (col j) t
  let coeff (t : Fin (Module.finrank ℂ V)) (i : ι) : ℂ := (b t).val i
  have hdim : Module.finrank ℂ V = Module.finrank ℂ W := e.finrank_map_eq W
  have hcol_expand (i j : ι) : ∑ t, coord j t * coeff t i = A i j := by
    let ev : V →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ i).comp V.subtype
    have h := congrArg ev (b.sum_repr (col j))
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  have h_basis (t : Fin (Module.finrank ℂ V)) : ∑ i, ‖coeff t i‖ ^ 2 = 1 := by
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (b t).val]
    change ‖b t‖ ^ 2 = 1
    rw [b.orthonormal.norm_eq_one t, one_pow]
  have h_coords (i : ι) : ∑ t, ‖coord i t‖ ^ 2 = ∑ j, ‖A j i‖ ^ 2 := by
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ => ℂ) (b.repr (col i)), b.repr.norm_map,
      Submodule.coe_norm, PiLp.norm_sq_eq_of_L2]
    rfl
  let B := Fin (Module.finrank ℂ V)
  have h := array_cauchy (fun p : ι × B => coord p.1 p.2)
    (fun p : ι × B => coeff p.2 p.1)
  simp only [B, Fintype.sum_prod_type, hcol_expand, h_coords] at h
  have hB : (∑ i, ∑ t, ‖coeff t i‖ ^ 2) = (Module.finrank ℂ W : ℝ) := by
    rw [Finset.sum_comm]
    simp [h_basis, hdim]
  rw [hB, Finset.sum_comm (f := fun i j => ‖A j i‖ ^ 2), mul_comm] at h
  simpa only [Matrix.trace, Matrix.diag_apply, Complex.normSq_eq_norm_sq] using h

/-- Specializing to the actual column space gives the rank bound. -/
theorem trace_normSq_le_rank (A : Matrix ι ι ℂ) :
    Complex.normSq A.trace ≤ (A.rank : ℝ) * ∑ i, ∑ j, Complex.normSq (A i j) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  exact trace_normSq_le _ A fun j => Submodule.subset_span ⟨j, rfl⟩

end BlockPermanents.TraceBound
