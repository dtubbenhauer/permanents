import BlockPermanents.CycleCuts
import Mathlib.GroupTheory.Perm.Centralizer

/-! From the relabelling mean to the actual sum of oriented cycles on a finite label set. -/
namespace BlockPermanents.RawCycleSquares
open CycleMatching CycleComposition CycleCuts
noncomputable section

def classSet (q : ℕ) (t : Multiset ℕ) : Finset (S q) :=
  Finset.univ.filter (fun τ => τ.cycleType = t)

def classSum {q : ℕ} (g : Gram q) (t : Multiset ℕ) : ℂ :=
  ∑ τ ∈ classSet q t, circuit g τ 1

private theorem relabel_class {q : ℕ} (g : Gram q) (t : Multiset ℕ) (σ : S q) :
    (∑ τ ∈ classSet q t, circuit g τ σ) = classSum g t := by
  classical
  unfold classSum
  refine Finset.sum_nbij' (fun τ => σ * τ * σ⁻¹) (fun τ => σ⁻¹ * τ * σ) ?_ ?_ ?_ ?_ ?_
  · intro τ h
    simpa [classSet] using h
  · intro τ h
    have he : (σ⁻¹ * τ * σ).cycleType = τ.cycleType := by
      simpa only [inv_inv] using (Equiv.Perm.cycleType_conj (σ := τ) (τ := σ⁻¹))
    simpa [classSet,he] using h
  · intro τ _; group
  · intro τ _; group
  · intro τ _
    apply Fintype.prod_equiv σ
    intro i
    simp [Equiv.Perm.mul_apply]

/-- Summing the actual permutation monomials over one cycle type is the
class cardinality times the mean weight of any representative. -/
theorem class_average {q : ℕ} (g : Gram q) (τ : S q) :
    classSum g τ.cycleType = ((classSet q τ.cycleType).card : ℂ) * mean g τ := by
  classical
  let t := τ.cycleType
  have hconst (π : S q) (hπ : π ∈ classSet q t) : mean g π = mean g τ :=
    mean_conjugate g (Equiv.Perm.isConj_iff_cycleType_eq.mpr (Finset.mem_filter.mp hπ).2)
  have sum : (∑ π ∈ classSet q t, mean g π) = classSum g t := by
    simp only [mean,complexAverage,← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [relabel_class,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
      nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero q : (q.factorial : ℂ) ≠ 0),one_mul]
  rw [← sum, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- Multiplicity of one oriented cycle of length n with s fixed labels. -/
theorem single_count (n s : ℕ) (hn : 2 ≤ n) :
    ((classSet (n+s) {n}).card : ℝ) =
      ((n+s).factorial : ℝ) / ((s.factorial : ℝ)*n) := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin (n+s)) ({n} : Multiset ℕ)
  simp [Fintype.card_fin,hn] at h
  apply (eq_div_iff (mul_ne_zero (by positivity) (by exact_mod_cast (show n ≠ 0 by omega)))).mpr
  change (((Finset.univ.filter (fun τ : S (n+s) => τ.cycleType = {n})).card : ℕ) : ℝ) * _ = _
  exact_mod_cast h

end
end BlockPermanents.RawCycleSquares
