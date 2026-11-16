import BlockPermanents.FourThickOpenings

/-! The proper cap numbers are 1 through k−1 for each ordinary merge width p ≥ k. -/
namespace BlockPermanents.FourNative
open Bend FourThickOpenings
open scoped BigOperators

/-- A common proper cap number, regarded as an index of the (p,k) opening. -/
def properCut {p k : ℕ} (hp : k ≤ p) (i : Fin (k-1)) : CutIndex p k :=
  ⟨i.val+1, by rw [min_eq_right hp]; have := i.isLt; omega⟩

/-- Reindex the filtered Schur sum independently of p. The new index i represents i+1 caps. -/
theorem sum_proper_eq {p k : ℕ} {A : Type*} [AddCommMonoid A] (hp : k ≤ p) (f : CutIndex p k → A) :
    (∑ r ∈ properIndices p k, f r) = ∑ i : Fin (k-1), f (properCut hp i) := by
  symm
  apply Finset.sum_bij (fun i _ => properCut hp i)
  · intro i _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change 0 < i.val+1 ∧ i.val+1 < k
    have := i.isLt
    omega
  · intro i _ j _ he
    apply Fin.ext
    have h := congrArg Fin.val he
    change i.val+1 = j.val+1 at h
    omega
  · intro r hr
    obtain ⟨hpos,hlt⟩ := (Finset.mem_filter.mp hr).2
    refine ⟨⟨r.val-1, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
    change r.val-1+1 = r.val
    omega
  · intro i _
    rfl

end BlockPermanents.FourNative
