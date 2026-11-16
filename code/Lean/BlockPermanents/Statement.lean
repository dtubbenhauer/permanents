import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Matrix formulation of Theorem 1A.1. Indices are a packet and a slot in
that packet. A nonnegative real difference records reality as well as order. -/
namespace BlockPermanents
noncomputable section
open scoped BigOperators ComplexOrder

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def blockPermanentMatrix (A : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i j => (A.submatrix (fun u => (i,u)) (fun v => (j,v))).permanent

/-- The matrix inequality at the given packet number and thickness. -/
def MarcusAt (m k : ℕ) : Prop :=
  ∀ A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ, A.PosSemidef →
    ∃ s : ℝ, 0 ≤ s ∧ A.permanent - (blockPermanentMatrix A).permanent = (s : ℂ)

/-- The precise parameter range of the main theorem, with its rational
threshold cleared of denominators. This is a statement for future milestones. -/
def ManuscriptTheorem : Prop :=
  ∀ m k : ℕ, 1 ≤ m → 1 ≤ k →
    (m ≤ 4 ∨ (m = 5 ∧ 3 ≤ k) ∨
      (2 ≤ m ∧ m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1))) → MarcusAt m k

/-- Simultaneous reindexing transports the permutation sum defining the permanent. -/
theorem permanent_reindex [CommSemiring R] (e : I ≃ J) (A : Matrix J J R) :
    (A.submatrix e e).permanent = A.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv e.permCongr
  intro p
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.permCongr_def]

/-- A single thin slot in each packet gives the original matrix. -/
theorem thickness_one (m : ℕ) : MarcusAt m 1 := by
  intro A _
  refine ⟨0, le_rfl, ?_⟩
  let e : Fin m ≃ Fin m × Fin 1 :=
    ⟨fun i => (i,0), Prod.fst, fun _ => rfl,
      fun ⟨i,t⟩ => Prod.ext rfl (Subsingleton.elim _ _)⟩
  have h : blockPermanentMatrix A = A.submatrix e e := by
    ext i j
    apply Matrix.permanent_eq_elem_of_subsingleton _ 0
  rw [h, permanent_reindex, sub_self, Complex.ofReal_zero]

/-- A single packet gives a one-entry matrix containing the original permanent. -/
theorem one_packet (k : ℕ) : MarcusAt 1 k := by
  intro A _
  refine ⟨0, le_rfl, ?_⟩
  let e : Fin k ≃ Fin 1 × Fin k :=
    ⟨fun i => (0,i), Prod.snd, fun _ => rfl,
      fun ⟨t,i⟩ => Prod.ext (Subsingleton.elim _ _) rfl⟩
  rw [Matrix.permanent_eq_elem_of_subsingleton (blockPermanentMatrix A) 0]
  change A.permanent - (A.submatrix e e).permanent = _
  rw [permanent_reindex, sub_self, Complex.ofReal_zero]

end
end BlockPermanents
