import BlockPermanents.WireSchur

/-! # Recovering the homogeneous Schur relation from its labelled-wire action -/

namespace BlockPermanents.SchurWireCriterion
open Bend Closures WireSchur SchurNormalization
open scoped BigOperators
noncomputable section

/-- The binomial weights on the square forks restore the two homogeneous lower forks. -/
theorem homogeneous_of_unbent {d p q : ℕ} (h : UnbentSchur d p q) : HomogeneousSchur d p q := by
  intro x y
  rw [homogeneousEntry_eq d (p+q) p (by omega)]
  refine (h x y).trans ?_
  apply Finset.sum_congr rfl
  intro r _
  simp only [mixedExchange, exchange, Matrix.mul_apply, splitPair, homogeneousFork, wordFork,
    homogeneousEntry_eq _ _ _ (WireSchur.leftLe r), homogeneousEntry_eq _ _ _ (WireSchur.rightLe r),
    weight, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

/-- The labelled-wire identity, in the rational endomorphism algebra used by transfer. -/
def OperatorIdentity (d p q : ℕ) : Prop :=
  ((p+q).choose p : ℚ) • Transfer.clasp (action d p q) =
    ∑ r : CutIndex p q, (weight p q r : ℚ) •
      (blockOp d p q * action d p q (exchangePerm p q r) * blockOp d p q)

open private total_action from BlockPermanents.WireSchur in
/-- A basis delta reads each entry of the open matrix, including words with repeated letters. -/
theorem unbent_of_operator {d p q : ℕ} (h : OperatorIdentity d p q) : UnbentSchur d p q := by
  classical
  intro x y
  obtain ⟨w, rfl⟩ := (splitWords d p q).surjective x
  obtain ⟨v, rfl⟩ := (splitWords d p q).surjective y
  let z (u : Slots p q → Fin d) : ℂ := if u = v then 1 else 0
  have hw := congrArg (fun T => (T z) w) h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Pi.smul_apply, Rat.smul_def, Rat.cast_natCast, smul_eq_mul, Module.End.mul_apply,
    totalOp_apply, blockOp_apply] at hw
  have hb : blockOp d p q z = blockClasp z := funext (blockOp_apply z)
  rw [hb] at hw
  change ((p+q).choose p : ℂ) * clasp z w =
    ∑ r : CutIndex p q, (weight p q r : ℂ) *
      blockClasp (fun u => blockClasp z (u ∘ exchangePerm p q r)) w at hw
  rw [← total_action z w] at hw
  simp_rw [← exchange_action] at hw
  simpa [z, mul_ite] using hw

/-- The full operator identity implies the original coefficient-one homogeneous relation. -/
theorem of_operator {d p q : ℕ} (h : OperatorIdentity d p q) : HomogeneousSchur d p q :=
  homogeneous_of_unbent (unbent_of_operator h)

/-- The entrywise homogeneous relation and the wire-operator identity are equivalent. -/
theorem operator_iff {d p q : ℕ} : OperatorIdentity d p q ↔ HomogeneousSchur d p q :=
  ⟨of_operator, wire_schur_operator⟩

end
end BlockPermanents.SchurWireCriterion
