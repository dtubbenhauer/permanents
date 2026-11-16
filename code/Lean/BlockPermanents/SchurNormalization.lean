import BlockPermanents.Bend
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The homogeneous Schur input and its three binomial coefficients

In the symmetric word model a hollow split sums over the choices of slots.
Its ambient permutation numerator divides by the two output factorials. A
square split divides the same numerator by the input factorial. The cited
classical homogeneous dumbbell-crossing relation has coefficient one on each exchange.
-/

namespace BlockPermanents.SchurNormalization
open BlockPermanents.Bend
open scoped BigOperators

/-- The common permutation numerator, with multiplicity for repeated letters. -/
noncomputable def orderedSum (d n : ℕ) (x y : Word d n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), if x = y ∘ σ then (1 : ℂ) else 0

/-- The homogeneous normalization for an `n`-strand output divided into two
groups of sizes `r` and `n-r`. The permutations within either group are
averaged and the choices of groups are summed. -/
noncomputable def homogeneousEntry (d n r : ℕ) (x y : Word d n) : ℂ :=
  ((r.factorial : ℂ) * (n-r).factorial)⁻¹ * orderedSum d n x y

private theorem inverse_factorials (n r : ℕ) (h : r ≤ n) :
    ((r.factorial : ℂ) * (n-r).factorial)⁻¹ = (n.choose r : ℂ) * (n.factorial : ℂ)⁻¹ := by
  have hc : (n.choose r : ℂ) * r.factorial * (n-r).factorial = n.factorial :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have h₁ : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h₂ : ((n-r).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-r)
  have h₃ : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  linear_combination -hc

/-- The hollow fork and square fork differ by the number of subset choices. -/
theorem homogeneousEntry_eq (d n r : ℕ) (h : r ≤ n) (x y : Word d n) :
    homogeneousEntry d n r x y = (n.choose r : ℂ) * symClasp d n x y := by
  simp only [homogeneousEntry, inverse_factorials n r h, orderedSum, symClasp, mul_assoc]

/-- Read the homogeneous split in the two groups of output indices. -/
noncomputable def homogeneousFork (d n r : ℕ) (h : r ≤ n) :
    Matrix (Word d (n-r) × Word d r) (Word d n) ℂ := fun z y =>
  homogeneousEntry d n r (fun t => Fin.append z.1 z.2
    (Fin.cast (Nat.sub_add_cancel h).symm t)) y

/-- The upper merging forks are left unchanged. Only the two lower hollow
forks (`F` and `G`) differ from the square convention. -/
noncomputable def mixedExchange {I J A B T : Type*} [Fintype A] [Fintype B] [Fintype T]
    (f F : Matrix (A × T) I ℂ) (g G : Matrix (B × T) J ℂ) : Matrix (I × J) (I × J) ℂ :=
  (splitPair f g).conjTranspose *
    (show Matrix ((A × B) × (T × T)) (I × J) ℂ from
      fun z x => splitPair F G (z.1, z.2.swap) x)

private lemma leftLe {p q : ℕ} (r : CutIndex p q) : r.val ≤ p :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_left _ _)
private lemma rightLe {p q : ℕ} (r : CutIndex p q) : r.val ≤ q :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_right _ _)

/-- The reference input is the coefficient-one homogeneous dumbbell-crossing relation,
Latifi–Tubbenhauer, arXiv version, Definition 5.2 (5.3), at quantum parameter
one and boundary `(p,q;p,q)`. Both sides use homogeneous entries explicitly. -/
def HomogeneousSchur (d p q : ℕ) : Prop := ∀ x y : Word d p × Word d q,
  homogeneousEntry d (p+q) p (Fin.append x.1 x.2) (Fin.append y.1 y.2) =
    ∑ r : CutIndex p q,
      mixedExchange (wordFork d p r (leftLe r)) (homogeneousFork d p r (leftLe r))
        (wordFork d q r (rightLe r)) (homogeneousFork d q r (rightLe r)) x y

/-- Conversion of the two lower hollow splits and the total split gives
exactly the three coefficients in equation `loc:exchange`. -/
theorem homogeneousSchur_implies_unbent (d p q : ℕ) (h : HomogeneousSchur d p q) :
    UnbentSchur d p q := by
  intro x y
  have he := h x y
  rw [homogeneousEntry_eq d (p+q) p (by omega)] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro r _
  simp only [mixedExchange, exchange, Matrix.mul_apply, splitPair, homogeneousFork, wordFork,
    homogeneousEntry_eq _ _ _ (leftLe r), homogeneousEntry_eq _ _ _ (rightLe r),
    weight, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

end BlockPermanents.SchurNormalization
