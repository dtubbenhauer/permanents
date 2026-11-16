import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Juxtaposing disjoint reflected cuts

The scalar identity in the proof of the appendix lemma “Disjoint cycles”.
A finite set indexes the cuts; a subset indexes the factors given a minus sign.
-/

namespace BlockPermanents.Cycles
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The product obtained by taking the negative gluing on `minus` and the
positive gluing on its complement in `s`. -/
def signedProduct (s minus : Finset ι) (D T : ι → ℝ) : ℝ :=
  (∏ i ∈ minus, (D i - T i)) * ∏ i ∈ s \ minus, (D i + T i)

/-- The product bound minus the cycle product, multiplied by `2 ^ |s|`,
is twice the sum over sign choices with negative total sign. This cleared
identity also covers the empty family. -/
theorem signedProduct_identity (s : Finset ι) (D T : ι → ℝ) :
    (2 : ℝ) ^ s.card * ((∏ i ∈ s, D i) - ∏ i ∈ s, T i) =
      2 * ∑ u ∈ s.powerset.filter (fun u => Odd u.card), signedProduct s u D T := by
  classical
  have hadd := Finset.prod_add (fun i => D i - T i) (fun i => D i + T i) s
  have hsub := Finset.prod_sub (fun i => D i + T i) (fun i => D i - T i) s
  simp_rw [show ∀ i, (D i - T i) + (D i + T i) = 2 * D i by intro i; ring] at hadd
  simp_rw [show ∀ i, (D i + T i) - (D i - T i) = 2 * T i by intro i; ring] at hsub
  simp only [Finset.prod_mul_distrib, Finset.prod_const] at hadd hsub
  rw [mul_sub, hadd, hsub, ← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rcases Nat.even_or_odd u.card with he | ho
  · rw [he.neg_one_pow, if_neg (Nat.not_odd_iff_even.mpr he)]
    ring
  · rw [ho.neg_one_pow, if_pos ho]
    unfold signedProduct
    ring

/-- If each individual reflected gluing of either sign is nonnegative, the
product of the diagonal bounds dominates the product of the cycle gluings. -/
theorem product_le_of_signed_nonneg (s : Finset ι) (D T : ι → ℝ)
    (hminus : ∀ i ∈ s, 0 ≤ D i - T i) (hplus : ∀ i ∈ s, 0 ≤ D i + T i) :
    (∏ i ∈ s, T i) ≤ ∏ i ∈ s, D i := by
  have h := signedProduct_identity s D T
  have hn : 0 ≤ ∑ u ∈ s.powerset.filter (fun u => Odd u.card), signedProduct s u D T := by
    apply Finset.sum_nonneg
    intro u hu
    have hus := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
    exact mul_nonneg (Finset.prod_nonneg (fun i hi => hminus i (hus hi)))
      (Finset.prod_nonneg (fun i hi => hplus i (Finset.mem_sdiff.mp hi).1))
  have h2 : 0 < (2 : ℝ) ^ s.card := pow_pos (by norm_num) _
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left h2).mp (h ▸ by linarith))

end BlockPermanents.Cycles
