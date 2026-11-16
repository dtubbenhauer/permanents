import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # A Maclaurin bound for nonnegative spectral weights

Adjoining one weight splits elementary symmetric sums into the terms that
use the new weight and those that omit it. The tangent inequality for
nonnegative powers bounds their sum at the new arithmetic mean.
-/
namespace BlockPermanents.PathMeans
noncomputable section

private theorem power_tangent (b y : ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y) (r : ℕ) :
    b^(r+1) + (r+1:ℝ)*(y-b)*b^r ≤ y^(r+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ ≤ _ + (r+1:ℝ)*b^r*(y-b)^2 := le_add_of_nonneg_right (by positivity)
      _ = y*(b^(r+1) + (r+1:ℝ)*(y-b)*b^r) := by
        simp only [pow_succ, Nat.cast_succ]; ring
      _ ≤ y*y^(r+1) := mul_le_mul_of_nonneg_left ih hy
      _ = _ := by rw [pow_succ y (r+1)]; ring

private theorem mean_step (n r : ℕ) (a b y : ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y)
    (hm : (n+1:ℝ)*y = a + n*b) :
    (n.choose (r+1):ℝ)*b^(r+1) + a*((n.choose r:ℝ)*b^r) ≤
        ((n+1).choose (r+1):ℝ)*y^(r+1) := by
  have hc : ((n+1).choose (r+1):ℝ) = n.choose r + (n.choose (r+1):ℝ) := by
    exact_mod_cast Nat.choose_succ_succ n r
  have hw : (n+1:ℝ)*(n.choose r:ℝ) = ((n+1).choose (r+1):ℝ)*(r+1) := by
    exact_mod_cast Nat.succ_mul_choose_eq n r
  calc
    _ = (((n+1).choose (r+1):ℝ)*b + (n.choose r:ℝ)*(a-b))*b^r := by
      rw [hc, pow_succ]; ring
    _ = ((n+1).choose (r+1):ℝ)*(b^(r+1) + (r+1:ℝ)*(y-b)*b^r) := by
      rw [show a-b=(n+1:ℝ)*(y-b) by linarith, pow_succ]
      linear_combination (y-b)*b^r*hw
    _ ≤ _ := mul_le_mul_of_nonneg_left (power_tangent b y hb hy r) (by positivity)

private theorem esymm_cons (s : Multiset ℝ) (a : ℝ) (r : ℕ) :
    (a ::ₘ s).esymm (r+1) = s.esymm (r+1) + a*s.esymm r := by
  simp [Multiset.esymm, Multiset.map_map, Function.comp_def, Multiset.sum_map_mul_left]

/-- Maclaurin's bound including repeated, zero, or absent weights, and all orders. -/
theorem maclaurin_multiset (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (r : ℕ) :
    s.esymm r ≤ (s.card.choose r : ℝ)*(s.sum/s.card)^r := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
    cases r <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hs' (x : ℝ) (hx : x ∈ s) : 0 ≤ x := hs x (Multiset.mem_cons_of_mem hx)
    have hz := Multiset.sum_nonneg hs'
    have hm : (s.card:ℝ)*(s.sum/s.card) = s.sum := by
      by_cases hc : s.card = 0
      · simp [Multiset.card_eq_zero.mp hc]
      · field_simp [hc]
    cases r with
    | zero => simp [Multiset.esymm]
    | succ r =>
      rw [esymm_cons, Multiset.card_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_one]
      apply (add_le_add (ih hs' (r+1)) (mul_le_mul_of_nonneg_left (ih hs' r) ha)).trans
      apply mean_step s.card r a _ _ (by positivity) (by positivity)
      have hp : (s.card:ℝ)+1 ≠ 0 := by positivity
      rw [hm]
      field_simp [hp]

/-- Finite-family form with one product for each actual subset. -/
theorem maclaurin {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (r : ℕ) :
    (∑ T ∈ Finset.univ.powersetCard r, ∏ i ∈ T, w i) ≤
        (N.choose r:ℝ)*((∑ i, w i)/N)^r := by
  let s := (Finset.univ : Finset (Fin N)).val.map w
  have hs (x : ℝ) (hx : x ∈ s) : 0 ≤ x := by
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hw i
  simpa only [s, Finset.esymm_map_val, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Fintype.card_fin] using maclaurin_multiset s hs r

end
end BlockPermanents.PathMeans
