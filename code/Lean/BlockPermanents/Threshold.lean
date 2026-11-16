import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Coefficients of the disjoint-pair threshold

The positive-weight path recurrence in (th-count) is bounded coefficientwise by
the fine-closure coefficients. We group consecutive path edges in pairs, then
balance the resulting integral weights. This gives an elementary alternative
to diagonalizing the tridiagonal matrix in the proof of (thm:threshold).
-/

namespace BlockPermanents.Threshold
open Multiset

/-- Elementary symmetric function on a multiset of nonnegative integer weights. -/
def elementary (s : Multiset ℕ) (r : ℕ) : ℕ :=
  ((s.powersetCard r).map Multiset.prod).sum

private theorem elementary_zero (s : Multiset ℕ) : elementary s 0 = 1 := by
  simp [elementary]

private theorem elementary_cons (a : ℕ) (s : Multiset ℕ) (r : ℕ) :
    elementary (a ::ₘ s) (r + 1) = elementary s (r + 1) + a * elementary s r := by
  simp [elementary, Multiset.map_map, Function.comp_def, ← Multiset.sum_map_mul_left]

private theorem elementary_empty_succ (r : ℕ) : elementary 0 (r + 1) = 0 := by
  simp [elementary, powersetCard_zero_right]

private theorem bounded_entries (s : Multiset ℕ) (b : ℕ) (h : ∀ x ∈ s, x ≤ b) (r : ℕ) :
    elementary s r ≤ s.card.choose r * b ^ r := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
    cases r <;> simp [elementary_zero, elementary_empty_succ]
  | cons x s ih =>
    have hx := h x (by simp)
    have hs : ∀ a ∈ s, a ≤ b := fun a ha => h a (by simp [ha])
    cases r with
    | zero => simp [elementary_zero]
    | succ r =>
      rw [elementary_cons, card_cons, Nat.choose_succ_succ, add_mul, pow_succ]
      have h1 := ih hs (r + 1)
      have h2 := Nat.mul_le_mul hx (ih hs r)
      rw [pow_succ] at h1
      nlinarith only [h1, h2]

private theorem lower_sum (s : Multiset ℕ) (b : ℕ) (h : ∀ x ∈ s, b ≤ x) :
    s.card * b ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have h1 := h x (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    simpa [Nat.succ_mul, add_comm] using Nat.add_le_add h1 h2

/-- Move one unit from a heavier entry to a lighter one. -/
private theorem balance_pair (s : Multiset ℕ) {x y : ℕ} (h : y ≤ x) (r : ℕ) :
    elementary ((x + 1) ::ₘ y ::ₘ s) r ≤ elementary (x ::ₘ (y + 1) ::ₘ s) r := by
  have hp : (x + 1) * y ≤ x * (y + 1) := by nlinarith
  cases r with
  | zero => simp [elementary_zero]
  | succ r =>
    cases r with
    | zero => simp only [elementary_cons, elementary_zero, mul_one]; omega
    | succ r =>
      simp only [elementary_cons]
      nlinarith only [Nat.mul_le_mul_right (elementary s r) hp]

/-- Integral form of the elementary symmetric mean bound, with an integral
upper bound on the mean. A single-unit transfer decreases the total excess. -/
theorem elementary_le_binomial (s : Multiset ℕ) (b : ℕ) (hs : s.sum ≤ s.card * b) (r : ℕ) :
    elementary s r ≤ s.card.choose r * b ^ r := by
  generalize hd0 : (s.map (fun a => a - b)).sum = d
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    by_cases h : ∀ x ∈ s, x ≤ b
    · exact bounded_entries s b h r
    push_neg at h
    obtain ⟨x, hx, hbig⟩ := h
    obtain ⟨t, rfl⟩ := exists_cons_of_mem hx
    have hsmall : ∃ y ∈ t, y < b := by
      by_contra! hn
      have hl := lower_sum t b hn
      simp only [sum_cons, card_cons, Nat.succ_mul] at hs
      omega
    obtain ⟨y, hy, hsmall⟩ := hsmall
    obtain ⟨u, rfl⟩ := exists_cons_of_mem hy
    cases x with
    | zero => omega
    | succ x =>
      have hs' : (x ::ₘ (y+1) ::ₘ u).sum ≤ (x ::ₘ (y+1) ::ₘ u).card * b := by
        simpa [add_assoc, add_comm, add_left_comm] using hs
      have hd : ((x ::ₘ (y+1) ::ₘ u).map (fun a => a - b)).sum < d := by
        simp only [map_cons, sum_cons] at hd0 ⊢
        omega
      have hrec := ih _ hd _ hs' rfl
      exact (balance_pair u (by omega : y ≤ x) r).trans (by simpa using hrec)


/-- The coefficients A(m,r) of the packet-closure path, with the empty
matching of weight one and out-of-range terms zero. -/
def pathCoeff : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | 1, _ + 1 => 0
  | m + 2, r + 1 => pathCoeff (m + 1) (r + 1) + (m + 1)^2 * pathCoeff m r

private theorem path_mono (m r : ℕ) : pathCoeff m r ≤ pathCoeff (m+1) r := by
  cases r with
  | zero => simp [pathCoeff]
  | succ r =>
    cases m with
    | zero => simp [pathCoeff]
    | succ m => rw [pathCoeff]; omega

/-- Two adjacent path edges cannot both occur in a matching. Forgetting
constraints between pairs gives one bin per two edges. -/
private def bins : ℕ → Multiset ℕ
  | 0 => 0
  | 1 => 0
  | 2 => {1}
  | m + 3 => ((m+1)^2 + (m+2)^2) ::ₘ bins (m+1)

private theorem bins_card (m : ℕ) : (bins m).card = m / 2 := by
  match m with
  | 0 | 1 | 2 => decide
  | m + 3 =>
    rw [bins, card_cons, bins_card (m+1)]
    omega

private theorem bins_sum (m : ℕ) : 6 * (bins m).sum = m * (m-1) * (2*m-1) := by
  match m with
  | 0 | 1 | 2 => decide
  | m + 3 =>
    have ih := bins_sum (m+1)
    rw [bins, sum_cons]
    have ha : 2 * (m + 1) - 1 = 2*m + 1 := by omega
    have hb : 2 * (m + 3) - 1 = 2*m + 5 := by omega
    rw [ha] at ih
    rw [hb]
    simp only [Nat.add_sub_cancel] at ih
    have hc : m+3-1 = m+2 := by omega
    rw [hc]
    nlinarith only [ih]

private theorem path_le_elementary (m r : ℕ) : pathCoeff m r ≤ elementary (bins m) r := by
  match m with
  | 0 | 1 =>
    cases r <;> simp [elementary_zero, elementary_empty_succ, pathCoeff, bins]
  | 2 =>
    cases r with
    | zero => simp [pathCoeff, elementary_zero]
    | succ r =>
      change pathCoeff 2 (r+1) ≤ elementary (1 ::ₘ 0) (r+1)
      cases r with
      | zero => decide
      | succ r =>
        rw [elementary_cons]
        simp [pathCoeff]
  | m + 3 =>
    cases r with
    | zero => simp [pathCoeff, elementary_zero]
    | succ r =>
      rw [pathCoeff, pathCoeff, bins, elementary_cons]
      have h0 := path_le_elementary (m+1) (r+1)
      have h1 := path_le_elementary (m+1) r
      have h2 := (path_mono m r).trans h1
      have h3 := Nat.mul_le_mul_left ((m+1)^2) h2
      have h4 := Nat.mul_le_mul_left ((m+2)^2) h1
      nlinarith only [h0, h3, h4]

/-- Coefficientwise comparison at the exact block-size threshold. The
hypothesis is cross-multiplied to retain the rational cutoff exactly. -/
theorem pathCoeff_le_fine (m b r : ℕ)
    (h : m * (m-1) * (2*m-1) ≤ 6 * (m/2) * b) :
    pathCoeff m r ≤ (m/2).choose r * b^r := by
  have hs := bins_sum m
  have hsum : (bins m).sum ≤ (bins m).card * b := by
    rw [bins_card]
    rw [← hs, Nat.mul_assoc] at h
    omega
  have he := elementary_le_binomial (bins m) b hsum r
  rw [bins_card] at he
  exact (path_le_elementary m r).trans he


/-- Comparison of the upper and lower matching polynomials on arbitrary
nonnegative matching means. Both sums stop at the maximum matching size. -/
theorem matching_sum_le (m k : ℕ) (z : ℕ → ℝ) (hz : ∀ r, 0 ≤ z r)
    (h : m * (m-1) * (2*m-1) ≤ 6 * (m/2) * (2^k-1)) :
    ∑ r ∈ Finset.range (m/2 + 1), (pathCoeff m r : ℝ) * z r ≤
    ∑ r ∈ Finset.range (m/2 + 1), (((m/2).choose r * (2^k-1)^r : ℕ) : ℝ) * z r := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (hz r)
  exact_mod_cast pathCoeff_le_fine m (2^k-1) r h

/-- The numerical hypothesis in the logarithmic corollary, written without
real logarithms: m² ≤ 2^k implies the exact threshold. -/
theorem threshold_of_square_le_pow (m k : ℕ) (hm : 2 ≤ m) (hk : m^2 ≤ 2^k) :
    m * (m-1) * (2*m-1) ≤ 6 * (m/2) * (2^k-1) := by
  have h1 : m-1 ≤ 2*(m/2) := by omega
  have h2 : m * (2*m-1) ≤ 3 * (2^k-1) := by
    have hp : 0 < 2^k := by positivity
    have h3 : 2 * m - 1 + 1 = 2 * m := by omega
    have h4 : 2^k-1+1 = 2^k := by omega
    nlinarith [congrArg (fun x : ℕ => m*x) h3, Nat.mul_self_le_mul_self hm]
  have h := Nat.mul_le_mul h1 h2
  nlinarith only [h]

/-- Coefficient bound under the power-of-two form of the logarithmic corollary. -/
theorem pathCoeff_le_fine_of_square (m k r : ℕ) (hm : 2 ≤ m) (hk : m^2 ≤ 2^k) :
    pathCoeff m r ≤ (m/2).choose r * (2^k-1)^r :=
  pathCoeff_le_fine _ _ _ (threshold_of_square_le_pow m k hm hk)

/-- Four packets at k ≥ 3 and five packets at k ≥ 4 meet the threshold.
The first row is sharp for this coefficient comparison: at k=2, 14 > 6. -/
theorem four_coefficients (k r : ℕ) (hk : 3 ≤ k) :
    pathCoeff 4 r ≤ (2:ℕ).choose r * (2^k-1)^r := by
  apply pathCoeff_le_fine
  have h : 2^3 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
  norm_num at h ⊢
  omega

theorem five_coefficients (k r : ℕ) (hk : 4 ≤ k) :
    pathCoeff 5 r ≤ (2:ℕ).choose r * (2^k-1)^r := by
  apply pathCoeff_le_fine
  have h : 2^4 ≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) hk
  norm_num at h ⊢
  omega

theorem four_quadratic_first_coefficient :
    pathCoeff 4 1 = 14 ∧ (2:ℕ).choose 1 * (2^2-1)^1 = 6 := by decide

/-- Spectator coefficients h(m,r), zero off the allowed range. -/
def spectator : ℕ → ℕ → ℕ
  | m, 0 => if 4 ≤ m then m.choose 3 else 0
  | 0, _ + 1 | 1, _ + 1 => 0
  | m + 2, r + 1 =>
    if 4 + 2*(r+1) ≤ m+2 then spectator (m+1) (r+1) + (m+1)^2 * spectator m r else 0

/-- The matrix of (prop:th-matrix). Lean row i denotes manuscript row i+1. -/
def tradeMatrix (m b : ℕ) : Matrix (Fin (m/2)) (Fin (m/2)) ℝ :=
  fun i j =>
    if i = j then
      (((m/2).choose (i.val+1) * b^(i.val+1) : ℕ) : ℝ) - pathCoeff m (i.val+1) +
        spectator m i.val + (if i.val = 0 then 0 else (spectator m (i.val-1) : ℝ))
    else if i.val + 1 = j.val then -(spectator m i.val : ℝ)
    else if j.val + 1 = i.val then -(spectator m j.val : ℝ) else 0

/-- The concrete matrix at six packets of size four. -/
theorem tradeMatrix_six_four :
    tradeMatrix 6 (2^4-1) = !![(10:ℝ), -20, 0; -20, 356, -100; 0, -100, 3250] := by
  ext i j
  change Fin 3 at i j
  fin_cases i <;> fin_cases j <;> norm_num [tradeMatrix, pathCoeff, spectator, Nat.choose]

/-- Exact LDL certificate for the example just after (prop:th-matrix). -/
theorem tradeMatrix_six_four_psd : (tradeMatrix 6 (2^4-1)).PosSemidef := by
  rw [tradeMatrix_six_four]
  constructor
  · ext i j
    change Fin 3 at i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose]
  · intro v
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have h : 0 ≤ 10*(v 0 - 2*v 1)^2 + 316*(v 1 - 25/79*v 2)^2 + 254250/79*(v 2)^2 := by
      positivity
    nlinarith only [h]

end BlockPermanents.Threshold
