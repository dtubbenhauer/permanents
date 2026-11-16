import BlockPermanents.TradeMatrix

/-! # The tridiagonal elimination in the proof of Lemma 7D.3

Rows are indexed from zero. After removing row i with pivot a and link −h,
the first diagonal of the remaining chain decreases by h²/a. A nonzero
link forces the current pivot of a positive semidefinite chain to be positive.
-/
namespace BlockPermanents.TradePivots
open Threshold
noncomputable section

def tail (v : ℕ → ℝ) (i : ℕ) := v (i+1)

def prepend (a : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i+1 => v i

private theorem tail_prepend (a : ℝ) (v : ℕ → ℝ) : tail (prepend a v) = v := rfl

/-- The real quadratic form of a chain with n links, initial diagonal a,
successive diagonals d, and off-diagonals −h. -/
def form : ℕ → ℝ → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | 0, a, _, _, v => a * (v 0)^2
  | n+1, a, d, h, v =>
    a*(v 0)^2 - 2*h 0*v 0*v 1 + form n (d 0) (tail d) (tail h) (tail v)

/-- Gaussian elimination pivots. Only indices in the chain are used. -/
def pivot (a : ℝ) (d h : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i+1 => d i - (h i)^2 / pivot a d h i

private theorem pivot_shift (a : ℝ) (d h : ℕ → ℝ) (i : ℕ) :
    pivot a d h (i+1) = pivot (d 0 - (h 0)^2/a) (tail d) (tail h) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [pivot, ← ih, tail]

private theorem form_zero (n : ℕ) (a : ℝ) (d h : ℕ → ℝ) :
    form n a d h (fun _ => 0) = 0 := by
  induction n generalizing a d h with
  | zero => simp [form]
  | succ n ih =>
    simp only [form, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, zero_add]
    exact ih _ _ _

private theorem form_single (n : ℕ) (a : ℝ) (d h : ℕ → ℝ) (t : ℝ) :
    form n a d h (prepend t fun _ => 0) = a*t^2 := by
  cases n <;> simp [form, tail_prepend, form_zero, prepend]

private theorem form_adjust (n : ℕ) (a c : ℝ) (d h v : ℕ → ℝ) :
    form n (a-c) d h v = form n a d h v - c*(v 0)^2 := by
  cases n <;> simp only [form] <;> ring

/-- Exact one-step Schur complement, including the eliminated square. -/
theorem remove_first (n : ℕ) (a : ℝ) (d h v : ℕ → ℝ) (ha : a ≠ 0) (t : ℝ) :
    form (n+1) a d h (prepend t v) =
      a*(t - h 0/a*v 0)^2 + form n (d 0 - (h 0)^2/a) (tail d) (tail h) v := by
  rw [form, tail_prepend, form_adjust]
  simp only [prepend]
  field_simp
  ring

/-- The first n pivots of an (n+1)-row positive semidefinite chain with
positive links are strictly positive. The final pivot is nonnegative. -/
theorem form_pivots (n : ℕ) (a : ℝ) (d h : ℕ → ℝ)
    (hh : ∀ i < n, 0 < h i) (hq : ∀ v, 0 ≤ form n a d h v) :
    (∀ i < n, 0 < pivot a d h i) ∧ 0 ≤ pivot a d h n := by
  have ha : 0 ≤ a := by
    simpa only [form_single, one_pow, mul_one] using hq (prepend 1 fun _ => 0)
  induction n generalizing a d h with
  | zero => exact ⟨by simp, ha⟩
  | succ n ih =>
    have hh₀ := hh 0 (Nat.zero_lt_succ n)
    have hpos : 0 < a := by
      apply lt_of_le_of_ne ha
      intro hzero
      have test := hq (prepend ((d 0+1)/(2*h 0)) (prepend 1 fun _ => 0))
      rw [form, tail_prepend, form_single, ← hzero] at test
      simp only [prepend, zero_mul, zero_sub, one_pow, mul_one] at test
      have he : 2 * h 0 * ((d 0+1)/(2*h 0)) = d 0+1 := by
        field_simp
      linarith
    have htail (v : ℕ → ℝ) : 0 ≤ form n (d 0 - (h 0)^2/a) (tail d) (tail h) v := by
      simpa only [remove_first n a d h v hpos.ne', sub_self, zero_pow (by decide : 2 ≠ 0),
        mul_zero, zero_add] using hq (prepend (h 0/a*v 0) v)
    have hnext : 0 ≤ d 0 - (h 0)^2/a := by
      simpa only [form_single, one_pow, mul_one] using htail (prepend 1 fun _ => 0)
    obtain ⟨hi,hlast⟩ := ih _ _ _ (fun i hi => hh (i+1) (by omega)) htail hnext
    refine ⟨?_, by rwa [pivot_shift]⟩
    intro i hi'
    cases i with
    | zero => exact hpos
    | succ i => rw [pivot_shift]; exact hi i (by omega)

/-- A symmetric real tridiagonal matrix with diagonal d and links −h. -/
def tridiagonal (N : ℕ) (d h : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val = j.val then d i.val else if i.val+1 = j.val then -(h i.val)
    else if j.val+1 = i.val then -(h j.val) else 0

private theorem quadratic_sum (n : ℕ) (d h v : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      v i.val * tridiagonal (n+1) d h i j * v j.val) =
      form n (d 0) (tail d) h v := by
  induction n generalizing d h v with
  | zero => simp [tridiagonal, form]; ring
  | succ n ih =>
    have l (i : Fin (n+1)) : tridiagonal (n+2) d h 0 i.succ =
        if i = 0 then -(h 0) else 0 := by
      have h₁ : (0:ℕ) ≠ i.val+1 := by omega
      have h₂ : i.val+1+1 ≠ 0 := by omega
      have h₃ : 0+1 = i.val+1 ↔ i = 0 := by
        rw [Fin.ext_iff, Fin.val_zero]; omega
      simp only [tridiagonal, Fin.val_zero, Fin.val_succ, if_neg h₁, if_neg h₂, h₃]
    have r (i : Fin (n+1)) : tridiagonal (n+2) d h i.succ 0 =
        if i = 0 then -(h 0) else 0 := by
      have h₁ : i.val+1 ≠ 0 := by omega
      have h₂ : i.val+1+1 ≠ 0 := by omega
      have h₃ : 0+1 = i.val+1 ↔ i = 0 := by
        rw [Fin.ext_iff, Fin.val_zero]; omega
      simp only [tridiagonal, Fin.val_zero, Fin.val_succ, if_neg h₁, if_neg h₂, h₃]
    have s (i j : Fin (n+1)) : tridiagonal (n+2) d h i.succ j.succ =
        tridiagonal (n+1) (tail d) (tail h) i j := by simp [tridiagonal, tail]
    have z : tridiagonal (n+2) d h 0 0 = d 0 := by simp [tridiagonal]
    rw [Fin.sum_univ_succ]
    simp_rw [Fin.sum_univ_succ (n := n+1)]
    rw [Finset.sum_add_distrib]
    simp only [z, l, r, s, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.val_zero, Fin.val_succ]
    change _ + (_ + ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      tail v i.val * tridiagonal (n+1) (tail d) (tail h) i j * tail v j.val) = _
    rw [ih, form]
    ring

/-- The pivot signs for a positive semidefinite real tridiagonal matrix.
The statement also applies to a matrix with no rows. -/
theorem matrix_pivots (N : ℕ) (d h : ℕ → ℝ) (hp : (tridiagonal N d h).PosSemidef)
    (hh : ∀ i, i+1 < N → 0 < h i) (i : ℕ) (hi : i < N) :
    0 ≤ pivot (d 0) (tail d) h i ∧ (i+1 < N → 0 < pivot (d 0) (tail d) h i) := by
  cases N with
  | zero => omega
  | succ n =>
    have hform (v : ℕ → ℝ) : 0 ≤ form n (d 0) (tail d) h v := by
      rw [← quadratic_sum]
      have hq := hp.2 (fun j => v j.val)
      change 0 ≤ ∑ i : Fin (n+1), v i.val * ∑ j : Fin (n+1),
        tridiagonal (n+1) d h i j * v j.val at hq
      simpa only [Finset.mul_sum, mul_assoc] using hq
    obtain ⟨hbefore, hlast⟩ := form_pivots n (d 0) (tail d) h
      (fun j hj => hh j (by omega)) hform
    refine ⟨?_, fun h => hbefore i (by omega)⟩
    rcases (show i ≤ n by omega).eq_or_lt with rfl | h
    · exact hlast
    · exact (hbefore i h).le

/-! ## The spectator links and the matrix of Lemma 7D.3 -/

theorem spectator_positive (m r : ℕ) (hfit : 4+2*r ≤ m) : 0 < spectator m r := by
  induction r generalizing m with
  | zero =>
    have hm : 4 ≤ m := by omega
    simpa [spectator, hm] using Nat.choose_pos (k := 3) (n := m) (by omega)
  | succ r ih =>
    obtain _ | _ | m := m
    · omega
    · omega
    · have h := ih m (by omega)
      have hpow : 0 < (m+1)^2 := by positivity
      simp only [spectator, if_pos hfit]
      exact Nat.add_pos_right _ (Nat.mul_pos hpow h)

def tradeDiagonal (m b i : ℕ) : ℝ :=
  (((m/2).choose (i+1) * b^(i+1) : ℕ) : ℝ) - pathCoeff m (i+1) +
    spectator m i + (if i = 0 then 0 else (spectator m (i-1) : ℝ))

theorem tradeMatrix_eq (m b : ℕ) : tradeMatrix m b =
    tridiagonal (m/2) (tradeDiagonal m b) (fun i => spectator m i) := by
  ext i j
  simp only [tradeMatrix, tridiagonal, tradeDiagonal, Fin.ext_iff]

/-- The i-th elimination pivot of the manuscript's matrix, zero-indexed. -/
def tradePivot (m b : ℕ) :=
  pivot (tradeDiagonal m b 0) (fun i => tradeDiagonal m b (i+1)) (fun i => spectator m i)

theorem tradePivot_sign (m b : ℕ) (hp : (tradeMatrix m b).PosSemidef) (i : ℕ) (hi : i < m/2) :
    0 ≤ tradePivot m b i ∧ (i+1 < m/2 → 0 < tradePivot m b i) := by
  rw [tradeMatrix_eq] at hp
  apply matrix_pivots _ _ _ hp _ i hi
  intro j hj
  exact_mod_cast spectator_positive m j (by omega)

/-- Choosing u=a/h spends the current pivot at row i and the Schur correction
h²/a at row i+1, leaving exactly the next elimination pivot. -/
theorem trade_parameter (m b i : ℕ) (hp : (tradeMatrix m b).PosSemidef) (hi : i+1 < m/2) :
    let a := tradePivot m b i
    let h : ℝ := spectator m i
    let u := a/h
    0 < u ∧ h*u = a ∧ h/u = h^2/a ∧
      tradeDiagonal m b (i+1) - h/u = tradePivot m b (i+1) := by
  dsimp only
  have ha := (tradePivot_sign m b hp i (by omega)).2 hi
  have hh : 0 < (spectator m i : ℝ) := by exact_mod_cast spectator_positive m i (by omega)
  refine ⟨div_pos ha hh, ?_, ?_, ?_⟩
  · field_simp
  · field_simp; ring
  · change _ = tradeDiagonal m b (i+1) - (spectator m i : ℝ)^2 / tradePivot m b i
    congr 1
    field_simp
    ring

/-- The positive parameter used on the link between degrees i+1 and i+2. -/
def parameter (m b i : ℕ) : ℝ := tradePivot m b i / spectator m i

/-- Each degree pays the two incident trades. Equality holds at every interior
degree; any unspent diagonal at the last degree is its nonnegative pivot. -/
theorem degree_budget (m b i : ℕ) (hp : (tradeMatrix m b).PosSemidef) (hi : i < m/2) :
    tradeDiagonal m b i =
      (if i = 0 then 0 else (spectator m (i-1) : ℝ) / parameter m b (i-1)) +
      (if i+1 < m/2 then (spectator m i : ℝ) * parameter m b i else 0) +
      (if i+1 < m/2 then 0 else tradePivot m b i) := by
  have previous :
      tradeDiagonal m b i = (if i = 0 then 0 else (spectator m (i-1) : ℝ) / parameter m b (i-1)) +
        tradePivot m b i := by
    cases i with
    | zero => simp [tradePivot, pivot]
    | succ i =>
      have used := (trade_parameter m b i hp hi).2.2.2
      simp only [Nat.succ_ne_zero, if_false, Nat.add_one_sub_one]
      unfold parameter
      linarith
  by_cases hj : i+1 < m/2
  · simpa only [if_pos hj, add_zero, parameter, (trade_parameter m b i hp hj).2.1] using previous
  · simpa only [if_neg hj, add_zero] using previous

/-- The exact rational pivots of Example 7D.4 obtained by the same recurrence. -/
theorem six_four :
    tradePivot 6 (2^4-1) 0 = 10 ∧ tradePivot 6 (2^4-1) 1 = 316 ∧
      tradePivot 6 (2^4-1) 2 = 254250/79 := by
  norm_num [tradePivot, pivot, tradeDiagonal, pathCoeff, spectator, Nat.choose]

end
end BlockPermanents.TradePivots
