import BlockPermanents.Coarse
import BlockPermanents.Quadratic
import BlockPermanents.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The marked packet closure (7B.5)
We open the permanent twice, first along the marked column and then along
the marked row. Every remaining mixed minor is a genuine packet pairing.
The normalized packet convention absorbs the factor (q−2)! in the exits.
-/
namespace BlockPermanents.MatchingCoarse
open scoped BigOperators ComplexConjugate
open Closures

noncomputable section

/-- Positions remaining after removing i, in swap-with-zero order. -/
def omitSlot {n : ℕ} (i : Fin (n+1)) (a : Fin n) := Equiv.swap 0 i a.succ

private theorem row_succ {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    A.permanent = ∑ j, A 0 j * (Matrix.of (fun u v : Fin n => A u.succ (omitSlot j v))).permanent := by
  rw [← Matrix.permanent_transpose A, Quadratic.permanent_succ]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact Matrix.permanent_transpose _

private theorem swap_remaining {n : ℕ} (i : Fin (n+1)) (a : Fin n) :
    Equiv.swap 0 i.succ (omitSlot i a).succ = (omitSlot i a).succ := by
  apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
  intro h
  have hi : Equiv.swap 0 i a.succ = Equiv.swap 0 i 0 := by
    simpa only [Equiv.swap_apply_left] using Fin.succ_injective _ h
  exact Fin.succ_ne_zero _ ((Equiv.swap 0 i).injective hi)

/-- The fixed-mark double Laplace expansion, valid over any commutative semiring. -/
theorem permanent_peel {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n+2)) (Fin (n+2)) R) :
    A.permanent = A 0 0 * (Matrix.of (fun u v : Fin (n+1) => A u.succ v.succ)).permanent +
    ∑ i : Fin (n+1), ∑ j : Fin (n+1), A i.succ 0 * A 0 j.succ *
      (Matrix.of (fun u v : Fin n => A (omitSlot i u).succ (omitSlot j v).succ)).permanent := by
  rw [Quadratic.permanent_succ, Fin.sum_univ_succ]
  simp only [Equiv.swap_self, Equiv.Perm.one_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let M : Matrix (Fin (n+1)) (Fin (n+1)) R :=
    fun u v => A (Equiv.swap 0 i.succ u.succ) v.succ
  change A i.succ 0 * M.permanent = _
  rw [← Matrix.permanent_permute_cols (Equiv.swap 0 i) M, row_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [M, Matrix.submatrix_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, id_eq,
    Matrix.of_apply, mul_assoc]
  congr 2
  congr 1
  ext u v
  exact congrArg (fun a => A a (omitSlot j v).succ) (swap_remaining i u)

variable {D : Type*} [Fintype D]

/-- After removing the mark and its partner i, keep the other vectors in
a common n-slot coordinate space. -/
def remainder {n : ℕ} (x : Fin (n+2) → D → ℂ) (i : Fin (n+1)) (a : Fin n) : D → ℂ :=
  x (omitSlot i a).succ

/-- Exit i, using a matrix packet on the unclamped survivor vectors.
This equals sqrt(n!) times the paper's exit x_i. -/
def exit {n : ℕ} (x : Fin (n+2) → D → ℂ) (i : Fin (n+1)) (w : Fin n → D) : ℂ :=
  bracket (x 0) (x i.succ) * packet (remainder x i) w

private theorem scale_pair {E : Type*} [Fintype E] (a b : ℂ) (u v : E → ℂ) :
    bracket (fun w => a*u w) (fun w => b*v w) = conj a * b * bracket u v := by
  simp only [bracket, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- Gluing two different exits is the mixed minor in the marked Laplace expansion. -/
theorem exit_pair {n : ℕ} (x : Fin (n+2) → D → ℂ) (i j : Fin (n+1)) :
    bracket (exit x i) (exit x j) =
    bracket (x i.succ) (x 0) * bracket (x 0) (x j.succ) *
      (crossGram (remainder x i) (remainder x j)).permanent := by
  rw [← packet_gram]
  have hc : conj (bracket (x 0) (x i.succ)) = bracket (x i.succ) (x 0) :=
    Quadratic.pair_conj _ _
  unfold exit
  rw [scale_pair, hc]

private theorem bracket_sum {T E : Type*} [Fintype T] [Fintype E] (z : T → E → ℂ) :
    bracket (fun w => ∑ i, z i w) (fun w => ∑ i, z i w) = ∑ i, ∑ j, bracket (z i) (z j) := by
  simp only [bracket, map_sum, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ w, ∑ i, ∑ j, conj (z i w) * z j w :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ w, ∑ j, conj (z i w) * z j w := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Marked identity before the variance split. No normalization or
nonvanishing assumptions on any packet are required. -/
theorem fixed_mark {n : ℕ} (x : Fin (n+2) → D → ℂ) :
    (crossGram x x).permanent =
    bracket (x 0) (x 0) * (crossGram (x ∘ Fin.succ) (x ∘ Fin.succ)).permanent +
    (Bend.energy (fun w => ∑ i, exit x i w) : ℂ) := by
  rw [permanent_peel, ← Coarse.bracket_self, bracket_sum]
  simp only [exit_pair]
  rfl

theorem exit_energy {n : ℕ} (x : Fin (n+2) → D → ℂ) (i : Fin (n+1)) :
    Bend.energy (exit x i) = Complex.normSq (bracket (x 0) (x i.succ)) *
      (crossGram (remainder x i) (remainder x i)).permanent.re := by
  rw [← packet_gram, Coarse.bracket_self, Complex.ofReal_re]
  simp [exit, Bend.energy, Complex.normSq_mul, Finset.mul_sum]

private theorem energy_sum {T E : Type*} [Fintype T] [Fintype E] (z : T → E → ℂ) :
    Bend.energy (fun w => ∑ i, z i w) = ∑ i, ∑ j, (bracket (z i) (z j)).re := by
  have h := congrArg Complex.re (bracket_sum z)
  simpa only [Coarse.bracket_self, Complex.ofReal_re, Complex.re_sum] using h

private theorem energy_difference {E : Type*} [Fintype E] (a b : E → ℂ) :
    Bend.energy (fun w => a w - b w) =
      Bend.energy a + Bend.energy b - (bracket a b).re - (bracket b a).re := by
  unfold Bend.energy bracket
  simp only [Complex.re_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The exact defect in Cauchy–Schwarz for the common-output exits. The
ordered sum counts each unordered pair twice. -/
theorem variance {T E : Type*} [Fintype T] [Fintype E] (z : T → E → ℂ) :
    2 * Bend.energy (fun w => ∑ i, z i w) +
      ∑ i, ∑ j, Bend.energy (fun w => z i w - z j w) =
    2 * (Fintype.card T : ℝ) * ∑ i, Bend.energy (z i) := by
  rw [energy_sum]
  simp only [energy_difference, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => (bracket (z j) (z i)).re)]
  ring

/-- Equation (7B.5) before averaging. We retain exactly the sum of squared
differences of exits, written with both orientations of each pair. -/
theorem peel_identity {n : ℕ} (x : Fin (n+2) → D → ℂ) :
    2*(crossGram x x).permanent.re +
      ∑ i, ∑ j, Bend.energy (fun w => exit x i w - exit x j w) =
    2*((bracket (x 0) (x 0)).re * (crossGram (x ∘ Fin.succ) (x ∘ Fin.succ)).permanent.re +
    (n+1 : ℝ) * ∑ i, Complex.normSq (bracket (x 0) (x i.succ)) *
      (crossGram (remainder x i) (remainder x i)).permanent.re) := by
  have h := congrArg Complex.re (fixed_mark x)
  rw [Coarse.bracket_self, Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.ofReal_re, Complex.ofReal_re] at h
  have hv := variance (exit x)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, exit_energy] at hv
  rw [h, Coarse.bracket_self, Complex.ofReal_re]
  linarith

/-- The fixed-mark coarse upper bound used by the threshold recurrence. -/
theorem peel_le {n : ℕ} (x : Fin (n+2) → D → ℂ) :
    (crossGram x x).permanent.re ≤
    (bracket (x 0) (x 0)).re * (crossGram (x ∘ Fin.succ) (x ∘ Fin.succ)).permanent.re +
    (n+1 : ℝ) * ∑ i, Complex.normSq (bracket (x 0) (x i.succ)) *
      (crossGram (remainder x i) (remainder x i)).permanent.re := by
  have h : 0 ≤ ∑ i, ∑ j, Bend.energy (fun w => exit x i w - exit x j w) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  linarith only [peel_identity x, h]

/-- Move the marked label to slot zero, retaining distinct labels even when
two input vectors coincide. -/
def mark {n : ℕ} (x : Fin (n+2) → D → ℂ) (t : Fin (n+2)) : Fin (n+2) → D → ℂ :=
  x ∘ Equiv.swap 0 t

/-- The full averaged identity, with denominators cleared. The edge sum is
over ordered distinct labels, so it counts both orientations of each edge.
The exit sum is also ordered and counts each squared difference twice. -/
theorem averaged_peel_identity {n : ℕ} (x : Fin (n+2) → D → ℂ) :
    2 * (n+2 : ℝ) * (crossGram x x).permanent.re +
      (∑ t, ∑ i, ∑ j, Bend.energy (fun w => exit (mark x t) i w - exit (mark x t) j w)) =
    2 * ((∑ t, (bracket (x t) (x t)).re *
      (crossGram (mark x t ∘ Fin.succ) (mark x t ∘ Fin.succ)).permanent.re) +
      (n+1 : ℝ) * ∑ t, ∑ i, Complex.normSq (bracket (x t) (mark x t i.succ)) *
        (crossGram (remainder (mark x t) i) (remainder (mark x t) i)).permanent.re) := by
  have hperm (t : Fin (n+2)) : (crossGram (mark x t) (mark x t)).permanent =
      (crossGram x x).permanent := permanent_reindex (Equiv.swap 0 t) (crossGram x x)
  have hm (t : Fin (n+2)) : mark x t 0 = x t := by simp [mark]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun t _ => peel_identity (mark x t))
  simp only [hperm, hm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, nsmul_eq_mul, ← Finset.mul_sum] at h
  rw [← h]
  ring

end
end BlockPermanents.MatchingCoarse
