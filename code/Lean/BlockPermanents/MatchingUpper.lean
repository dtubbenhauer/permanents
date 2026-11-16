import BlockPermanents.Matchings
import BlockPermanents.MatchingCoarse

/-! Section 7B. Iterating the averaged marked-cap estimate gives the coefficients
of the weighted path recurrence on homogeneous matching means. -/
namespace BlockPermanents.MatchingUpper
open scoped BigOperators
open Closures Matchings Threshold
noncomputable section

private def upper {m : ℕ} (R : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (R+1), (pathCoeff m r : ℝ) * moment m r v p

private theorem single_average {m : ℕ} (R : ℕ) (v : Fin (m+1) → ℝ) (p : Fin (m+1) → Fin (m+1) → ℝ) :
    average (m+1) (fun σ => v (σ 0) * upper R (fun a => v (σ a.succ)) (fun a b => p (σ a.succ) (σ b.succ))) =
    ∑ r ∈ Finset.range (R+1), (pathCoeff m r : ℝ) * moment (m+1) r v p := by
  simp only [upper, Finset.mul_sum]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : 2*r ≤ m
  · simp_rw [mul_left_comm (v _) (pathCoeff m r : ℝ)]
    rw [average_smul, average_single v p hr]
  · rw [pathCoeff_outside (by omega : m < 2*r)]
    simp [average]

private theorem pair_average {m : ℕ} (R : ℕ) (v : Fin (m+2) → ℝ) (p : Fin (m+2) → Fin (m+2) → ℝ)
    (i : Fin (m+1)) :
    average (m+2) (fun σ => p (σ 0) (σ i.succ) * upper R
      (fun a => v (σ ((Equiv.swap 0 i a.succ).succ)))
      (fun a b => p (σ ((Equiv.swap 0 i a.succ).succ)) (σ ((Equiv.swap 0 i b.succ).succ)))) =
    ∑ r ∈ Finset.range (R+1), (pathCoeff m r : ℝ) * moment (m+2) (r+1) v p := by
  simp only [upper, Finset.mul_sum]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : 2*r ≤ m
  · simp_rw [mul_left_comm (p _ _) (pathCoeff m r : ℝ)]
    rw [average_smul, average_pair v p i hr]
  · rw [pathCoeff_outside (by omega : m < 2*r)]
    simp [average]

private theorem collect_coefficients (m R : ℕ) (z : ℕ → ℝ) :
    (∑ r ∈ Finset.range (R+2), (pathCoeff (m+1) r : ℝ) * z r) +
      (m+1 : ℝ)^2 * (∑ r ∈ Finset.range (R+1), (pathCoeff m r : ℝ) * z (r+1)) =
    ∑ r ∈ Finset.range (R+2), (pathCoeff (m+2) r : ℝ) * z r := by
  rw [Finset.sum_range_succ' (f := fun r => (pathCoeff (m+1) r : ℝ) * z r),
    Finset.sum_range_succ' (f := fun r => (pathCoeff (m+2) r : ℝ) * z r)]
  simp only [pathCoeff, Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

variable {D : Type*} [Fintype D]

private def diag {m : ℕ} (x : Fin m → D → ℂ) (i : Fin m) := (bracket (x i) (x i)).re
private def edge {m : ℕ} (x : Fin m → D → ℂ) (i j : Fin m) := Complex.normSq (bracket (x i) (x j))
private def H {m : ℕ} (x : Fin m → D → ℂ) := (crossGram x x).permanent.re

private theorem upper_zero_only {m : ℕ} (R : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) (hm : m ≤ 1) :
    upper R v p = ∏ i, v i := by
  unfold upper
  rw [Finset.sum_eq_single 0]
  · simp [pathCoeff, moment_zero]
  · intro r _ h
    rw [pathCoeff_outside (by omega : m < 2*r)]
    simp
  · simp

private theorem upper_permanent {m : ℕ} (R : ℕ) (hr : m/2 ≤ R) (x : Fin m → D → ℂ) :
    H x ≤ upper R (diag x) (edge x) := by
  match m with
  | 0 =>
    rw [upper_zero_only _ _ _ (by decide)]
    simp [H, Matrix.permanent_isEmpty]
  | 1 =>
    rw [upper_zero_only _ _ _ (by decide)]
    simp [H, diag, crossGram]
  | n+2 =>
    obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
    let v := diag x
    let p := edge x
    let C (σ : Equiv.Perm (Fin (n+2))) :=
      v (σ 0) * upper (S+1) (fun a => v (σ a.succ)) (fun a b => p (σ a.succ) (σ b.succ))
    let P (i : Fin (n+1)) (σ : Equiv.Perm (Fin (n+2))) :=
      p (σ 0) (σ i.succ) * upper S (fun a : Fin n => v (σ ((Equiv.swap 0 i a.succ).succ)))
        (fun a b => p (σ ((Equiv.swap 0 i a.succ).succ)) (σ ((Equiv.swap 0 i b.succ).succ)))
    have peel (σ : Equiv.Perm (Fin (n+2))) : H x ≤ C σ + (n+1 : ℝ) * ∑ i, P i σ := by
      have h := MatchingCoarse.peel_le (x ∘ σ)
      have he : (crossGram (x ∘ σ) (x ∘ σ)).permanent = (crossGram x x).permanent :=
        permanent_reindex σ (crossGram x x)
      rw [he] at h
      apply h.trans
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left (upper_permanent (S+1) (by omega) ((x ∘ σ) ∘ Fin.succ))
        rw [Coarse.bracket_self, Complex.ofReal_re]
        exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (upper_permanent S (by omega)
          (MatchingCoarse.remainder (x ∘ σ) i)) (Complex.normSq_nonneg _)
    have h := average_le peel
    rw [average_const, average_add, average_smul, average_sum] at h
    have hC : average (n+2) C = _ := single_average (S+1) v p
    have hP (i : Fin (n+1)) : average (n+2) (P i) = _ := pair_average S v p i
    rw [hC] at h
    simp_rw [hP] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, ← mul_assoc, ← sq] at h
    exact h.trans_eq (collect_coefficients n S fun r => moment (n+2) r v p)
termination_by m

/-- Homogeneous matching upper estimate on the permanent of the actual Gram
matrix. The singletons carry their squared norms, so zero packets are allowed. -/
theorem permanent_le_upper {m : ℕ} (x : Fin m → D → ℂ) :
    (crossGram x x).permanent.re ≤ ∑ r ∈ Finset.range (m/2+1),
      (pathCoeff m r : ℝ) * moment m r (fun i => (bracket (x i) (x i)).re)
        (fun i j => Complex.normSq (bracket (x i) (x j))) :=
  upper_permanent (m/2) le_rfl x

end
end BlockPermanents.MatchingUpper
