import BlockPermanents.PathJacobiCoefficients

/-! # The positive-coefficient determinant of the imaginary Jacobi matrix -/
namespace BlockPermanents.PathJacobi
open Polynomial Matrix Threshold Complex
noncomputable section

/-- The matrix occurring in the manuscript's positive-coefficient determinant. -/
def iJ (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := I • (J m).map Complex.ofRealHom

private theorem comp_coeff (p : ℂ[X]) (a : ℂ) (k : ℕ) :
    (p.comp (C a * X)).coeff k = a^k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n b =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← map_pow,
      ← mul_assoc, ← map_mul, coeff_C_mul_X_pow]
    by_cases h : n = k
    · subst k
      simp only [coeff_C_mul_X_pow, coeff_monomial, if_true, ite_true, eq_self]
      ring
    · simp only [coeff_C_mul_X_pow, coeff_monomial, if_neg h, if_neg (Ne.symm h), mul_zero]

private theorem rotate (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) :
    (I • A).charpoly = (C I)^m * (A.charpoly.comp (C (-I) * X)) := by
  let f := compRingHom (C (-I) * X)
  have he : (I • A).charmatrix = C I • A.charmatrix.map f := by
    ext i j : 1
    by_cases h : i = j
    · subst j
      simp only [charmatrix_apply_eq, smul_apply, smul_eq_mul, Matrix.map_apply,
        f, coe_compRingHom, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, ← map_mul]
      simp
    · simp only [charmatrix_apply_ne _ _ _ h, smul_apply, smul_eq_mul, Matrix.map_apply,
        f, coe_compRingHom, neg_comp, C_comp, mul_neg, map_mul]
  change (I • A).charmatrix.det = _ * f A.charmatrix.det
  rw [he, det_smul, Fintype.card_fin, RingHom.map_det]
  rfl

/-- Rotation by i multiplies each coefficient of degree k by i^(m−k). -/
theorem iJ_coeff (m k : ℕ) (h : k ≤ m) :
    (iJ m).charpoly.coeff k = I^(m-k) * (((J m).charpoly.coeff k : ℝ) : ℂ) := by
  rw [iJ, rotate, ← map_pow, coeff_C_mul, comp_coeff, charpoly_map, coeff_map]
  have he : I^m * (-I)^k = I^(m-k) := by
    calc I^m * (-I)^k = (I^(m-k) * I^k) * (-I)^k := by rw [← pow_add, Nat.sub_add_cancel h]
         _ = I^(m-k) * (I * -I)^k := by rw [mul_pow, mul_assoc]
         _ = I^(m-k) := by simp
  rw [← mul_assoc, he]
  rfl

/-- The powers of i cancel the signs of the real signed matching polynomial. -/
theorem positive_coeff (m r : ℕ) (h : 2*r ≤ m) :
    (iJ m).charpoly.coeff (m-2*r) = (pathCoeff m r : ℂ) := by
  rw [iJ_coeff _ _ (Nat.sub_le _ _), charpoly_coeff _ _ h,
    show m-(m-2*r)=2*r by omega, pow_mul, I_sq]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  simp

/-- The polynomial identity det(tI−iJ_m) = ∑ A(m,r) t^(m−2r). -/
theorem determinant (m : ℕ) :
    (iJ m).charpoly = ∑ r ∈ Finset.range (m/2+1), C (pathCoeff m r : ℂ) * X^(m-2*r) := by
  ext k
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hit : ∃ r, r ≤ m/2 ∧ m-2*r = k
  · obtain ⟨r, hr, rfl⟩ := hit
    rw [Finset.sum_eq_single r, if_pos rfl]
    · exact positive_coeff m r (by omega)
    · intro s hs ne
      have hs' := Finset.mem_range.mp hs
      exact if_neg (by omega)
    · simp [Finset.mem_range, show r < m/2+1 by omega]
  · rw [Finset.sum_eq_zero]
    · by_cases hk : k ≤ m
      · have ho : Odd (m-k) := by
          refine ⟨(m-k)/2, ?_⟩
          by_contra hn
          exact hit ⟨(m-k)/2, by omega, by omega⟩
        rw [iJ_coeff _ _ hk, charpoly_odd_coeff _ _ hk ho]
        simp
      · apply coeff_eq_zero_of_natDegree_lt
        simpa using lt_of_not_ge hk
    · intro r hr
      exact if_neg (fun e => hit ⟨r, by have := Finset.mem_range.mp hr; omega, by omega⟩)

private theorem trace_entries (m : ℕ) :
    (J m ^ 2).trace = ∑ i, ∑ j, (J m i j)^2 := by
  simp only [Matrix.trace, Matrix.diag, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(symmetric m).apply]

private theorem trace_step (n : ℕ) :
    (J (n+2) ^ 2).trace = (J (n+1) ^ 2).trace + 2*(n+1 : ℝ)^2 := by
  let L := Fin.last (n+1)
  have far (i : Fin n) : J (n+2) i.castSucc.castSucc L = 0 := by
    simp [J,L, show ¬ i.val+1=n+1 by omega, show ¬ n+1+1=i.val by omega, show i.val≠n by omega]
  have hc : (∑ i : Fin (n+1), (J (n+2) i.castSucc L)^2) = (n+1 : ℝ)^2 := by
    rw [Fin.sum_univ_castSucc]
    have adjacent : J (n+2) (Fin.last n).castSucc L = (n+1 : ℝ) := by simp [J, L]
    simp [far, adjacent]
  have hr : (∑ i : Fin (n+1), (J (n+2) L i.castSucc)^2) = (n+1 : ℝ)^2 := by
    simpa only [(symmetric (n+2)).apply L] using hc
  have hb (i : Fin (n+1)) :
      (∑ j : Fin (n+2), (J (n+2) i.castSucc j)^2) =
        (∑ j : Fin (n+1), (J (n+1) i j)^2) + (J (n+2) i.castSucc L)^2 :=
    Fin.sum_univ_castSucc _
  rw [trace_entries, trace_entries, Fin.sum_univ_castSucc]
  change (∑ i : Fin (n+1), ∑ j : Fin (n+2), (J (n+2) i.castSucc j)^2) +
    (∑ j : Fin (n+2), (J (n+2) L j)^2) = _
  simp only [hb, Finset.sum_add_distrib, hc]
  rw [Fin.sum_univ_castSucc (fun j : Fin (n+2) => (J (n+2) L j)^2), hr]
  have hz : J (n+2) L L = 0 := by simp [J]
  rw [show Fin.last (n+1) = L from rfl, hz]
  ring

/-- The two orientations of each edge contribute twice its squared weight. -/
theorem trace_square (m : ℕ) :
    (J m ^ 2).trace / 2 = ∑ j ∈ Finset.range m, (j : ℝ)^2 := by
  match m with
  | 0 => simp [Matrix.trace]
  | 1 => simp [trace_entries, J]
  | n+2 =>
    rw [trace_step, Finset.sum_range_succ, ← trace_square (n+1)]
    push_cast
    ring

/-- The mass of one edge is half the trace of the square of the Jacobi matrix. -/
theorem first_coeff_trace (m : ℕ) : (pathCoeff m 1 : ℝ) = (J m ^ 2).trace / 2 := by
  match m with
  | 0 => simp [trace_square, pathCoeff]
  | 1 => simp [trace_square, pathCoeff]
  | n+2 =>
    rw [pathCoeff, pathCoeff, mul_one, trace_step]
    push_cast
    rw [first_coeff_trace (n+1)]
    ring

end
end BlockPermanents.PathJacobi
