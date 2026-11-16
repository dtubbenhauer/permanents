import BlockPermanents.PathJacobiCoefficients
import BlockPermanents.PathMeans
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Expand

/-! # Paired real eigenvalues of the weighted path in Theorem 7C.1 -/
namespace BlockPermanents.PathSpectrum
open Matrix Polynomial Multiset
noncomputable section

/-- Product of the linear factors for a multiset of real roots. -/
def linearFactors (s : Multiset ℝ) : ℝ[X] := (s.map fun a => X - C a).prod

/-- The characteristic polynomial of a real symmetric matrix in its orthonormal eigenbasis. -/
theorem spectral_factors {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    A.charpoly = linearFactors (Finset.univ.val.map hA.eigenvalues) := by
  let U := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hu : U * star U = 1 := (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2)
  have ha : A = U * diagonal hA.eigenvalues * star U := hA.spectral_theorem
  apply Polynomial.funext
  intro t
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix]
  simp only [eval_sub, eval_X, eval_C]
  have he : scalar (Fin m) t - A = U * diagonal (fun i => t - hA.eigenvalues i) * star U := by
    conv_lhs => rw [ha]
    rw [← Matrix.diagonal_sub, ← Matrix.smul_one_eq_diagonal, mul_sub, sub_mul]
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hu]
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [he, det_mul, det_mul, det_diagonal]
  have hd : U.det * (star U).det = 1 := by rw [← det_mul, hu, det_one]
  rw [mul_right_comm, hd, one_mul]
  simp only [linearFactors, Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C, Finset.prod]

private theorem scale_linear (x : ℝ) : (X - C x).scaleRoots (-1) = X - C (-x) := by
  ext k
  rw [coeff_scaleRoots, natDegree_X_sub_C]
  cases k with
  | zero => simp
  | succ k => simp

private theorem scale_factors (s : Multiset ℝ) :
    (linearFactors s).scaleRoots (-1) = linearFactors (s.map Neg.neg) := by
  induction s using Multiset.induction_on with
  | empty => simp [linearFactors, one_scaleRoots]
  | cons x s ih =>
    simp only [linearFactors, map_cons, prod_cons] at *
    rw [mul_scaleRoots_of_noZeroDivisors, scale_linear, ih]

/-- A real multiset fixed by sign change consists of opposite pairs and at most one zero. -/
private theorem pair_multiset (s : Multiset ℝ) (hs : s.map Neg.neg = s) :
    ∃ z : Multiset ℝ, z.card = s.card/2 ∧
      s = replicate (s.card%2) 0 + (z + z.map Neg.neg) := by
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    by_cases h : ∀ x ∈ s, x = 0
    · refine ⟨replicate (s.card/2) 0, by simp, ?_⟩
      conv_lhs => rw [eq_replicate_card.mpr h]
      simp only [map_replicate, neg_zero, ← replicate_add]
      congr 1
      omega
    · push_neg at h
      obtain ⟨x,hx,h0⟩ := h
      have hx' : -x ∈ s := hs ▸ (mem_map.mpr ⟨x,hx,rfl⟩ : -x ∈ s.map Neg.neg)
      obtain ⟨u,rfl⟩ := exists_cons_of_mem hx
      have hh : -x ∈ u := (mem_cons.mp hx').resolve_left (by intro e; apply h0; linarith)
      obtain ⟨v,rfl⟩ := exists_cons_of_mem hh
      simp only [map_cons, neg_neg] at hs
      rw [cons_swap] at hs
      have hv := (cons_inj_right _).mp ((cons_inj_right _).mp hs)
      obtain ⟨z,hz,hv'⟩ := ih v ((lt_cons_self v (-x)).trans (lt_cons_self _ x)) hv
      refine ⟨x ::ₘ z, ?_, ?_⟩
      · simp only [card_cons]; omega
      · simp only [card_cons, map_cons, cons_add, add_cons]
        rw [show (v.card+1+1)%2=v.card%2 by omega, ← hv']

private theorem factor_pairs (z : Multiset ℝ) :
    linearFactors (z + z.map Neg.neg) = expand ℝ 2 (linearFactors (z.map (fun x => x^2))) := by
  induction z using Multiset.induction_on with
  | empty => simp [linearFactors]
  | cons x z ih =>
    simp only [map_cons,cons_add,add_cons,linearFactors,prod_cons,map_mul] at *
    rw [← ih, map_sub, expand_X, expand_C, map_neg, map_pow]
    ring

/-- The real eigenvalues of the weighted Jacobi matrix, counted with multiplicity. -/
def eigenvalues (m : ℕ) : Multiset ℝ :=
  let h : (PathJacobi.J m).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact PathJacobi.symmetric m
  Finset.univ.val.map h.eigenvalues

private theorem jacobi_factors (m : ℕ) : (PathJacobi.J m).charpoly = linearFactors (eigenvalues m) :=
  spectral_factors _

@[simp] theorem eigenvalues_card (m : ℕ) : (eigenvalues m).card = m := by simp [eigenvalues]

/-- Sign change preserves every eigenvalue multiplicity, including the zero eigenvalue. -/
theorem eigenvalues_neg (m : ℕ) : (eigenvalues m).map Neg.neg = eigenvalues m := by
  have h : (PathJacobi.J m).charpoly.scaleRoots (-1) = (PathJacobi.J m).charpoly := by
    ext k
    rw [coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rcases Nat.even_or_odd (m-k) with he | ho
    · rw [he.neg_one_pow, mul_one]
    · have hk : k ≤ m := by
        by_contra! h
        simp [Nat.sub_eq_zero_of_le h.le] at ho
      rw [PathJacobi.charpoly_odd_coeff m k hk ho, zero_mul]
  rw [jacobi_factors, scale_factors] at h
  simpa only [linearFactors, Polynomial.roots_multiset_prod_X_sub_C] using congrArg Polynomial.roots h

/-- The weighted path determinant has quadratic factors from the opposite eigenvalue pairs. -/
theorem paired_spectrum (m : ℕ) : ∃ z : Multiset ℝ, z.card = m/2 ∧
    eigenvalues m = replicate (m%2) 0 + (z + z.map Neg.neg) ∧
    (PathJacobi.J m).charpoly = X^(m%2) * expand ℝ 2 (linearFactors (z.map (fun x => x^2))) := by
  obtain ⟨z,hz,he⟩ := pair_multiset _ (eigenvalues_neg m)
  rw [eigenvalues_card] at hz he
  refine ⟨z,hz,he,?_⟩
  rw [jacobi_factors, he, ← factor_pairs]
  simp [linearFactors, Multiset.map_add, Multiset.prod_add]

/-- Every matching coefficient is an elementary symmetric function of the same
squared eigenvalues. The partner multiplicities are part of the conclusion. -/
theorem pathCoeff_esymm (m : ℕ) : ∃ z : Multiset ℝ, z.card = m/2 ∧
    eigenvalues m = replicate (m%2) 0 + (z + z.map Neg.neg) ∧
    ∀ r, 2*r ≤ m → (Threshold.pathCoeff m r : ℝ) = (z.map (fun x => x^2)).esymm r := by
  obtain ⟨z,hz,he,hp⟩ := paired_spectrum m
  refine ⟨z,hz,he,?_⟩
  intro r hr
  let s := z.map (fun x => x^2)
  have hc : s.card = m/2 := by simp [s,hz]
  have h := PathJacobi.charpoly_coeff m r hr
  rw [hp, show m-2*r = 2*(m/2-r) + m%2 by omega, coeff_X_pow_mul, coeff_expand_mul' (by decide : 0 < 2)] at h
  change (linearFactors s).coeff (m/2-r) = _ at h
  rw [linearFactors, Multiset.prod_X_sub_C_coeff s (by omega), hc, show m/2-(m/2-r)=r by omega] at h
  exact (mul_left_cancel₀ (pow_ne_zero r (by norm_num : (-1 : ℝ) ≠ 0)) h).symm

/-- The first path coefficient counts every single edge with its squared weight. -/
theorem first_moment (m : ℕ) : Threshold.pathCoeff m 1 = ∑ j ∈ Finset.range m, j^2 := by
  induction m with
  | zero => simp [Threshold.pathCoeff]
  | succ m ih =>
    cases m with
    | zero => simp [Threshold.pathCoeff]
    | succ m => rw [Finset.sum_range_succ, ← ih, Threshold.pathCoeff]; simp [Threshold.pathCoeff]

/-- Six times the first matching moment gives the integer numerator of the threshold. -/
theorem first_moment_value (m : ℕ) : 6 * Threshold.pathCoeff m 1 = m*(m-1)*(2*m-1) := by
  rw [first_moment]
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => decide
    | succ m =>
      rw [Finset.sum_range_succ, mul_add, ih]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [show 2*(m+1)-1=2*m+1 by omega, show 2*(m+1+1)-1=2*m+3 by omega]
      ring

private theorem first_esymm (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map, Function.comp_def]

private theorem trace_sq_eq (m : ℕ) : ((PathJacobi.J m)^2).trace =
    ((eigenvalues m).map (fun x => x^2)).sum := by
  let A := PathJacobi.J m
  let h : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact PathJacobi.symmetric m
  let U := (h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  let D := diagonal h.eigenvalues
  have he : A = U * D * star U := h.spectral_theorem
  have hu : star U * U = 1 := unitary.coe_star_mul_self h.eigenvectorUnitary
  have hp : A^2 = U * (D*D) * star U := by
    calc A^2 = (U * D * star U) * (U * D * star U) := by rw [pow_two]; exact congrArg₂ (· * ·) he he
         _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
         _ = _ := by rw [hu, mul_one, Matrix.mul_assoc U D D]
  change (A^2).trace = _
  rw [hp, trace_mul_cycle, hu, one_mul, show D*D = diagonal (fun i => h.eigenvalues i * h.eigenvalues i) from diagonal_mul_diagonal .., trace_diagonal]
  simp only [eigenvalues, Multiset.map_map, Function.comp_def, pow_two, Finset.sum]

/-- The squared Jacobi trace counts each one-edge matching at its two ends. -/
theorem trace_first_moment (m : ℕ) (hm : 2 ≤ m) :
    ((PathJacobi.J m)^2).trace / 2 = (Threshold.pathCoeff m 1 : ℝ) := by
  obtain ⟨z,_,he,hc⟩ := pathCoeff_esymm m
  rw [trace_sq_eq, he, hc 1 (by omega), first_esymm]
  simp [Multiset.map_add, Multiset.map_map, Function.comp_def, add_div]

/-- Maclaurin's inequality applied to the actual squared path eigenvalues. -/
theorem spectral_coefficient_bound (m r : ℕ) (hm : 2 ≤ m) :
    (Threshold.pathCoeff m r : ℝ) ≤ ((m/2).choose r : ℝ) *
      ((Threshold.pathCoeff m 1 : ℝ)/(m/2 : ℕ))^r := by
  by_cases hr : 2*r ≤ m
  · obtain ⟨z,hz,_,he⟩ := pathCoeff_esymm m
    let s := z.map (fun x => x^2)
    have hc : s.card = m/2 := by simp [s,hz]
    have hs : ∀ t ∈ s, 0 ≤ t := by
      intro t ht
      obtain ⟨a,_,rfl⟩ := Multiset.mem_map.mp ht
      exact sq_nonneg a
    have h1 : (Threshold.pathCoeff m 1 : ℝ) = s.sum := (he 1 (by omega)).trans (first_esymm s)
    rw [he r hr, h1]
    simpa only [hc] using PathMeans.maclaurin_multiset s hs r
  · rw [Matchings.pathCoeff_outside (lt_of_not_ge hr)]
    simp [Nat.choose_eq_zero_of_lt (by omega : m/2 < r)]

/-- The paper's integer threshold, derived from the real spectrum and its arithmetic mean. -/
theorem spectral_threshold (m b r : ℕ) (hm : 2 ≤ m)
    (h : m*(m-1)*(2*m-1) ≤ 6*(m/2)*b) :
    Threshold.pathCoeff m r ≤ (m/2).choose r * b^r := by
  have hh : Threshold.pathCoeff m 1 ≤ m/2*b := by
    rw [← first_moment_value, Nat.mul_assoc] at h
    omega
  have hpos : 0 < (m/2 : ℕ) := by omega
  have hav : (Threshold.pathCoeff m 1 : ℝ)/(m/2 : ℕ) ≤ b := by
    apply (div_le_iff₀ (by exact_mod_cast hpos)).2
    rw [mul_comm]
    exact_mod_cast hh
  exact_mod_cast (spectral_coefficient_bound m r hm).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hav r) (by positivity))

end
end BlockPermanents.PathSpectrum
