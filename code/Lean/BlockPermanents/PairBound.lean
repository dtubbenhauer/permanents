import BlockPermanents.Bridges
import BlockPermanents.PacketSupport
import BlockPermanents.TraceBound
import BlockPermanents.SchurNormalization
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Nat.Choose.Sum

/-! # Completing a partial contraction (Section 7A)

A surviving pair of equally thick cables is a square matrix in word
coordinates. Its trace closes all remaining pairs. The column-space estimate
only uses decomposability of the positive input.
-/

namespace BlockPermanents.PairBound
open Closures Bend
open scoped BigOperators
noncomputable section

theorem cut_le {k : ℕ} (r : CutIndex k k) : r.val ≤ k := by
  simpa using Nat.le_of_lt_succ r.isLt

/-- Joining the two outgoing words recovers an arbitrary incoming word exactly once. -/
def splitWords (d k : ℕ) (r : CutIndex k k) :
    Word d (k-r) × Word d r ≃ Word d k where
  toFun z := fun t => Fin.append z.1 z.2 (Fin.cast (Nat.sub_add_cancel (cut_le r)).symm t)
  invFun w := (fun a => w (Fin.cast (Nat.sub_add_cancel (cut_le r)) (Fin.castAdd r a)),
               fun b => w (Fin.cast (Nat.sub_add_cancel (cut_le r)) (Fin.natAdd (k-r) b)))
  left_inv z := by
    cases z with | mk a b => simp [-Fin.natAdd_eq_addNat]
  right_inv w := by
    funext t
    have h := congrFun (Fin.append_castAdd_natAdd (f := fun u =>
       w (Fin.cast (Nat.sub_add_cancel (cut_le r)) u))) (Fin.cast (Nat.sub_add_cancel (cut_le r)).symm t)
    exact h

/-- Partial contraction before the last trace. -/
def cutMatrix {d k : ℕ} (F H : Word d k → ℂ) (r : CutIndex k k) :
    Matrix (Word d (k-r)) (Word d (k-r)) ℂ :=
  fun a b => (wordCap d k k r).mulVec (product F (fun i => star (H i))) (a,b)

theorem cutMatrix_entry {d k : ℕ} {F H : Word d k → ℂ}
    (hF : Bend.Symmetric F) (hH : Bend.Symmetric H) (r : CutIndex k k) (a b : Word d (k-r)) :
    cutMatrix F H r a b =
      ∑ t : Word d r, F (splitWords d k r (a,t)) * star (H (splitWords d k r (b,t))) := by
  rw [cutMatrix, wordCap, cap_product]
  apply Finset.sum_congr rfl
  intro t _
  rw [split_symmetric _ hF, split_symmetric _ hH]
  rfl

/-- Completing any number of previously contracted pairs gives the same full pairing. -/
theorem cut_trace {d k : ℕ} {F H : Word d k → ℂ}
    (hF : Bend.Symmetric F) (hH : Bend.Symmetric H) (r : CutIndex k k) :
    (cutMatrix F H r).trace = ∑ t, F t * star (H t) := by
  unfold Matrix.trace
  simp only [Matrix.diag, cutMatrix_entry hF hH]
  let f := fun u : Word d (k-r) × Word d r => F (splitWords d k r u) * star (H (splitWords d k r u))
  exact (Fintype.sum_prod_type f).symm.trans ((splitWords d k r).sum_comp (fun t => F t * star (H t)))

/-- The Frobenius norm of the cut matrix is the energy of the halfweb. -/
theorem cut_frobenius {d k : ℕ} (F H : Word d k → ℂ) (r : CutIndex k k) :
    ∑ a, ∑ b, Complex.normSq (cutMatrix F H r a b) =
      energy ((wordCap d k k r).mulVec (product F (fun i => star (H i)))) :=
  (Fintype.sum_prod_type (fun u : Word d (k-r) × Word d (k-r) => Complex.normSq (cutMatrix F H r u.1 u.2))).symm

/-- Each column lies in the subset-indexed support of the first packet.
The second input can be any symmetric tensor. -/
theorem cut_columns_mem {d k : ℕ} (x : Fin k → Fin d → ℂ)
    {H : Word d k → ℂ} (hH : Bend.Symmetric H) (r : CutIndex k k) (b : Word d (k-r)) :
    (fun a => cutMatrix (packet x) H r a b) ∈ PacketSupport.splitSupport x r (cut_le r) := by
  simp only [cutMatrix_entry (Bridges.packet_symmetric d k x) hH]
  convert PacketSupport.split_contraction_mem x r (cut_le r) (fun t => star (H (splitWords d k r (b,t)))) using 1
  funext a
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

/-- Number of independent surviving columns after contraction. -/
theorem cut_rank {d k : ℕ} (x : Fin k → Fin d → ℂ) {H : Word d k → ℂ}
    (hH : Bend.Symmetric H) (r : CutIndex k k) : (cutMatrix (packet x) H r).rank ≤ k.choose r := by
  rw [Matrix.rank_eq_finrank_span_cols]
  apply le_trans _ (PacketSupport.splitSupport_dimension x r (cut_le r))
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨b,rfl⟩
  exact cut_columns_mem x hH r b

private theorem normSq_trace_pair {I : Type*} [Fintype I] (F H : I → ℂ) :
    Complex.normSq (∑ t, F t * star (H t)) = Complex.normSq (bracket F H) := by
  have h : (∑ t, F t * star (H t)) = (starRingEnd ℂ) (bracket F H) := by
    simp only [bracket, map_sum, map_mul, Complex.conj_conj]
    rfl
  rw [h, Complex.normSq_conj]

/-- The r-th cut carries at least choose(k,r) copies of the completed cap. -/
theorem full_cap_copies {d k : ℕ} (x : Fin k → Fin d → ℂ) {H : Word d k → ℂ}
    (hH : Bend.Symmetric H) (r : CutIndex k k) :
    (k.choose r : ℝ) * Complex.normSq (bracket (packet x) H) ≤ cutTerm (packet x) H r := by
  let W := PacketSupport.splitSupport x r (cut_le r)
  have h := TraceBound.trace_normSq_le W _ (cut_columns_mem x hH r)
  rw [cut_trace (Bridges.packet_symmetric _ _ _) hH, normSq_trace_pair, cut_frobenius] at h
  have hr : (Module.finrank ℂ W : ℝ) ≤ (k.choose r : ℝ) := by
    exact_mod_cast PacketSupport.splitSupport_dimension x r (cut_le r)
  have hn := h.trans (mul_le_mul_of_nonneg_right hr (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ (k.choose r : ℝ) from Nat.cast_nonneg _)
  simpa only [cutTerm, weight, Nat.cast_mul, mul_assoc] using hm

private theorem choose_sum_nonzero (k : ℕ) :
    ∑ r ∈ (Finset.univ.erase (zeroCut k)), (k.choose r : ℝ) = (2:ℝ)^k - 1 := by
  have h : ∑ r : CutIndex k k, k.choose r = 2^k := by
    simp only [CutIndex, min_self]
    rw [Fin.sum_univ_eq_sum_range, min_self, Nat.sum_range_choose]
  have he := Finset.sum_erase_add Finset.univ (fun r : CutIndex k k => (k.choose r : ℝ))
    (Finset.mem_univ (zeroCut k))
  have hc : ∑ r : CutIndex k k, (k.choose r : ℝ) = 2^k := by exact_mod_cast h
  rw [hc] at he
  simpa [zeroCut] using (eq_sub_of_add_eq he)

/-- Homogeneous, unit-free form of Lemma 7A.1. Only the first input has to
be a matrix packet. The second input is an arbitrary symmetric tensor. -/
theorem full_caps_from_pair {d k : ℕ} (homogeneous : SchurNormalization.HomogeneousSchur d k k)
    (x : Fin k → Fin d → ℂ) {H : Word d k → ℂ} (hH : Bend.Symmetric H) :
    energy (packet x) * energy H + ((2:ℝ)^k - 1) * Complex.normSq (bracket (packet x) H) ≤
      (((k+k).choose k : ℂ) * quadratic (totalClasp d k k) (product (packet x) H)).re := by
  have h := congrArg Complex.re (closed_bent_schur d k k
    (SchurNormalization.homogeneousSchur_implies_unbent _ _ _ homogeneous) (packet x) H)
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at h
  change ((k+k).choose k : ℝ) * (quadratic _ _).re = ∑ r, cutTerm (packet x) H r at h
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [h]
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (zeroCut k))]
  have h0 : cutTerm (packet x) H (zeroCut k) = energy (packet x) * energy H := by
    rw [cutTerm, zero_cap_energy (Bridges.packet_symmetric _ _ _) hH]
    simp [weight, zeroCut]
  rw [h0, add_comm, ← choose_sum_nonzero k, Finset.sum_mul]
  exact add_le_add_right (Finset.sum_le_sum (fun r _ => full_cap_copies x hH r)) _

/-- The pair bound directly in the units of the fine Gram permanent. -/
theorem two_packet_lower_bound {d k : ℕ} (homogeneous : SchurNormalization.HomogeneousSchur d k k)
    (x : Fin 2 → Fin k → Fin d → ℂ) :
    energy (packet (x 0)) * energy (packet (x 1)) +
      ((2:ℝ)^k - 1) * Complex.normSq (bracket (packet (x 0)) (packet (x 1))) ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re := by
  rw [← Bridges.two_fine_permanent x]
  exact full_caps_from_pair homogeneous (x 0) (Bridges.packet_symmetric _ _ _)

/-- Tensoring the second input with a fixed first input, then projecting
onto the symmetric cable of twice the thickness. -/
def symmetricProductMatrix {d k : ℕ} (F : Word d k → ℂ) :
    Matrix (Word d (k+k)) (Word d k) ℂ :=
  symClasp d (k+k) * (Matrix.of (fun (w : Word d (k+k)) (v : Word d k) => if v = fun t => w (Fin.natAdd k t)
    then F (fun t => w (Fin.castAdd k t)) else 0))

theorem symmetricProductMatrix_action {d k : ℕ} (F H : Word d k → ℂ) :
    (symmetricProductMatrix F).mulVec H = clasp
      (fun w : Word d (k+k) => F (fun t => w (Fin.castAdd k t)) * H (fun t => w (Fin.natAdd k t))) := by
  rw [symmetricProductMatrix, ← Matrix.mulVec_mulVec, Bridges.symClasp_action]
  apply congrArg (fun u : Word d (k+k) → ℂ => clasp u)
  funext w
  simp [Matrix.mulVec, dotProduct, ite_mul, Matrix.of_apply]

theorem projected_symmetric (d k : ℕ) (v : Word d k → ℂ) :
    Bend.Symmetric ((symClasp d k).mulVec v) := by
  simp only [Bend.Symmetric, Bridges.symClasp_action]
  funext w
  change ((Fintype.card (Fin k)).factorial : ℂ)⁻¹ * (∑ p : Equiv.Perm (Fin k),
    clasp v (w ∘ p.symm)) = _
  simp only [clasp_invariant, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_mul]

theorem product_quadratic_energy {d k : ℕ} (F H : Word d k → ℂ) :
    quadratic (totalClasp d k k) (product F H) = (energy ((symmetricProductMatrix F).mulVec H) : ℂ) := by
  let z := fun w : Word d (k+k) => F (fun t => w (Fin.castAdd k t)) * H (fun t => w (Fin.natAdd k t))
  have h : product F H = z ∘ Bridges.joinWords d k := by
    funext u
    simp [product, z, Function.comp_def, Bridges.joinWords, -Fin.natAdd_eq_addNat]
  have q := Bridges.quadratic_reindex (Bridges.joinWords d k) (symClasp d (k+k)) z
  change quadratic (totalClasp d k k) _ = _ at q
  rw [h, q, Bridges.quadratic_bracket, Bridges.symClasp_action, ← bracket_clasp, Coarse.bracket_self,
    symmetricProductMatrix_action]

private theorem energy_scale {I : Type*} [Fintype I] (a : ℂ) (v : I → ℂ) :
    energy (fun i => a * v i) = Complex.normSq a * energy v := by
  simp [energy, Complex.normSq_mul, Finset.mul_sum]

private theorem product_scale {d k : ℕ} (a : ℂ) (F H : Word d k → ℂ) :
    (symmetricProductMatrix (fun i => a * F i)).mulVec H =
      fun w => a * (symmetricProductMatrix F).mulVec H w := by
  rw [symmetricProductMatrix_action, symmetricProductMatrix_action]
  funext w
  simp only [clasp, sumSlots, mul_assoc, ← Finset.mul_sum]
  ring

/-- The normalized statement of Lemma 7A.1 in the original symmetric
product norm, for an arbitrary proportional first packet and an arbitrary
symmetric second input. -/
theorem full_caps_normalized {d k : ℕ} (homogeneous : SchurNormalization.HomogeneousSchur d k k)
    {F H : Word d k → ℂ}
    (hF : ∃ (a : ℂ) (x : Fin k → Fin d → ℂ), F = fun i => a * packet x i)
    (hunit : energy F = 1) (hH : Bend.Symmetric H) :
    energy H + ((2:ℝ)^k - 1) * Complex.normSq (bracket F H) ≤
      ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix F).mulVec H) := by
  obtain ⟨a,x,rfl⟩ := hF
  have h := full_caps_from_pair homogeneous x hH
  rw [product_quadratic_energy, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  rw [energy_scale] at hunit
  rw [product_scale, energy_scale]
  have hb : bracket (fun i => a * packet x i) H = (starRingEnd ℂ) a * bracket (packet x) H := by
    simpa only [one_mul, mul_one] using bracket_scale a 1 (packet x) H
  rw [hb, Complex.normSq_mul, Complex.normSq_conj]
  have hw := mul_le_mul_of_nonneg_left h (Complex.normSq_nonneg a)
  rw [mul_add, ← mul_assoc _ (energy (packet x)), hunit, one_mul] at hw
  convert hw using 1 <;> ring

end
end BlockPermanents.PairBound
