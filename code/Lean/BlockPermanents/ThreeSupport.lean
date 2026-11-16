import BlockPermanents.PairBound

/-! # The last contraction of the three-packet bend

For every spectator word, contracting the remaining paired wires is the
trace of a concrete matrix. Its adjoint columns lie in the support of the
marked packet, including for the sum of the two routes of the packet clasp.
-/

namespace BlockPermanents.ThreeSupport
open Bend Closures PairBound
open scoped BigOperators Matrix
noncomputable section

/-- The proper U-cut with the spectator word fixed, including both orders
of the packet average. -/
def partialThree {d k : ℕ} (F G H : Word d k → ℂ) (r : CutIndex k k) (t : Word d k) :
    Matrix (Word d (k-r)) (Word d (k-r)) ℂ :=
  (1/2 : ℂ) • (F t • cutMatrix G H r + G t • cutMatrix F H r)

/-- The two routes of the full packet cap. -/
def fullThree {d k : ℕ} (F G H : Word d k → ℂ) (t : Word d k) : ℂ :=
  (F t * bracket H G + G t * bracket H F) / 2

theorem cut_adjoint {d k : ℕ} {G H : Word d k → ℂ} (hG : Symmetric G)
    (hH : Symmetric H) (r : CutIndex k k) :
    (cutMatrix G H r)ᴴ = cutMatrix H G r := by
  ext a b
  rw [Matrix.conjTranspose_apply, cutMatrix_entry hG hH, cutMatrix_entry hH hG]
  simp [map_sum, mul_comm]

theorem complete_three {d k : ℕ} {F G H : Word d k → ℂ} (hF : Symmetric F)
    (hG : Symmetric G) (hH : Symmetric H) (r : CutIndex k k) (t : Word d k) :
    (partialThree F G H r t).trace = fullThree F G H t := by
  simp [partialThree, fullThree, Matrix.trace_smul, Matrix.trace_add, cut_trace hG hH,
    cut_trace hF hH, smul_eq_mul, bracket, mul_comm, div_eq_mul_inv]
  ring

theorem partialThree_cols {d k : ℕ} {F G : Word d k → ℂ} (hF : Symmetric F)
    (hG : Symmetric G) (x : Fin k → Fin d → ℂ) (r : CutIndex k k) (t : Word d k)
    (b : Word d (k-r)) : (fun a => (partialThree F G (packet x) r t)ᴴ a b) ∈
      PacketSupport.splitSupport x r (cut_le r) := by
  let W := PacketSupport.splitSupport x r (cut_le r)
  have h := W.smul_mem (star (1/2 : ℂ)) (W.add_mem
    (W.smul_mem (star (F t)) (cut_columns_mem x hG r b))
    (W.smul_mem (star (G t)) (cut_columns_mem x hF r b)))
  simpa only [partialThree, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    cut_adjoint hF (Bridges.packet_symmetric _ _ _), cut_adjoint hG (Bridges.packet_symmetric _ _ _),
    Matrix.smul_apply, Matrix.add_apply] using h

/-- The squared trace estimate for any spectator matrix whose adjoint
columns lie in one supported space. It applies to sums of cap routes. -/
theorem trace_of_adjoint_columns {I : Type*} [Fintype I]
    (W : Submodule ℂ (I → ℂ)) (M : Matrix I I ℂ)
    (hcol : ∀ j, (fun i => Mᴴ i j) ∈ W) :
    Complex.normSq M.trace ≤ (Module.finrank ℂ W : ℝ) * ∑ i, ∑ j, Complex.normSq (M i j) := by
  have h := TraceBound.trace_normSq_le W Mᴴ hcol
  rw [Matrix.trace_conjTranspose] at h
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj,
    Finset.sum_comm (f := fun i j => Complex.normSq (M j i))] using h

/-- The completed cap bound on actual packet inputs, with no choice of an
adapted basis. Any r is allowed. At r=k−1 the bound is precisely k. -/
theorem fullThree_le {d k : ℕ} {F G : Word d k → ℂ} (hF : Symmetric F)
    (hG : Symmetric G) (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :
    energy (fullThree F G (packet x)) ≤ (k.choose r : ℝ) *
      ∑ t, ∑ a, ∑ b, Complex.normSq (partialThree F G (packet x) r t a b) := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have h := trace_of_adjoint_columns _ _ (partialThree_cols hF hG x r t)
  rw [complete_three hF hG (Bridges.packet_symmetric _ _ _) r t] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact_mod_cast PacketSupport.splitSupport_dimension x r (cut_le r)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Last proper cut at positive thickness. -/
def lastProper (k : ℕ) : CutIndex k k := ⟨k-1, by simp; omega⟩

theorem last_weight_nonnegative {d k : ℕ} (hk : 2 ≤ k) {F G : Word d k → ℂ}
    (hF : Symmetric F) (hG : Symmetric G) (x : Fin k → Fin d → ℂ) :
    0 ≤ 2 * (k : ℝ)^2 *
      (∑ t, ∑ a, ∑ b, Complex.normSq (partialThree F G (packet x) (lastProper k) t a b)) -
      (9/4 : ℝ) * energy (fullThree F G (packet x)) := by
  have he := fullThree_le hF hG x (lastProper k)
  have hc : k.choose (k-1) = k := by
    rw [Nat.choose_symm (show 1 ≤ k by omega), Nat.choose_one_right]
  change _ ≤ (k.choose (k-1) : ℝ) * _ at he
  rw [hc] at he
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let E := ∑ t, ∑ a, ∑ b, Complex.normSq (partialThree F G (packet x) (lastProper k) t a b)
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change 0 ≤ 2 * (k : ℝ)^2 * E - _ * _
  change _ ≤ (k : ℝ) * E at he
  have hscale : (9/4 : ℝ) ≤ 2 * k := by linarith
  have hex := mul_le_mul_of_nonneg_right hscale (mul_nonneg (Nat.cast_nonneg k) hE)
  linarith only [hex, he]

end
end BlockPermanents.ThreeSupport
