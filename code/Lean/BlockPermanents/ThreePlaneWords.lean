import BlockPermanents.ThreeLastRouted
import BlockPermanents.TensorCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Tensor powers of the marked embedding and the last surviving marked letter. -/
namespace BlockPermanents.ThreePlane
open Bend TensorCoordinates
open scoped Matrix BigOperators
noncomputable section

private theorem clasp_as_sum {d k : ℕ} (u : Word d k → ℂ) :
    (symClasp d k).mulVec u = (k.factorial : ℂ)⁻¹ •
      ∑ p : Equiv.Perm (Fin k), Transfer.tensorAction (Fin k) (Fin d) p.symm u := by
  rw [Bridges.symClasp_action]
  ext w
  simp [Closures.clasp, Closures.sumSlots, Transfer.tensorAction, Finset.sum_apply]

/-- The symmetric clasp commutes with every rectangular coordinate map on the letters. -/
theorem clasp_power {d s : ℕ} (k : ℕ) (E : Matrix (Fin d) (Fin s) ℂ) :
    symClasp d k * power (Fin k) E = power (Fin k) E * symClasp s k := by
  have act (v : Word s k → ℂ) :
      (symClasp d k).mulVec ((power (Fin k) E).mulVec v) =
        (power (Fin k) E).mulVec ((symClasp s k).mulVec v) := by
    rw [clasp_as_sum, clasp_as_sum]
    simp only [← Matrix.mulVecLin_apply, map_smul, map_sum]
    simp only [Matrix.mulVecLin_apply, naturality]
  ext w z
  have h := congrFun (act (Pi.single z 1)) w
  simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] using h

/-- Changing the marked alphabet preserves symmetric tensors. -/
theorem power_symmetric {d s k : ℕ} (E : Matrix (Fin d) (Fin s) ℂ)
    {v : Word s k → ℂ} (hv : Symmetric v) :
    Symmetric ((power (Fin k) E).mulVec v) := by
  change (symClasp d k).mulVec ((power (Fin k) E).mulVec v) = _
  rw [Matrix.mulVec_mulVec, clasp_power, ← Matrix.mulVec_mulVec, hv]

open private allSlots from BlockPermanents.ThreeLastRouted in
private theorem power_last {d s k : ℕ} (hk : 1 ≤ k) (E : Matrix (Fin d) (Fin s) ℂ)
    (b : Fin d) (v : Word d (k-1)) (a : Fin s) (w : Word s (k-1)) :
    power (Fin k) E (allSlots hk (b,v)) (allSlots hk (a,w)) =
      E b a * power (Fin (k-1)) E v w := by
  let h : k-(k-1) + (k-1) = k := by omega
  change (∏ t, E (Fin.append (fun _ : Fin (k-(k-1)) => b) v ((finCongr h).symm t))
    (Fin.append (fun _ : Fin (k-(k-1)) => a) w ((finCongr h).symm t))) = _
  rw [← (finCongr h).prod_comp]
  simp only [Equiv.symm_apply_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, show k-(k-1)=1 by omega, pow_one]
  rfl

open private allSlots from BlockPermanents.ThreeLastRouted in
/-- With the other marked letters fixed, the remaining slice lies in the range
of E. The coefficient vector is obtained by transforming the k−1 fixed letters. -/
theorem power_slice {d s k : ℕ} {J : Type*} (hk : 1 ≤ k) (E : Matrix (Fin d) (Fin s) ℂ)
    (D : Matrix (Word s k) J ℂ) (v : Word d (k-1)) (j : J) :
    ∃ c, E.mulVec c = fun b => (power (Fin k) E * D) (allSlots hk (b,v)) j := by
  refine ⟨fun a => ∑ w : Word s (k-1), power (Fin (k-1)) E v w * D (allSlots hk (a,w)) j, ?_⟩
  funext b
  rw [Matrix.mul_apply, ← (allSlots (d:=s) hk).sum_comp, Fintype.sum_prod_type]
  simp only [power_last, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

end
end BlockPermanents.ThreePlane
