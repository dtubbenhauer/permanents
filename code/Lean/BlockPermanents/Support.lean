import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Orthogonal cuts on a marked support (Sections 2D, 3D and 7A). -/
namespace BlockPermanents.Support
noncomputable section
open scoped BigOperators Matrix

variable {U Z T S V : Type*}

/-- The square obtained by gluing a half to its adjoint. -/
def reflected [Fintype Z] (Y : Matrix Z U ℂ) : Matrix U U ℂ := Yᴴ * Y

/-- Orthogonal resolution at a seam, for every input and arbitrary spectators. -/
theorem orthogonal_cut [Fintype Z] [DecidableEq Z] (Y : Matrix Z U ℂ)
    (P : Matrix Z Z ℂ) (hstar : Pᴴ = P) (hsq : P * P = P) :
    reflected Y = reflected (P * Y) + reflected ((1 - P) * Y) := by
  have hcomp : (1-P)*(1-P) = 1-P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hsq, sub_self, sub_zero]
  have glue (Q : Matrix Z Z ℂ) (hQ : Qᴴ = Q) (hQ' : Q*Q=Q) :
      reflected (Q*Y) = Yᴴ*(Q*Y) := by
    unfold reflected
    rw [Matrix.conjTranspose_mul, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ']
  rw [glue P hstar hsq, glue (1-P) (by simp [hstar]) hcomp, ← Matrix.mul_add,
    ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  rfl

/-- Contract a supported dual color with its ordinary partner. The other
tensor factors are indexed by T and pass straight through this cap. -/
def lastCap [DecidableEq T] [DecidableEq V] (j : S ↪ V) :
    Matrix T (T × (S × V)) ℂ :=
  fun t x => if t = x.1 ∧ j x.2.1 = x.2.2 then 1 else 0

theorem lastCap_bubble [Fintype T] [Fintype S] [Fintype V]
    [DecidableEq T] [DecidableEq V] (j : S ↪ V) :
    lastCap (T := T) j * (lastCap j)ᴴ = (Fintype.card S : ℂ) • (1 : Matrix T T ℂ) := by
  classical
  ext a b
  simp only [lastCap, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite star, star_one, star_zero, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases h : a = b
  · subst b
    simp [ite_and, eq_comm]
  · simp [ite_and, h, eq_comm]

/-- Closing one further thin pair splits its squared norm into the square
orthogonal to the cup and the full cap with coefficient 1/d. -/
theorem resolve_last_cap [Fintype Z] [DecidableEq Z] [Fintype T] [DecidableEq T]
    (e : Matrix T Z ℂ) (Y : Matrix Z U ℂ) (d : ℕ) (hd : 0 < d)
    (he : e * eᴴ = (d : ℂ) • (1 : Matrix T T ℂ)) :
    let P := (d : ℂ)⁻¹ • (eᴴ * e)
    reflected Y = reflected ((1-P)*Y) + (d : ℂ)⁻¹ • reflected (e*Y) := by
  let P := (d : ℂ)⁻¹ • (eᴴ * e)
  change _ = reflected ((1-P)*Y) + _
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hs : Pᴴ = P := by simp [P, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  have hi : P * P = P := by
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc e, he, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, smul_smul]
    simp [mul_assoc, hn]
  have hpy : reflected (P*Y) = (d : ℂ)⁻¹ • reflected (e*Y) := by
    unfold reflected
    rw [Matrix.conjTranspose_mul, hs, ← Matrix.mul_assoc (Yᴴ * P), Matrix.mul_assoc Yᴴ P P, hi]
    simp [P, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [orthogonal_cut Y P hs hi, hpy, add_comm]

/-- The coefficient left in the three-packet decomposition stays positive
throughout the support range 1 ≤ d ≤ k, k ≥ 2. -/
theorem three_full_cap_weight (k d : ℕ) (hk : 2 ≤ k) (hd : 0 < d) (hb : d ≤ k) :
    0 < 2*(k : ℝ)^2 / d - 9/4 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hb' : (d : ℝ) ≤ k := by exact_mod_cast hb
  apply sub_pos.mpr
  apply (lt_div_iff₀ hd').mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hk') (show (0:ℝ) ≤ k by positivity)]

end
end BlockPermanents.Support
