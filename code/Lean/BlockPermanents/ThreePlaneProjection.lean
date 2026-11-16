import BlockPermanents.ThreePlaneCap

/-! # The cup and its orthogonal complement at the last thin cut -/
namespace BlockPermanents.ThreePlane
open Bend ThreeLastCap
open scoped BigOperators Matrix
noncomputable section
variable {T I : Type*} [Fintype T] [DecidableEq T] {d s : ℕ}

/-- The component along the closing cup, with arbitrary spectators and inputs. -/
def cupComponent (E : Matrix (Fin d) (Fin s) ℂ) (Y : Matrix (T × Pair d) I ℂ) :
    Matrix (T × Pair d) I ℂ :=
  (s : ℂ)⁻¹ • ((planeCap E)ᴴ * (planeCap E * Y))

theorem perpendicular_eq_sub (E : Matrix (Fin d) (Fin s) ℂ) (Y : Matrix (T × Pair d) I ℂ) :
    perpendicular E Y = Y - cupComponent E Y := by
  rw [perpendicular, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, cupComponent]

/-- The perpendicular half is annihilated when the same thin cap is closed again. -/
theorem perpendicular_closes_to_zero (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1)
    (hs : 0 < s) (Y : Matrix (T × Pair d) I ℂ) : planeCap (T:=T) E * perpendicular E Y = (0 : Matrix T I ℂ) := by
  have hn : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [perpendicular_eq_sub, Matrix.mul_sub, cupComponent, Matrix.mul_smul, ← Matrix.mul_assoc,
    cap_bubble E hE, Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hn, one_smul, sub_self]

theorem perpendicular_fixes_iff (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1)
    (hs : 0 < s) (Y : Matrix (T × Pair d) I ℂ) :
    perpendicular E Y = Y ↔ planeCap (T:=T) E * Y = (0 : Matrix T I ℂ) := by
  constructor
  · intro h
    rw [← h]
    exact perpendicular_closes_to_zero E hE hs Y
  · intro h
    rw [perpendicular_eq_sub, cupComponent, h, Matrix.mul_zero, smul_zero, sub_zero]

namespace Example

/-- Regard a two-by-two matrix as the boundary tensor with one ordinary and one dual letter. -/
def boundary (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Unit × Pair 2) Unit ℂ :=
  fun z _ => A (z.2.1 0) (z.2.2 0)

abbrev unit11 : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,0]
abbrev frame : Matrix (Fin 2) (Fin 2) ℂ := 1

open private cap_apply from BlockPermanents.ThreePlaneCap in
private theorem cap_unit11 : planeCap (T:=Unit) frame * boundary unit11 = (1 : Matrix Unit Unit ℂ) := by
  ext t j
  rw [cap_apply]
  norm_num [frame, boundary, Fin.sum_univ_two, Matrix.one_apply]

/-- The cup component of E₁₁ is half the identity. -/
theorem cup_e11 : cupComponent frame (boundary unit11) = boundary ((2 : ℂ)⁻¹ • 1) := by
  rw [cupComponent, cap_unit11, Matrix.mul_one]
  ext ⟨t,a,b⟩ j
  simp only [planeCap, frame, boundary, Matrix.conjTranspose_apply, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.smul_apply, Matrix.one_apply, Subsingleton.elim j t, if_true]
  by_cases hab : a 0 = b 0 <;> simp [hab, eq_comm]

/-- Its trace-free complement is the diagonal tensor (1/2,−1/2). -/
theorem perpendicular_e11 :
    perpendicular frame (boundary unit11) = boundary !![(1/2 : ℂ),0;0,-(1/2)] := by
  rw [perpendicular_eq_sub, cup_e11]
  have h (i j : Fin 2) : unit11 i j - ((2:ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j =
      (!![(1/2 : ℂ),0;0,-(1/2)] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]
  ext z j
  exact h (z.2.1 0) (z.2.2 0)

private theorem boundary_energy (A : Matrix (Fin 2) (Fin 2) ℂ) :
    energy (fun z => boundary A z ()) = ∑ a, ∑ b, Complex.normSq (A a b) := by
  simp only [energy,Fintype.sum_prod_type,Fintype.sum_unique,boundary]
  let e := Equiv.funUnique (Fin 1) (Fin 2)
  apply Eq.trans _ (Finset.sum_congr rfl fun a _ => e.sum_comp (fun b => Complex.normSq (A a b)))
  exact e.sum_comp (fun a => ∑ b : Word 2 1, Complex.normSq (A a (b 0)))

/-- Both branches on E₁₁ have squared norm one half. -/
theorem e11_energies :
    energy (fun z => perpendicular frame (boundary unit11) z ()) = 1/2 ∧
    energy (fun z => cupComponent frame (boundary unit11) z ()) = 1/2 := by
  rw [perpendicular_e11, cup_e11, boundary_energy, boundary_energy]
  norm_num [Fin.sum_univ_two,Matrix.one_apply,Complex.normSq_ofReal,
    show (2:ℂ)⁻¹ = ((2:ℝ)⁻¹ : ℂ) by norm_num, Complex.normSq_neg,Complex.normSq_inv,
    Complex.normSq_div, Complex.normSq_ofNat]

end Example
end
end BlockPermanents.ThreePlane
