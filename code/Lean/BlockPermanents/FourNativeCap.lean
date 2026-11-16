import BlockPermanents.FullCapBoundary
import BlockPermanents.FourRoutes

/-! # The full contraction at packet one on the ordered three-packet boundary

The two remaining ordinary outputs keep their order. The marked map and the
ordinary map may be rectangular, so the identity also applies on a subspace. -/
namespace BlockPermanents.FourNativeCap
open Bend ThreeTransfer ThreeGeneralOpen
open scoped Matrix BigOperators
noncomputable section

variable {K I J : Type*} [Fintype K] [DecidableEq K]
abbrev O (K : Type*) := Fin 3 → K
abbrev T (K : Type*) := K × K

def order (K : Type*) : O K ≃ T K × K where
  toFun x := ((x 1,x 2),x 0)
  invFun a := ![a.2,a.1.1,a.1.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

def swapMatrix : Matrix (O K × K) (O K × K) ℂ :=
  fun i j => ThreeTransfer.cross ((order K i.1),i.2) ((order K j.1),j.2)

def half (P : Matrix (O K) I ℂ) (N : Matrix K J ℂ) : Matrix (T K) (I×J) ℂ :=
  TwoFullCaps.full (fun a i => P ((order K).symm a) i) N

/-- Bend an actual whole-packet interchange with arbitrary maps at its feet. -/
theorem bend_full (P Q : Matrix (O K) I ℂ) (N : Matrix K J ℂ) :
    partialTranspose ((legs P N)ᴴ * swapMatrix * legs Q N) = (half P N)ᴴ * half Q N := by
  let e := (order K).prodCongr (Equiv.refl K)
  have eqn : (legs P N)ᴴ * swapMatrix * legs Q N =
      TwoFullCaps.crossing (fun a i => P ((order K).symm a) i)
        (fun a i => Q ((order K).symm a) i) N := by
    ext i j
    simp only [TwoFullCaps.crossing, Matrix.mul_apply]
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    rw [← e.symm.sum_comp]
    rfl
  rw [eqn]
  exact TwoFullCaps.bend_crossing _ _ _

theorem half_sub_smul (P Q : Matrix (O K) I ℂ) (N : Matrix K J ℂ) (a : ℚ) :
    half (P-a • Q) N = half P N - a • half Q N := by
  ext t x
  simp only [half, TwoFullCaps.full, Matrix.sub_apply, Matrix.smul_apply, sub_mul,
    smul_mul_assoc,Finset.sum_sub_distrib,← Finset.smul_sum]

/-- Projection on spectator outputs commutes with capping packet one.
This gives the half called pu in (5C.3). -/
def survivor (p : Matrix (T K) (T K) ℂ) : Matrix (O K) (O K) ℂ :=
  fun i j => if i 0 = j 0 then p (i 1,i 2) (j 1,j 2) else 0

theorem half_survivor [Fintype I] (p : Matrix (T K) (T K) ℂ)
    (F : Matrix (O K) I ℂ) (N : Matrix K J ℂ) :
    half (survivor p * F) N = p * half F N := by
  ext t x
  simp only [half, TwoFullCaps.full, Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => enter [2,b]; rw [← (order K).symm.sum_comp]
  simp only [Fintype.sum_prod_type, survivor,order,Equiv.coe_fn_symm_mk,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,ite_mul,zero_mul,mul_ite]
  simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

end
end BlockPermanents.FourNativeCap
