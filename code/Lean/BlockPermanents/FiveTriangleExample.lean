import BlockPermanents.FiveProjection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The two signs of the cubic triangle gluing in Example 8B.2. -/
namespace BlockPermanents.FiveTriangleExample
open Closures Bend
open scoped Matrix
noncomputable section

/-- The packet box on a single leg, in word coordinates. -/
def box {D : Type*} (F : D → ℂ) : Matrix D D ℂ := fun i j => F i * star (F j)

/-- Reflect the G,F cable and glue it to the two caps passing through H. -/
theorem triangle_trace {D : Type*} [Fintype D] (F G H : D → ℂ) :
    star (bracket G F) * (bracket G H * bracket H F) =
      (box F * box G * box H).trace := by
  have pair (i j : D) : (box F * box G) i j = F i * bracket F G * star (G j) := by
    simp only [box,Matrix.mul_apply,bracket,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro _ _; simp only [starRingEnd_apply]; ring
  have triple (i j : D) : (box F * box G * box H) i j =
      F i * bracket F G * bracket G H * star (H j) := by
    simp only [Matrix.mul_apply,pair,box]
    have ghexp : bracket G H = ∑ t, star (G t) * H t := rfl
    rw [ghexp,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro _ _; ring
  have adj : star (bracket G F) = bracket F G := by
    simp [bracket,Complex.star_def,map_sum,mul_comm]
  rw [adj,Matrix.trace]
  simp only [Matrix.diag_apply,triple]
  rw [show bracket F G * (bracket G H * bracket H F) =
    (bracket F G * bracket G H) * bracket H F by ring]
  have hfexp : bracket H F = ∑ t, star (H t) * F t := rfl
  rw [hfexp,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro _ _; ring

/-- The coordinates are real. F and H are fixed, while the sign of one
coordinate of G changes between the two configurations. -/
def thin (negative : Bool) : Fin 3 → Fin 4 → ℂ :=
  ![![1,0,0,0], (if negative then ![-1/2,1/2,1/2,1/2] else ![1/2,1/2,1/2,-1/2]),
    ![1/2,1/2,1/2,1/2]]

def sign (negative : Bool) : ℂ := if negative then -1 else 1

def thinGram (negative : Bool) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then 1 else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then sign negative/2 else 1/2

theorem thin_gram (negative : Bool) :
    crossGram (thin negative) (thin negative) = thinGram negative := by
  have conjTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    exact star_ofNat _
  ext i j
  fin_cases i <;> fin_cases j <;> cases negative <;>
    norm_num [crossGram,thinGram,thin,sign,bracket,Fin.sum_univ_succ,conjTwo]

theorem thin_determinants : (crossGram (thin false) (thin false)).det = 1/2 ∧
    (crossGram (thin true) (thin true)).det = 0 := by
  rw [thin_gram,thin_gram,Matrix.det_fin_three,Matrix.det_fin_three]
  norm_num (config := { decide := true }) [thinGram,sign]

theorem thin_minors (negative : Bool) (i j : Fin 3) (h : i ≠ j) :
    let g := crossGram (thin negative) (thin negative)
    g i i * g j j - g i j * g j i = 3/4 := by
  dsimp only
  rw [thin_gram]
  fin_cases i <;> fin_cases j <;> cases negative <;>
    norm_num (config := { decide := true }) [thinGram,sign] at *

/-- Three identical thin tensor factors at each foot, as in Example 8B.2. -/
def packets (negative : Bool) (i : Fin 3) : Word 4 3 → ℂ :=
  pureWord (fun _ : Fin 3 => thin negative i)

theorem packets_symmetric (negative : Bool) (i : Fin 3) : Symmetric (packets negative i) := by
  rw [Bend.Symmetric,Bridges.symClasp_action]
  funext w
  have invariant (p : Equiv.Perm (Fin 3)) : packets negative i (w ∘ p.symm) = packets negative i w :=
    pure_reindex (fun _ => thin negative i) p w
  simp only [clasp,sumSlots,invariant,Finset.sum_const,
    Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  norm_num [Nat.factorial] <;> ring

theorem packet_entry (negative : Bool) (i j : Fin 3) :
    bracket (packets negative i) (packets negative j) = (thinGram negative i j)^3 := by
  have h := congrFun (congrFun (thin_gram negative) i) j
  change bracket (thin negative i) (thin negative j) = _ at h
  simp only [packets,bracket_pureWord,h,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem packet_units (negative : Bool) (i : Fin 3) : energy (packets negative i) = 1 := by
  have h := packet_entry negative i i
  rw [Coarse.bracket_self] at h
  fin_cases i <;> simpa [thinGram] using congrArg Complex.re h

/-- Every pair square agrees in the two examples. The directed triangle
retains the sign and has value ±1/512. -/
theorem triangle_sign (negative : Bool) :
    let F := packets negative 0
    let G := packets negative 1
    let H := packets negative 2
    Complex.normSq (bracket G F) = 1/64 ∧
    Complex.normSq (bracket G H) = 1/64 ∧
    Complex.normSq (bracket H F) = 1/64 ∧
    bracket G F = sign negative/8 ∧ bracket G H * bracket H F = 1/64 ∧
    star (bracket G F) * (bracket G H * bracket H F) = sign negative/512 := by
  dsimp only
  simp only [packet_entry]
  cases negative <;> norm_num (config := { decide := true }) [thinGram,sign,Complex.normSq_apply,Complex.star_def]

end
end BlockPermanents.FiveTriangleExample
