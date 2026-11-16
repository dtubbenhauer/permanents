import BlockPermanents.FourProperOrder
import BlockPermanents.FourMergedHalf

/-! In the second proper-cut family of Definition 5C.1, the first ordinary
packet passes through. The other two ordinary packets form the active cable. -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourExchangeKernel ThreeGeneralOpen
open scoped Matrix BigOperators
noncomputable section
variable {d k : ℕ} {I J : Type*}

open private turnWords from BlockPermanents.FourProperOrder in
/-- Reorder ordinary words as 2,3,1. In these coordinates the first two
words form the merged cable, in the same order as in the drawing. -/
private def mergedTurn (d k : ℕ) : Equiv.Perm (Triple d k) := (turnWords d k).symm

open private turnWords turn_fixed from BlockPermanents.FourProperOrder in
private theorem mergedTurn_fixed (x y : Triple d k) :
    ordinaryFoot d k (mergedTurn d k x) y = ordinaryFoot d k x y := by
  simpa only [mergedTurn, Equiv.apply_symm_apply] using
    (turn_fixed ((turnWords d k).symm x) y).symm

/-- Select the drawing's spectator and read the ordinary 2k-word before the
symmetric fork in the word cap. -/
def drawnMergedSlice (s : Word d ((3-2)*k)) : Matrix (Word d (2*k)) (Triple d k) ℂ :=
  fun w x => slice 2 (by decide) s w (mergedTurn d k x)

/-- The spectator is packet 1. Positions of the merged word index packets
2 and 3, in order, by their packet and slot quotients. -/
theorem drawnMergedSlice_apply (s : Word d ((3-2)*k)) (w : Word d (2*k)) (x : Triple d k) :
    drawnMergedSlice s w x =
      if (fun i : Fin ((3-2)*k) => x 0 i.modNat) = s ∧
        w = (fun i : Fin (2*k) => x (Fin.succ i.divNat) i.modNat) then 1 else 0 := by
  have hi : idle 2 (mergedTurn d k x) = (fun i : Fin ((3-2)*k) => x 0 i.modNat) := by
    funext i
    change mergedTurn d k x ⟨2+i.divNat.val, _⟩ i.modNat = _
    have e : (⟨2+i.divNat.val, by have h := i.divNat.isLt; omega⟩ : Fin 3) = 2 :=
      Fin.ext (by have h := i.divNat.isLt; change 2+i.divNat.val = 2; omega)
    rw [e]
    rfl
  have ha : active 2 (by decide) (mergedTurn d k x) =
      (fun i : Fin (2*k) => x (Fin.succ i.divNat) i.modNat) := by
    funext i
    have h (j : Fin 2) : mergedTurn d k x (j.castLE (by decide)) = x j.succ := by
      fin_cases j <;> rfl
    exact congrFun (h i.divNat) i.modNat
  simp only [drawnMergedSlice, slice, hi, ha]

/-- The middle diagram Wᵣ on rectangular feet. Its row contains the spectator
word and the ordinary and dual through words after the r-fold contraction. -/
def drawnMergedHalf (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (2*k) k) :
    Matrix (Word d ((3-2)*k) × (Word d (2*k-r) × Word d (k-r))) (I×J) ℂ :=
  fun row col => routed (fun s => drawnMergedSlice s * (ordinaryFoot d k * M)) N r row.1 row.2 col

theorem drawn_merged_eq (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (2*k) k) :
    drawnMergedHalf M N r = mergedProperHalf 2 (by decide) (ordinaryFoot d k * M) N r := by
  have h (s : Word d ((3-2)*k)) : drawnMergedSlice s * ordinaryFoot d k =
      slice 2 (by decide) s * ordinaryFoot d k := by
    ext w i
    change (∑ x, slice 2 (by decide) s w (mergedTurn d k x) * ordinaryFoot d k x i) =
      ∑ x, slice 2 (by decide) s w x * ordinaryFoot d k x i
    calc
      _ = ∑ x, slice 2 (by decide) s w (mergedTurn d k x) *
          ordinaryFoot d k (mergedTurn d k x) i := by simp only [mergedTurn_fixed]
      _ = _ := Equiv.sum_comp (mergedTurn d k) (fun x => slice 2 (by decide) s w x * ordinaryFoot d k x i)
  have hr (s : Word d ((3-2)*k)) : drawnMergedSlice s * (ordinaryFoot d k * M) =
      slice 2 (by decide) s * (ordinaryFoot d k * M) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  funext row col
  simp only [drawnMergedHalf, mergedProperHalf, hr]

end
end BlockPermanents.FourNative
