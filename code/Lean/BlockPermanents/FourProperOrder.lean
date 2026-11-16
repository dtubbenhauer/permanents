import BlockPermanents.FourProperBoundary
import BlockPermanents.FourProperHalf

/-! The rightmost active packet in the drawing of Definition 5C.1. -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourExchangeKernel FourWireAlgebra TransferBlocks FourTarget ThreeTransfer ThreeGeneralOpen
open scoped Matrix BigOperators
noncomputable section
variable {d k : ℕ} {I J : Type*}

/-- Reorder the three ordinary inputs as 3,1,2, so the leftmost cut
in these coordinates cuts the rightmost cable in the displayed picture. -/
private def turn3 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

private def turnWords (d k : ℕ) : Equiv.Perm (Triple d k) :=
  turn3.symm.arrowCongr (Equiv.refl _)

private theorem turn_layout (x : Index d k) :
    layout d k ((layout d k).symm x ∘ wires k (swap23*swap12)) =
      (turnWords d k x.1, x.2) := by
  apply Prod.ext
  · funext t j; fin_cases t <;> rfl
  · rfl

private theorem turn_fixed (x y : Triple d k) :
    ordinaryFoot d k (turnWords d k x) y = ordinaryFoot d k x y := by
  let ρ := packets d k
  let F := ordinary ρ
  have u : ρ swap12 * ρ swap12 = 1 := by rw [←map_mul,show swap12*swap12=1 by decide,map_one]
  have v : ρ swap23 * ρ swap23 = 1 := by rw [←map_mul,show swap23*swap23=1 by decide,map_one]
  have braid : ρ swap12 * ρ swap23 * ρ swap12 = ρ swap23 * ρ swap12 * ρ swap23 := by
    simp only [←map_mul];congr 1;decide
  have vf : ρ swap23 * F = F := by
    change ρ swap23 * triple _ _ = triple _ _
    rw [triple_flip _ _ braid,triple_left _ _ v]
  have h : ρ (swap23*swap12) * F = F := by rw [map_mul,mul_assoc,triple_left _ _ u,vf]
  have H := congrArg (matrix d k) h
  rw [map_mul] at H
  change matrix d k (act d k (wires k (swap23*swap12))) * matrix d k (ordinary (packets d k)) =
    matrix d k (ordinary (packets d k)) at H
  rw [ordinaryFoot_spec] at H
  have entry := congrFun (congrFun H (x,x 0)) (y,x 0)
  simpa only [Matrix.mul_apply,matrix_perm_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,if_true,turn_layout,upright,ite_true] using entry

/-- At the diagram's rightmost placement, ordinary packet 3 is active, and
the remaining packets occur in the order 1,2. -/
def drawnSlice (s : Word d ((3-1)*k)) : Matrix (Word d (1*k)) (Triple d k) ℂ :=
  fun w x => slice 1 (by decide) s w (turnWords d k x)

/-- Explicit input labels in the drawing: spectators are 1,2 in order
and the ordinary active input is 3 (here the three indices are 0,1,2). -/
theorem drawnSlice_apply (s : Word d ((3-1)*k)) (w : Word d (1*k)) (x : Triple d k) :
    drawnSlice s w x =
      if (fun i : Fin ((3-1)*k) => x (i.divNat.castLE (by decide)) i.modNat) = s ∧
        w = (fun i => x 2 i.modNat) then 1 else 0 := by
  have hi : idle 1 (turnWords d k x) =
      (fun i : Fin ((3-1)*k) => x (i.divNat.castLE (by decide)) i.modNat) := by
    funext i
    change (turnWords d k x) ⟨1+i.divNat.val,_⟩ i.modNat =
      x (i.divNat.castLE (by decide)) i.modNat
    have f (j : Fin 2) : turnWords d k x ⟨1+j.val,by omega⟩ = x (j.castLE (by decide)) := by
      fin_cases j <;> rfl
    exact congrFun (f i.divNat) i.modNat
  have ha : active 1 (by decide) (turnWords d k x) =
      (fun i : Fin (1*k) => x 2 i.modNat) := by
    funext i
    change (turnWords d k x) (i.divNat.castLE (by decide)) i.modNat = _
    rw [Subsingleton.elim i.divNat (0 : Fin 1)]
    rfl
  simp only [drawnSlice,slice,hi,ha]

/-- The drawing's cap, with the ordinary packet average at its feet. -/
def drawnHalf (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) (r : CutIndex (1*k) k) :
    Matrix (Word d ((3-1)*k) × (Word d (1*k-r) × Word d (k-r))) (I×J) ℂ :=
  fun row col => routed (fun s => drawnSlice s * (ordinaryFoot d k * M)) N r row.1 row.2 col

theorem drawn_half_eq (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (1*k) k) :
    drawnHalf M N r = properHalf (ordinaryFoot d k * M) N r := by
  have h (s : Word d ((3-1)*k)) : drawnSlice s * ordinaryFoot d k =
      slice 1 (by decide) s * ordinaryFoot d k := by
    ext w i
    change (∑ x, slice 1 (by decide) s w (turnWords d k x) * ordinaryFoot d k x i) =
      ∑ x, slice 1 (by decide) s w x * ordinaryFoot d k x i
    calc
      _ = ∑ x, slice 1 (by decide) s w (turnWords d k x) * ordinaryFoot d k (turnWords d k x) i := by simp only [turn_fixed]
      _ = _ := Equiv.sum_comp (turnWords d k) (fun x => slice 1 (by decide) s w x * ordinaryFoot d k x i)
  have hr (s : Word d ((3-1)*k)) : drawnSlice s * (ordinaryFoot d k * M) =
      slice 1 (by decide) s * (ordinaryFoot d k * M) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  funext row col
  simp only [drawnHalf, properHalf,hr]

end
end BlockPermanents.FourNative
