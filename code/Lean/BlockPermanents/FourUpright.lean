import BlockPermanents.FourWireCutDefs
import BlockPermanents.FourActualAlgebra
import BlockPermanents.ThreeWire

/-! # Upright ordinary and fine clasps of the three routes on a common boundary -/
namespace BlockPermanents.FourUpright
open FourTarget FourWireCut FourCapOrbit FourCapValues FourRoutes FourWireAlgebra TransferBlocks
open LocalAction LocalGroup Equiv
open scoped BigOperators
noncomputable section

def last : Pos ⊕ Fin 2 ≃ Slot 2 where
  toFun := Sum.elim (fun i => (i.1.castSucc,i.2)) (fun j => (3,j))
  invFun i := if h : i.1.val < 3 then .inl (⟨i.1.val,h⟩,i.2) else .inr i.2
  left_inv i := by
    rcases i with ⟨a,b⟩|b
    · simp [a.isLt]
    · rfl
  right_inv i := by rcases i with ⟨a,b⟩; fin_cases a <;> rfl

def ordinaryLayout (r : Fin 3) : A r ⊕ U r ≃ Pos :=
  (Equiv.sumComm _ _).trans (sections r).symm

def allLayout (r : Fin 3) : A r ⊕ (U r ⊕ Fin 2) ≃ Slot 2 :=
  (Equiv.sumAssoc _ _ _).symm.trans (((ordinaryLayout r).sumCongr (Equiv.refl _)).trans last)

private theorem twist_eq (r : Fin 3) (p : Perm (A r)) :
    liftPerm (ordinaryLayout r) p = (order r p).trans (order r 1).symm := by
  apply Equiv.ext
  intro w
  obtain ⟨v,rfl⟩ := (sections r).symm.surjective w
  cases v <;> simp [liftPerm,ordinaryLayout,order,Equiv.permCongr_def]

private theorem pull {d} (r : Fin 3) (p : Perm (A r)) (u : (Pos → Fin d) → ℂ)
    (H : Bend.Word d 2 → ℂ) :
    act d 2 (liftPerm (allLayout r) p) (product u H) =
    product (Transfer.tensorAction Pos (Fin d) (liftPerm (ordinaryLayout r) p) u) H := by
  funext w
  change u (fun i => w ((liftPerm (allLayout r) p) (last (.inl i)))) *
      H (fun j => w ((liftPerm (allLayout r) p) (last (.inr j)))) =
    u (fun i => w (last (.inl ((liftPerm (ordinaryLayout r) p) i)))) * H (fun j => w (last (.inr j)))
  congr 1
  · apply congrArg u; funext i
    obtain ⟨i,rfl⟩ := (ordinaryLayout r).surjective i
    cases i <;> simp [allLayout,liftPerm,Equiv.permCongr_def]

def suffix (d : ℕ) (r : Fin 3) : Op d 2 :=
  projector (Fin d) (fun i : Slot 2 => 2-r.val ≤ i.1.val ∧ i.1.val<3)

private theorem suffix_eq (d : ℕ) (r : Fin 3) :
    extend (allLayout r) (Transfer.clasp (Transfer.tensorAction (A r) (Fin d))) = suffix d r := by
  apply projector_extend
  · fin_cases r <;> decide
  · fin_cases r <;> decide

theorem suffix_product {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Bend.Word d 2 → ℂ) :
    suffix d r (product (feet F) H) = product (merged r F) H := by
  rw [← suffix_eq,extend_clasp]
  funext w
  simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply,
    Rat.smul_def,smul_eq_mul,Finset.sum_apply,Fintype.card_perm,MonoidHom.comp_apply,Rat.cast_inv,Rat.cast_natCast]
  change ((↑(Fintype.card (A r)).factorial : ℂ)⁻¹) * (∑ p : Perm (A r),
    (act d 2 (liftPerm (allLayout r) p) (product (feet F) H)) w) = _
  simp only [pull,product,merged,Transfer.tensorAction,MonoidHom.coe_mk,OneHom.coe_mk,
    LinearMap.coe_mk,AddHom.coe_mk,twist_eq,← Finset.sum_mul]
  simp [A,mul_assoc]

def ori : FourPerm := Equiv.swap 0 2
def frontPair (d : ℕ) := localClasp d 2 2

theorem reversed_pair (d : ℕ) : packets d 2 ori * frontPair d * packets d 2 ori = suffix d 1 := by
  rw [frontPair,FourLocalSlots.local_is_projector]
  have h := conjugate (D := Fin d) (wires 2 ori) (fun i : Slot 2 => i.1.val<2)
    (fun i : Slot 2 => 2 - (1 : Fin 3).val ≤ i.1.val ∧ i.1.val<3) (by decide)
  have hi : (wires 2 ori)⁻¹ = wires 2 ori := by decide
  rw [hi] at h
  exact h

theorem entire (d : ℕ) : localClasp d 2 3 = suffix d 2 := by
  rw [FourLocalSlots.local_is_projector,suffix]
  congr 1; funext i; exact propext (by simp)

end
end BlockPermanents.FourUpright
