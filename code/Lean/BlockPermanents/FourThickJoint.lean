import BlockPermanents.FourThickSlots
import BlockPermanents.FourThickCompression
import BlockPermanents.FourWireAlgebra

/-! # Repositioning the three local openings in the symmetric packet space -/
namespace BlockPermanents.FourThickJoint
open FourTarget FourThickSlots FourThickCompression FourWireAlgebra
open FourLocalCompression (avg_mul_fixed mul_avg_fixed mul_avg_comm commute_from_conj)
open LocalGroup TransferBlocks SchurNormalization Bend
open scoped BigOperators
noncomputable section
local instance (k : ℕ) (P : Slot k → Prop) : Fintype (fixedOutside P) := Fintype.ofFinite _
local instance (k n : ℕ) : Fintype (group k n) := Fintype.ofFinite _

theorem marked_absorbed (d k : ℕ) : marked d k * W d k = W d k ∧ W d k * marked d k = W d k := by
  have h (p : fixedOutside (fun j : Slot k => j.1=3)) :=
    single_wire_absorbed d k p 3 (fun a ha => p.prop a ha)
  exact ⟨avg_mul_fixed _ _ fun p => (h p).1,mul_avg_fixed _ _ fun p => (h p).2⟩

theorem marked_comm (d k n : ℕ) (hn : n ≤ 3) :
    marked d k * localClasp d k n = localClasp d k n * marked d k := by
  apply mul_avg_comm
  intro p
  symm
  apply commute_from_conj (act d k) p (marked d k)
  apply LocalGroup.conjugate
  intro a
  have fixed (a : Slot k) (h : a.1=3) : (p:Wire k) a=a := p.prop a (by rw [h]; exact hn)
  constructor
  · intro ha; rw [fixed a ha,ha]
  · intro ha
    obtain he := p.val.injective (fixed (p.val a) ha)
    rwa [he] at ha

theorem compressed_block (d k n : ℕ) (hn : n ≤ 3) (u : Op d k) :
    sand (W d k) (block d k n*u*block d k n) =
      sand (W d k) (localClasp d k n*u*localClasp d k n) := by
  have hL : W d k*block d k n = W d k*localClasp d k n := by
    rw [block,← marked_comm d k n hn,← mul_assoc,(marked_absorbed d k).2]
  have hR : block d k n*W d k = localClasp d k n*W d k := by
    rw [block,mul_assoc,(marked_absorbed d k).1]
  change W d k*(block d k n*u*block d k n)*W d k = _
  calc
    _=(W d k*block d k n)*u*(block d k n*W d k) := by simp only [mul_assoc]
    _=_ := by rw [hL,hR]; change _=W d k*(_*_*_)*W d k; simp only [mul_assoc]

theorem joint_three (d k : ℕ) : joint d k 3 = fineClasp d k := by
  let P := fun j : Slot k => j.1.val < 3 ∨ j.1=3
  have hall (i : Slot k) : P i := by
    change i.1.val<3 ∨ i.1=3
    by_cases h : i.1.val<3
    · exact Or.inl h
    · exact Or.inr (Fin.ext (by have hh:=i.1.isLt; omega))
  let e : fixedOutside P ≃ Wire k := {
    toFun := Subtype.val
    invFun := fun p => ⟨p,fun i hi => (hi (hall i)).elim⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  change Transfer.clasp ((act d k).comp (fixedOutside P).subtype) = Transfer.clasp (act d k)
  simp only [Transfer.clasp,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

theorem joint_two (d k : ℕ) :
    sand (packets d k swap34) (localClasp d k 3) = joint d k 2 := by
  rw [local_is_projector]
  change act d k (wires k swap34) * _ * act d k (wires k swap34) = _
  have he : (wires k swap34)⁻¹ = wires k swap34 := by
    rw [← map_inv,show swap34⁻¹ = swap34 by decide]
  rw [← he]
  nth_rw 1 [he]
  apply LocalGroup.conjugate
  rintro ⟨a,b⟩; exact (by decide : ∀ a : Fin 4, a.val<3 ↔ (swap34 a).val<2 ∨ swap34 a=3) a

theorem joint_one (d k : ℕ) :
    sand (packets d k swap34) (movedPair (packets d k) (localClasp d k 2)) =
      sand (packets d k swap12) (joint d k 1) := by
  let P := fun j : Slot k => j.1=1 ∨ j.1=2
  let Q := fun j : Slot k => j.1=1 ∨ j.1=3
  have conj (τ : FourPerm) (P Q : Slot k → Prop) (hτ : τ⁻¹=τ)
      (hh : ∀ j, P j ↔ Q (wires k τ j)) :
      sand (packets d k τ) (projector (Fin d) P) = projector (Fin d) Q := by
    have he : (wires k τ)⁻¹ = wires k τ := by rw [← map_inv,hτ]
    simpa only [he] using (LocalGroup.conjugate (D:=Fin d) (wires k τ) P Q hh)
  have a := conj (Equiv.swap 0 2) (fun j : Slot k => j.1.val<2) P (by decide) (by
    rintro ⟨a,b⟩; exact (by decide : ∀ a : Fin 4, a.val<2 ↔ Equiv.swap 0 2 a=1 ∨ Equiv.swap 0 2 a=2) a)
  have b := conj swap34 P Q (by decide) (by
    rintro ⟨a,b⟩; exact (by decide : ∀ a : Fin 4, (a=1 ∨ a=2) ↔ swap34 a=1 ∨ swap34 a=3) a)
  have c := conj swap12 (fun j : Slot k => j.1.val<1 ∨ j.1=3) Q (by decide) (by
    rintro ⟨a,b⟩; exact (by decide : ∀ a : Fin 4, (a.val<1 ∨ a=3) ↔ swap12 a=1 ∨ swap12 a=3) a)
  rw [local_is_projector]
  change sand _ (sand _ _) = _
  rw [a,b]
  exact c.symm

theorem comm_sand {R : Type*} [Ring R] [Algebra ℚ R] (w f a : R) (h : w*f=f*w) :
    sand w (sand f a) = sand f (sand w a) := by
  change w*(f*a*f)*w=f*(w*a*w)*f
  calc
    _=(w*f)*a*(f*w) := by simp only [mul_assoc]
    _=(f*w)*a*(w*f) := congrArg₂ (fun l r => l*a*r) h h.symm
    _=_ := by simp only [mul_assoc]

theorem surround {d k} (F := ordinary (packets d k)) {a b : Op d k}
    (h : sand (W d k) a = sand (W d k) b) (hF : W d k*F = F*W d k) :
    sand (W d k) (sand F a) = sand (W d k) (sand F b) := by
  rw [comm_sand _ _ _ hF,comm_sand _ _ _ hF,h]

theorem first_compress (d k : ℕ) (a : Op d k) :
    sand (W d k) (localClasp d k 1*a*localClasp d k 1) = sand (W d k) a := by
  let w := W d k
  let p := localClasp d k 1
  obtain ⟨pw,wp⟩ := first_packet_absorbed d k
  change w*(p*a*p)*w = w*a*w
  calc
    _=(w*p)*a*(p*w) := by simp only [mul_assoc]
    _=_ := by rw [show w*p=w from wp,show p*w=w from pw]

theorem compressed_identity (d k : ℕ) :
    sand (W d k) (localClasp d k 1) = sand (W d k) 1 := by
  change W d k*_*W d k=W d k*1*W d k
  rw [(first_packet_absorbed d k).2,mul_one]


end
end BlockPermanents.FourThickJoint
