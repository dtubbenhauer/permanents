import BlockPermanents.FourLocalSlots
import BlockPermanents.FourLocalCompression
import BlockPermanents.FourWireAlgebra

/-! The three Schur openings in the packet-symmetric image of the four-packet operator. -/
namespace BlockPermanents.FourOpenings
open FourTarget FourLocalSlots FourLocalCompression FourWireAlgebra
open LocalGroup TransferBlocks SchurNormalization Bend
open scoped BigOperators
noncomputable section

local instance (P : Slot 2 → Prop) : Fintype (fixedOutside P) := Fintype.ofFinite _
local instance (n : ℕ) : Fintype (group 2 n) := Fintype.ofFinite _

private theorem marked_absorbed (d : ℕ) : marked d * W d = W d ∧ W d * marked d = W d := by
  have h (p : fixedOutside (fun j : Slot 2 => j.1=3)) :=
    single_wire_absorbed d p 3 (fun a ha => p.prop a ha)
  exact ⟨avg_mul_fixed _ _ fun p => (h p).1,mul_avg_fixed _ _ fun p => (h p).2⟩

private theorem marked_comm (d n : ℕ) (hn : n ≤ 3) :
    marked d * localClasp d 2 n = localClasp d 2 n * marked d := by
  apply mul_avg_comm
  intro p
  symm
  apply commute_from_conj (act d 2) p (marked d)
  apply LocalGroup.conjugate
  intro a
  have fixed (a : Slot 2) (h : a.1=3) : (p:Wire 2) a=a := p.prop a (by rw [h]; exact hn)
  constructor
  · intro ha; rw [fixed a ha,ha]
  · intro ha
    obtain he := p.val.injective (fixed (p.val a) ha)
    rwa [he] at ha

private theorem compressed_block (d n : ℕ) (hn : n ≤ 3) (u : Op d 2) :
    sand (W d) (block d n*u*block d n) =
      sand (W d) (localClasp d 2 n*u*localClasp d 2 n) := by
  have hL : W d*block d n = W d*localClasp d 2 n := by
    rw [block,← marked_comm d n hn,← mul_assoc,(marked_absorbed d).2]
  have hR : block d n*W d = localClasp d 2 n*W d := by
    rw [block,mul_assoc,(marked_absorbed d).1]
  change W d*(block d n*u*block d n)*W d = _
  calc
    _=(W d*block d n)*u*(block d n*W d) := by simp only [mul_assoc]
    _=_ := by rw [hL,hR]; change _=W d*(_*_*_)*W d; simp only [mul_assoc]

private theorem joint_three (d : ℕ) : joint d 3 = fineClasp d 2 := by
  let P := fun j : Slot 2 => j.1.val < 3 ∨ j.1=3
  have hall (i : Slot 2) : P i := by
    change i.1.val<3 ∨ i.1=3
    by_cases h : i.1.val<3
    · exact Or.inl h
    · exact Or.inr (Fin.ext (by have hh:=i.1.isLt; omega))
  let e : fixedOutside P ≃ Wire 2 := {
    toFun := Subtype.val
    invFun := fun p => ⟨p,fun i hi => (hi (hall i)).elim⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  change Transfer.clasp ((act d 2).comp (fixedOutside P).subtype) = Transfer.clasp (act d 2)
  simp only [Transfer.clasp,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

private theorem joint_two (d : ℕ) :
    sand (packets d 2 swap34) (localClasp d 2 3) = joint d 2 := by
  rw [local_is_projector]
  change act d 2 (wires 2 swap34) * _ * act d 2 (wires 2 swap34) = _
  have he : (wires 2 swap34)⁻¹ = wires 2 swap34 := by
    ext i : 1; revert i; decide
  rw [← he]
  nth_rw 1 [he]
  apply LocalGroup.conjugate
  decide

private theorem joint_one (d : ℕ) :
    sand (packets d 2 swap34) (movedPair (packets d 2) (localClasp d 2 2)) =
      sand (packets d 2 swap12) (joint d 1) := by
  let P := fun j : Slot 2 => j.1=1 ∨ j.1=2
  let Q := fun j : Slot 2 => j.1=1 ∨ j.1=3
  have conj (τ : FourPerm) (P Q : Slot 2 → Prop) (hτ : τ⁻¹=τ)
      (hh : ∀ j, P j ↔ Q (wires 2 τ j)) :
      sand (packets d 2 τ) (projector (Fin d) P) = projector (Fin d) Q := by
    have he : (wires 2 τ)⁻¹ = wires 2 τ := by rw [← map_inv,hτ]
    simpa only [he] using (LocalGroup.conjugate (D:=Fin d) (wires 2 τ) P Q hh)
  have a := conj (Equiv.swap 0 2) (fun j : Slot 2 => j.1.val<2) P (by decide) (by decide)
  have b := conj swap34 P Q (by decide) (by decide)
  have c := conj swap12 (fun j : Slot 2 => j.1.val<1 ∨ j.1=3) Q (by decide) (by decide)
  rw [local_is_projector]
  change sand _ (sand _ _) = _
  rw [a,b]
  exact c.symm

private theorem comm_sand {R : Type*} [Ring R] [Algebra ℚ R] (w f a : R) (h : w*f=f*w) :
    sand w (sand f a) = sand f (sand w a) := by
  change w*(f*a*f)*w=f*(w*a*w)*f
  calc
    _=(w*f)*a*(f*w) := by simp only [mul_assoc]
    _=(f*w)*a*(w*f) := congrArg₂ (fun l r => l*a*r) h h.symm
    _=_ := by simp only [mul_assoc]

private theorem chosen_exchange {n : ℕ} (hn : n ≤ 3) (hn0 : 0<n) :
    let c := Equiv.swap (0:Fin 4) ⟨n-1,by omega⟩
    (FourLocalSlots.exchange n hn ⟨0,by omega⟩ = 1) ∧
    (FourLocalSlots.exchange n hn ⟨1, by omega⟩ = wires 2 c * eWire * wires 2 c) ∧
    (FourLocalSlots.exchange n hn ⟨2, by omega⟩ = wires 2 c * tWire * wires 2 c) := by
  interval_cases n <;> decide +revert

private theorem cut_sum {R : Type*} [AddCommMonoid R] {m : ℕ} (h : 2≤m)
    (f : CutIndex m 2 → R) :
    (∑ r,f r) = f ⟨0,by omega⟩ + f ⟨1,by omega⟩ + f ⟨2,by omega⟩ := by
  have he : 3=min m 2+1 := by omega
  rw [← (finCongr he).sum_comp f, Fin.sum_univ_three]
  rfl

private theorem local_schur (d n : ℕ) (hn : n ≤ 3) (hn0 : 0<n)
    (h : HomogeneousSchur d (n*2) 2) :
    let C := sand (W d)
    let P := localClasp d 2 n
    let e := act d 2 eWire
    let t := packets d 2 swap14
    C (((n*2+2).choose (n*2) : ℚ) • joint d n) =
      C (P + (weight (n*2) 2 1 : ℚ) • (P*e*P) + (weight (n*2) 2 2 : ℚ) • (P*t*P)) := by
  dsimp only
  let c := Equiv.swap (0:Fin 4) ⟨n-1,by omega⟩
  have hc : wires 2 c ∈ group 2 n := by
    rintro ⟨a,b⟩ ha
    change n≤a.val at ha
    change (c a,b)=(a,b)
    have ha0 : a ≠ 0 := fun he => by rw [he] at ha; change n≤0 at ha;omega
    have ha' : a ≠ ⟨n-1,by omega⟩ := fun he => by rw [he] at ha;change n≤n-1 at ha;omega
    rw [show c a = a from Equiv.swap_apply_of_ne_of_ne ha0 ha']
  let P := localClasp d 2 n
  have hL : act d 2 (wires 2 c) * P = P :=
    Transfer.absorb_left ((act d 2).comp (group 2 n).subtype) ⟨_,hc⟩
  have hR : P * act d 2 (wires 2 c) = P :=
    Transfer.absorb_right ((act d 2).comp (group 2 n).subtype) ⟨_,hc⟩
  have hconj (v : Wire 2) :
      P*act d 2 (wires 2 c * v * wires 2 c)*P=P*act d 2 v*P := by
    rw [map_mul,map_mul]
    exact absorb_conjugate _ _ _ _ hR hL rfl
  obtain ⟨eq₀,eq₁,eq₂⟩ := chosen_exchange hn hn0
  have eqn := congrArg (sand (W d)) (schur_on_slots d n hn h)
  rw [map_sum,cut_sum (by omega : 2≤n*2)] at eqn
  simp only [map_smul,compressed_block _ _ hn,eq₀,eq₁,eq₂,map_one,mul_one,
    show weight (n*2) 2 0 = 1 by simp [weight], Nat.cast_one,one_smul] at eqn
  have pp : P*P=P := Transfer.clasp_sq _
  have a := hconj eWire
  have b := hconj tWire
  change P*act d 2 (wires 2 c*eWire*wires 2 c)*P = _ at a
  change P*act d 2 (wires 2 c*tWire*wires 2 c)*P = P*packets d 2 swap14*P at b
  have sq := compressed_block d n hn (1:Op d 2)
  simp only [mul_one] at sq
  simp only [map_add,map_smul]
  simpa only [P,c,sq,pp,a,b] using eqn

private theorem surround {d} (F := ordinary (packets d 2)) {a b : Op d 2}
    (h : sand (W d) a = sand (W d) b) (hF : W d*F = F*W d) :
    sand (W d) (sand F a) = sand (W d) (sand F b) := by
  rw [comm_sand _ _ _ hF,comm_sand _ _ _ hF,h]

private theorem first_compress (d : ℕ) (a : Op d 2) :
    sand (W d) (localClasp d 2 1*a*localClasp d 2 1) = sand (W d) a := by
  let w := W d
  let p := localClasp d 2 1
  obtain ⟨pw,wp⟩ := first_packet_absorbed d
  change w*(p*a*p)*w = w*a*w
  calc
    _=(w*p)*a*(p*w) := by simp only [mul_assoc]
    _=_ := by rw [show w*p=w from wp,show p*w=w from pw]

private theorem compressed_identity (d : ℕ) :
    sand (W d) (localClasp d 2 1) = sand (W d) 1 := by
  change W d*_*W d=W d*1*W d
  rw [(first_packet_absorbed d).2,mul_one]

set_option maxHeartbeats 1200000 in
theorem openings_three (d : ℕ) (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2)
    (h₆ : HomogeneousSchur d 6 2) :
    Openings (sand (W d)) (packets d 2) (localClasp d 2 2) (localClasp d 2 3)
      (fineClasp d 2) (act d 2 eWire) := by
  let ρ := packets d 2
  let F := ordinary ρ
  let C := sand (W d)
  let e := act d 2 eWire
  let t := ρ swap14
  let P := localClasp d 2 2
  let E := localClasp d 2 3
  have wF : W d*F=F*W d := W_comm_triple d
  have uu : ρ swap12*ρ swap12=1 := by rw [← map_mul,show swap12*swap12=1 by decide,map_one]
  have vv : ρ swap23*ρ swap23=1 := by rw [← map_mul,show swap23*swap23=1 by decide,map_one]
  have braid : ρ swap12*ρ swap23*ρ swap12 = ρ swap23*ρ swap12*ρ swap23 := by
    simp only [← map_mul]; congr 1; decide
  have ff : F*F=F := triple_idem _ _ uu vv braid
  have fu := triple_right (ρ swap12) (ρ swap23) uu
  have uf := triple_left (ρ swap12) (ρ swap23) uu
  have fl (a : Op d 2) : sand F (sand (ρ swap12) a) = sand F a :=
    absorb_conjugate _ _ _ _ fu uf rfl
  have s₃ := local_schur d 3 (by decide) (by decide) h₆
  have s₂ := surround (F:=F) (local_schur d 2 (by decide) (by decide) h₄) wF
  have s₁ := local_schur d 1 (by decide) (by decide) h₂
  change C ((28:ℚ) • joint d 3)=C (E+(12:ℚ) • (E*e*E)+(15:ℚ) • (E*t*E)) at s₃
  change C (sand F ((15:ℚ) • joint d 2))=C (sand F (P+(8:ℚ) • (P*e*P)+(6:ℚ) • (P*t*P))) at s₂
  change sand (W d) ((6:ℚ) • joint d 1)=sand (W d) (localClasp d 2 1+
    (4:ℚ) • (localClasp d 2 1*e*localClasp d 2 1)+(1:ℚ) • (localClasp d 2 1*t*localClasp d 2 1)) at s₁
  simp only [one_smul,map_add,map_smul,first_compress,compressed_identity] at s₁
  have s₁' : C ((6:ℚ) • joint d 1)=C (1+(4:ℚ) • e+t) := by
    simpa only [map_add,map_smul] using s₁
  have s₁'' := surround (F:=F) s₁' wF
  have expand (u v : Op d 2) : sand F (u*v*u)=F*u*v*u*F := by
    change F*(u*v*u)*F=_
    simp only [mul_assoc]
  constructor
  · rw [joint_three] at s₃
    change C ((2520:ℚ) • fineClasp d 2) =
      C ((90:ℚ) • E+(1080:ℚ) • (E*e*E)+(1350:ℚ) • (E*t*E))
    have hh := congrArg (fun a => (90:ℚ) • a) s₃
    dsimp only at hh
    simp only [map_add,map_smul,smul_add,smul_smul] at hh ⊢
    norm_num at hh
    exact hh
  · rw [← joint_two] at s₂
    change C ((90:ℚ) • sand F (sand (ρ swap34) E)) =
      C ((6:ℚ) • sand F P + (48:ℚ) • (F*P*e*P*F)+(36:ℚ) • (F*P*t*P*F))
    have hh := congrArg (fun a => (6:ℚ) • a) s₂
    dsimp only at hh
    simp only [map_smul,map_add,smul_add,smul_smul,expand] at hh ⊢
    norm_num at hh
    exact hh
  · change C ((6:ℚ) • sand F (sand (packets d 2 swap34) (movedPair (packets d 2) (localClasp d 2 2)))) =
      C (F + (4:ℚ) • (F*e*F) + F*t*F)
    rw [joint_one,fl]
    have sf : sand F (1:Op d 2)=F := by change F*1*F=F;rw [mul_one,ff]
    simp only [map_smul,map_add,sf] at s₁'' ⊢
    exact s₁''

theorem openings (d : ℕ) (h : ∀ n, HomogeneousSchur d (n*2) 2) :
    Openings (sand (W d)) (packets d 2) (localClasp d 2 2) (localClasp d 2 3)
      (fineClasp d 2) (act d 2 eWire) :=
  openings_three d (h 1) (h 2) (h 3)

end
end BlockPermanents.FourOpenings
