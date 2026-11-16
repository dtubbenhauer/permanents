import BlockPermanents.TransferBlocks
import BlockPermanents.MatchingThreshold
import Mathlib.Tactic.Module

/-! # The four-packet transfer on the same thin slots as the matrix permanent -/
namespace BlockPermanents.FourTarget
open Closures TransferBlocks
open scoped BigOperators
noncomputable section

abbrev Slot (k : ℕ) := Fin 4 × Fin k
abbrev Wire (k : ℕ) := Equiv.Perm (Slot k)
abbrev Op (d k : ℕ) := Module.End ℂ ((Slot k → Fin d) → ℂ)

def wires (k : ℕ) : FourPerm →* Wire k where
  toFun σ := σ.prodCongr (Equiv.refl (Fin k))
  map_one' := rfl
  map_mul' _ _ := rfl

def act (d k : ℕ) : Wire k →* Op d k := Transfer.tensorAction _ _
def packets (d k : ℕ) : FourPerm →* Op d k := (act d k).comp (wires k)

/-- All permutations of the thin slots in the first n packets, with every
spectator thin slot fixed individually. -/
def group (k n : ℕ) : Subgroup (Wire k) where
  carrier := {p | ∀ i, n ≤ i.1.val → p i = i}
  one_mem' _ _ := rfl
  mul_mem' ha hb i hi := by rw [Equiv.Perm.mul_apply, hb i hi, ha i hi]
  inv_mem' {a} ha i hi := a.injective (by rw [Equiv.Perm.apply_inv_self, ha i hi])

local instance (k n : ℕ) : Fintype (group k n) := Fintype.ofFinite _

def localClasp (d k n : ℕ) : Op d k := Transfer.clasp ((act d k).comp (group k n).subtype)
def fineClasp (d k : ℕ) : Op d k := Transfer.clasp (act d k)
def packetClaspOp (d k : ℕ) : Op d k := Transfer.clasp (packets d k)

def X₄ (d k : ℕ) : Op d k := (((4*k).factorial : ℚ) / k.factorial^4) • fineClasp d k -
  (24:ℚ) • packetClaspOp d k

def X₃ (d k : ℕ) : Op d k := (((3*k).factorial : ℚ) / k.factorial^3) • localClasp d k 3 -
  (6:ℚ) • triple (packets d k swap12) (packets d k swap23)

def Q (d k : ℕ) : Op d k :=
  fourOperator ((k+k).choose k) (packets d k swap12) (packets d k swap23)
    (packets d k swap34) (packets d k swap14) (localClasp d k 2) (X₃ d k) (X₄ d k)

theorem local_absorption (d k n : ℕ) (p : FourPerm) (h : wires k p ∈ group k n) :
    packets d k p * localClasp d k n = localClasp d k n ∧
    localClasp d k n * packets d k p = localClasp d k n :=
  ⟨Transfer.absorb_left ((act d k).comp (group k n).subtype) ⟨wires k p,h⟩,
    Transfer.absorb_right ((act d k).comp (group k n).subtype) ⟨wires k p,h⟩⟩

theorem first_two (k : ℕ) (n : ℕ) (hn : 2 ≤ n) : wires k swap12 ∈ group k n := by
  rintro ⟨i,t⟩ hi
  change n ≤ i.val at hi
  change (Equiv.swap 0 1 i,t) = (i,t)
  rw [Equiv.swap_apply_of_ne_of_ne (by intro h; subst i; norm_num at hi; omega) (by intro h; subst i; norm_num at hi; omega)]

theorem next_two (k : ℕ) : wires k swap23 ∈ group k 3 := by
  rintro ⟨i,t⟩ hi
  change 3 ≤ i.val at hi
  change (Equiv.swap 1 2 i,t) = (i,t)
  rw [Equiv.swap_apply_of_ne_of_ne (by intro h; subst i; norm_num at hi) (by intro h; subst i; norm_num at hi)]

private theorem fixed_average {d k} (B : Op d k)
    (h : ∀ p, packets d k p * B * packets d k p⁻¹ = B) :
    Transfer.bracket (packets d k) B = B := by
  change (Fintype.card FourPerm : ℚ)⁻¹ • ∑ p : FourPerm, _ = B
  simp only [h,Finset.sum_const,Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) B

theorem four_average_actual (d k : ℕ) : Transfer.bracket (packets d k) (Q d k) = X₄ d k := by
  let u := packets d k swap12
  let v := packets d k swap23
  let E := localClasp d k 3
  have hu : u*u=1 := by rw [show u*u = packets d k (swap12*swap12) from (map_mul ..).symm,
    show swap12*swap12=1 by decide,map_one]
  have hv : v*v=1 := by rw [show v*v = packets d k (swap23*swap23) from (map_mul ..).symm,
    show swap23*swap23=1 by decide,map_one]
  have hbr : u*v*u=v*u*v := by
    dsimp only [u,v]; simp only [← map_mul]; congr 1; decide
  obtain ⟨uP,Pu⟩ := local_absorption d k 2 _ (first_two k 2 le_rfl)
  obtain ⟨uE,Eu⟩ := local_absorption d k 3 _ (first_two k 3 (by decide))
  obtain ⟨vE,Ev⟩ := local_absorption d k 3 _ (next_two k)
  have absorbed : triple u v * E = E ∧ E * triple u v = E := by
    dsimp only [u,v,E]
    constructor
    · simp only [triple,smul_mul_assoc,add_mul,mul_assoc,one_mul,uE,vE]; module
    · simp only [triple,mul_smul_comm,mul_add,← mul_assoc,mul_one,Eu,Ev]; module
  have hsq := triple_idem u v hu hv hbr
  apply four_average
  · simp only [pair,smul_mul_assoc,add_mul,one_mul,uP]; module
  · simp only [pair,mul_smul_comm,mul_add,mul_one,Pu]; module
  · change triple u v * (_ • E - _ • triple u v) = _
    rw [mul_sub,mul_smul_comm,mul_smul_comm,absorbed.1,hsq]; rfl
  · change (_ • E - _ • triple u v) * triple u v = _
    rw [sub_mul,smul_mul_assoc,smul_mul_assoc,absorbed.2,hsq]; rfl
  · apply fixed_average
    intro p
    have fineL := Transfer.absorb_left (act d k) (wires k p)
    have fineR := Transfer.absorb_right (act d k) (wires k p⁻¹)
    change packets d k p * fineClasp d k = fineClasp d k at fineL
    change fineClasp d k * packets d k p⁻¹ = fineClasp d k at fineR
    simp only [X₄,mul_sub,mul_smul_comm,sub_mul,smul_mul_assoc,fineL,fineR,
      packetClaspOp,Transfer.absorb_left,Transfer.absorb_right]

private theorem eval_average {I M D : Type*} [Fintype I] [Group M] [Fintype M] [Fintype D]
    (ρ : M →* Equiv.Perm I) (v : (I → D) → ℂ) (w : I → D) :
    Transfer.clasp ((Transfer.tensorAction I D).comp ρ) v w =
      (Fintype.card M : ℂ)⁻¹ * ∑ σ : M, v (w ∘ ρ σ) := by
  classical
  simp [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Finset.sum_apply,
    Transfer.tensorAction, Rat.smul_def]

theorem fine_clasp_action (d k : ℕ) (z : (Slot k → Fin d) → ℂ) :
    fineClasp d k z = clasp z := by
  funext w
  have h := eval_average (MonoidHom.id (Wire k)) z w
  change fineClasp d k z w = _ at h
  rw [h]
  simp only [Fintype.card_perm,MonoidHom.id_apply,clasp,sumSlots]
  congr 1
  exact (Equiv.sum_comp (Equiv.inv (Wire k)) (fun (p : Wire k) => z (w ∘ p))).symm

theorem packet_clasp_action (d k : ℕ) (z : (Slot k → Fin d) → ℂ) :
    packetClaspOp d k z = packetClasp z := by
  funext w
  have h := eval_average (wires k) z w
  change packetClaspOp d k z w = _ at h
  rw [h]
  simp only [packetClasp,clasp,sumSlots,Fintype.card_perm]
  congr 1
  exact (Equiv.sum_comp (Equiv.inv FourPerm) (fun p => z (w ∘ wires k p))).symm

theorem target_action (d k : ℕ) (z : (Slot k → Fin d) → ℂ) : X₄ d k z = defect z := by
  funext w
  simp [X₄,LinearMap.smul_apply,LinearMap.sub_apply,Pi.sub_apply,Rat.smul_def,
    fine_clasp_action,packet_clasp_action,defect,fineWeight,Nat.factorial]

private theorem move_boundary {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] (p : Equiv.Perm I)
    (z y : (I → D) → ℂ) :
    bracket z (fun w => y (w ∘ p)) = bracket (fun w => z (w ∘ p.symm)) y := by
  let e := p.symm.arrowCongr (Equiv.refl D)
  simpa [e,bracket,Function.comp_def] using
    e.sum_comp (fun w => (starRingEnd ℂ) (z (w ∘ p.symm)) * y w)

private theorem eval_conjugate (d k : ℕ) (σ : FourPerm) (B : Op d k)
    (z : (Slot k → Fin d) → ℂ) :
    bracket z ((packets d k σ * B * packets d k σ⁻¹) z) =
    bracket (packets d k σ⁻¹ z) (B (packets d k σ⁻¹ z)) :=
  move_boundary (wires k σ) _ _

private theorem scaled_bracket_sum {I M : Type*} [Fintype I] [Fintype M]
    (z : I → ℂ) (v : M → I → ℂ) :
    bracket z (((24:ℚ)⁻¹) • ∑ i, v i) = (24:ℂ)⁻¹ * ∑ i, bracket z (v i) := by
  simp only [bracket,Pi.smul_apply,Rat.smul_def,smul_eq_mul,Finset.sum_apply,
    Finset.mul_sum,← mul_assoc]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem average_evaluation {d k} (B : Op d k) (z : (Slot k → Fin d) → ℂ) :
    (∑ σ : FourPerm, bracket (packets d k σ⁻¹ z) (B (packets d k σ⁻¹ z))) =
    24 * bracket z ((Transfer.bracket (packets d k) B) z) := by
  have cc : Fintype.card FourPerm = 24 := by simp [FourPerm,Fintype.card_perm,Nat.factorial]
  simp only [Transfer.bracket,LinearMap.coe_mk,AddHom.coe_mk,cc,Nat.cast_ofNat,
    LinearMap.smul_apply,LinearMap.sum_apply,scaled_bracket_sum,← mul_assoc]
  rw [show (24:ℂ)*24⁻¹ = 1 by norm_num,one_mul]
  exact Finset.sum_congr rfl (fun σ _ => (eval_conjugate d k σ B z).symm)

/-- The marked operator evaluated on every relabeling gives the permanent
difference on precisely the same packet inputs, after averaging. -/
theorem averaged_gap {d k : ℕ} (x : Fin 4 → Fin k → Fin d → ℂ) :
    let z := flatPackets x
    (∑ σ : FourPerm, bracket (packets d k σ⁻¹ z) (Q d k (packets d k σ⁻¹ z))) =
    24 * ((crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
      (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent) := by
  dsimp only
  rw [average_evaluation,four_average_actual,target_action,defect_closure]
  have hg : (fun i j => (crossGram (x i) (x j)).permanent) = crossGram (fun i => packet (x i))
      (fun i => packet (x i)) := by funext i j; exact (packet_gram _ _).symm
  rw [hg]

end
end BlockPermanents.FourTarget
