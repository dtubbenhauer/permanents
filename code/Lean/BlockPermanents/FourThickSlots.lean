import BlockPermanents.LocalGroup
import BlockPermanents.WireSchur
/-! # The local Schur opening on the four packets of arbitrary thickness -/
namespace BlockPermanents.FourThickSlots
open FourTarget LocalGroup LocalAction WireSchur Bend SchurNormalization
open scoped BigOperators
noncomputable section

def joint (d k n : ℕ) := projector (Fin d) (fun j : Slot k => j.1.val < n ∨ j.1=3)
def marked (d k : ℕ) := projector (Fin d) (fun j : Slot k => j.1=3)
def block (d k n : ℕ) := localClasp d k n * marked d k

theorem local_is_projector (d k n : ℕ) :
    localClasp d k n = projector (Fin d) (fun j : Slot k => j.1.val < n) := by
  have he : group k n = fixedOutside (fun j : Slot k => j.1.val < n) := by
    ext σ
    simp only [group,fixedOutside,Subgroup.mem_mk,Set.mem_setOf_eq,not_lt]
  letI : Fintype (group k n) := Fintype.ofFinite _
  letI : Fintype (fixedOutside (fun j : Slot k => j.1.val < n)) := Fintype.ofFinite _
  exact avg_eq (MulEquiv.subgroupCongr he).toEquiv _ _ (fun x => rfl)

/-- First arrange whole packets with the marked packet after the active ordinary slots. -/
private def arrange (k n : ℕ) (hn : n ≤ 3) :
    ((Fin n × Fin k ⊕ Fin k) ⊕ Fin (3-n) × Fin k) ≃ Slot k where
  toFun
    | .inl (.inl (a,b)) => (⟨a.val,by omega⟩,b)
    | .inl (.inr b) => (3,b)
    | .inr (a,b) => (⟨n+a.val,by omega⟩,b)
  invFun j := if a : j.1.val < n then .inl (.inl (⟨j.1.val,a⟩,j.2))
    else if b : j.1=3 then .inl (.inr j.2) else .inr (⟨j.1.val-n,by
      have : j.1.val ≠ 3 := fun e => b (Fin.ext e)
      omega⟩,j.2)
  left_inv j := by
    rcases j with ((⟨a,b⟩ | b) | ⟨a,b⟩)
    · simp [a.isLt]
    · simp [show ¬(3:Fin 4).val<n by change ¬3<n;omega]
    · simp only [show ¬ n+a.val<n by omega,dif_neg,
        show (⟨n+a.val,by omega⟩:Fin 4) ≠ 3 from fun h => by
          have hh := congrArg Fin.val h; change n+a.val = 3 at hh; omega]
      simp
  right_inv j := by
    obtain ⟨a,b⟩ := j
    dsimp only
    split_ifs with h g
    · rfl
    · subst a; rfl
    · apply Prod.ext
      · apply Fin.ext; dsimp; omega
      · rfl

/-- Flatten the active ordinary packets consecutively, place the marked packet next,
then leave the unused ordinary packets in their original order. -/
def placement (k n : ℕ) (hn : n ≤ 3) :
    (Slots (n*k) k ⊕ Fin ((3-n)*k)) ≃ Slot k :=
  (((finProdFinEquiv.symm).sumCongr (Equiv.refl _)).sumCongr finProdFinEquiv.symm).trans
    (arrange k n hn)

def exchange (k n : ℕ) (hn : n ≤ 3) (r : CutIndex (n*k) k) : Wire k :=
  liftPerm (placement k n hn) (exchangePerm (n*k) k r)

private theorem total_ext (d k n : ℕ) (hn : n ≤ 3) :
    extend (placement k n hn) (Transfer.clasp (action d (n*k) k)) = joint d k n := by
  apply projector_extend
  · rintro (i|i)
    · exact Or.inl (show i.divNat.val<n from i.divNat.isLt)
    · exact Or.inr rfl
  · intro i
    change ¬ (n+i.divNat.val<n ∨ (⟨n+i.divNat.val,_⟩ : Fin 4)=3)
    have hi := i.divNat.isLt
    rintro (h|h)
    · omega
    · have hh := congrArg Fin.val h; change n+i.divNat.val=3 at hh; omega

theorem block_ext (d k n : ℕ) (hn : n ≤ 3) :
    extend (placement k n hn) (blockOp d (n*k) k) = block d k n := by
  rw [blockOp,extend_block,block,local_is_projector]
  congr 1
  · apply projector_extend
    · intro i; exact i.divNat.isLt
    · rintro (j|j)
      · change ¬ 3<n;omega
      · change ¬ n+j.divNat.val<n;omega
  · apply projector_extend
    · intro i; rfl
    · rintro (j|j)
      · intro h
        have hh := congrArg Fin.val h
        change j.divNat.val = 3 at hh
        have hj := j.divNat.isLt
        omega
      · intro h
        have hh := congrArg Fin.val h
        change n+j.divNat.val = 3 at hh
        have hj := j.divNat.isLt
        omega

theorem schur_on_slots (d k n : ℕ) (hn : n ≤ 3) (h : HomogeneousSchur d (n*k) k) :
    ((n*k+k).choose (n*k) : ℚ) • joint d k n =
      ∑ r : CutIndex (n*k) k, (weight (n*k) k r : ℚ) •
        (block d k n * act d k (exchange k n hn r) * block d k n) := by
  have eqn := congrArg (extend (placement k n hn)) (wire_schur_operator h)
  simpa only [map_smul,map_sum,map_mul,total_ext,block_ext,action,extend_perm,exchange,act] using eqn

end
end BlockPermanents.FourThickSlots
