import BlockPermanents.LocalGroup
import BlockPermanents.WireSchur
/-! # The local Schur opening on the four quadratic packets -/
namespace BlockPermanents.FourLocalSlots
open FourTarget LocalGroup LocalAction WireSchur Bend SchurNormalization
open scoped BigOperators
noncomputable section

def joint (d n : ℕ) := projector (Fin d) (fun j : Slot 2 => j.1.val < n ∨ j.1=3)
def marked (d : ℕ) := projector (Fin d) (fun j : Slot 2 => j.1=3)
def block (d n : ℕ) := localClasp d 2 n * marked d

theorem local_is_projector (d n : ℕ) :
    localClasp d 2 n = projector (Fin d) (fun j : Slot 2 => j.1.val < n) := by
  have he : group 2 n = fixedOutside (fun j : Slot 2 => j.1.val < n) := by
    ext σ
    simp only [group,fixedOutside,Subgroup.mem_mk,Set.mem_setOf_eq,not_lt]
  letI : Fintype (group 2 n) := Fintype.ofFinite _
  letI : Fintype (fixedOutside (fun j : Slot 2 => j.1.val < n)) := Fintype.ofFinite _
  exact avg_eq (MulEquiv.subgroupCongr he).toEquiv _ _ (fun x => rfl)

/-- The active ordinary strands come first, then both marked strands.
The remaining strands retain their order and become spectators. -/
def placement (n : ℕ) (hn : n ≤ 3) :
    (Slots (n*2) 2 ⊕ Fin ((3-n)*2)) ≃ Slot 2 where
  toFun
    | .inl (.inl i) => (⟨i.val/2,by omega⟩,⟨i.val%2,by omega⟩)
    | .inl (.inr i) => (3,i)
    | .inr i => (⟨n+i.val/2,by omega⟩,⟨i.val%2,by omega⟩)
  invFun j := if a : j.1.val < n then .inl (.inl ⟨2*j.1.val+j.2.val,by omega⟩)
    else if b : j.1=3 then .inl (.inr j.2) else .inr ⟨2*(j.1.val-n)+j.2.val,by
      have : j.1.val ≠ 3 := fun e => b (Fin.ext e)
      omega⟩
  left_inv j := by
    rcases j with ((i|i)|i)
    · simp only [show i.val/2<n by omega, dif_pos]
      congr 3; omega
    · simp [show ¬(3:Fin 4).val<n by change ¬3<n;omega]
    · simp only [show ¬ n+i.val/2<n by omega,dif_neg,
        show (⟨n+i.val/2,by omega⟩:Fin 4) ≠ 3 from fun h => by
          have hh := congrArg Fin.val h; change n+i.val/2 = 3 at hh; omega]
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp
      omega
  right_inv j := by
    obtain ⟨a,b⟩ := j
    dsimp only
    split_ifs with h g
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
    · subst a; rfl
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

def exchange (n : ℕ) (hn : n ≤ 3) (r : CutIndex (n*2) 2) : Wire 2 :=
  liftPerm (placement n hn) (exchangePerm (n*2) 2 r)

private theorem total_ext (d n : ℕ) (hn : n ≤ 3) :
    extend (placement n hn) (Transfer.clasp (action d (n*2) 2)) = joint d n := by
  apply projector_extend
  · rintro (i|i)
    · exact Or.inl (show i.val/2<n by omega)
    · exact Or.inr rfl
  · intro i
    change ¬ (n+i.val/2<n ∨ (⟨n+i.val/2,_⟩ : Fin 4)=3)
    rintro (h|h)
    · omega
    · have hh := congrArg Fin.val h; change n+i.val/2=3 at hh; omega

private theorem block_ext (d n : ℕ) (hn : n ≤ 3) :
    extend (placement n hn) (blockOp d (n*2) 2) = block d n := by
  rw [blockOp,extend_block,block,local_is_projector]
  congr 1
  · apply projector_extend
    · intro i; change i.val/2<n;omega
    · rintro (j|j)
      · change ¬ 3<n;omega
      · change ¬ n+j.val/2<n;omega
  · apply projector_extend
    · intro i; rfl
    · rintro (j|j)
      · intro h
        have hh := congrArg Fin.val h
        change j.val/2 = 3 at hh
        omega
      · intro h
        have hh := congrArg Fin.val h
        change n+j.val/2 = 3 at hh
        omega

theorem schur_on_slots (d n : ℕ) (hn : n ≤ 3) (h : HomogeneousSchur d (n*2) 2) :
    ((n*2+2).choose (n*2) : ℚ) • joint d n =
      ∑ r : CutIndex (n*2) 2, (weight (n*2) 2 r : ℚ) •
        (block d n * act d 2 (exchange n hn r) * block d n) := by
  have eqn := congrArg (extend (placement n hn)) (wire_schur_operator h)
  simpa only [map_smul,map_sum,map_mul,total_ext,block_ext,action,extend_perm,exchange,act] using eqn

end
end BlockPermanents.FourLocalSlots
