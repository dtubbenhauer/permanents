import BlockPermanents.FourThickSlots

/-! # Straight and full exchanges on the four packets -/
namespace BlockPermanents.FourThickSlots
open FourTarget LocalAction WireSchur Bend
noncomputable section

theorem exchange_zero (k n : ℕ) (hn : n ≤ 3) :
    exchange k n hn ⟨0,by omega⟩ = 1 := by
  let r : CutIndex (n*k) k := ⟨0,by omega⟩
  have hz : exchangePerm (n*k) k r = 1 := by
    apply Equiv.ext
    rintro (i|i)
    · obtain ⟨j|j,rfl⟩ := (splitSlot (leftLe r)).surjective i
      · exact exchange_left_prefix _ _
      · exact Fin.elim0 j
    · obtain ⟨j|j,rfl⟩ := (splitSlot (rightLe r)).surjective i
      · exact exchange_right_prefix _ _
      · exact Fin.elim0 j
  change liftPerm _ (exchangePerm _ _ r) = _
  rw [hz,map_one]

private theorem straight (k n : ℕ) (hn : n ≤ 3) (i : Fin n) (z : Fin k) :
    placement k n hn (.inl (.inl (finProdFinEquiv (i,z)))) = (⟨i.val,by omega⟩,z) := by
  simp only [placement,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,Equiv.symm_apply_apply]
  rfl

private theorem split_left_val {p r : ℕ} (h : r ≤ p) (j : Fin (p-r)) :
    (splitSlot h (.inl j)).val = j.val := rfl

private theorem split_right_val {p r : ℕ} (h : r ≤ p) (j : Fin r) :
    (splitSlot h (.inr j)).val = p-r+j.val := rfl

private theorem penultimate (m k : ℕ) : (m+1)*k-k=m*k := by rw [Nat.succ_mul,Nat.add_sub_cancel]

/-- At the full cut the entire last active packet swaps with the marked packet.
The survivor slots keep their order. -/
theorem exchange_full (k n : ℕ) (hn : n ≤ 3) (hp : 0<n) :
    exchange k n hn ⟨k,by
      have := Nat.mul_le_mul_right k hp
      simp only [Nat.one_mul] at this
      omega⟩ = wires k (Equiv.swap (⟨n-1,by omega⟩ : Fin 4) 3) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let r : CutIndex ((m+1)*k) k := ⟨k,by simp [Nat.succ_mul]⟩
  let P := placement k (m+1) hn
  let slot : Fin 4 := ⟨m,by omega⟩
  let swap := Equiv.swap slot 3
  have three : slot ≠ 3 := fun h => by have hh := congrArg Fin.val h;change m=3 at hh;omega
  change liftPerm P (exchangePerm _ _ r) = wires k swap
  have mv (i : Slots ((m+1)*k) k) : liftPerm P (exchangePerm _ _ r) (P (.inl i)) =
      P (.inl (exchangePerm _ _ r i)) := by simp [liftPerm,Equiv.permCongr_def]
  have stay (i : Fin ((3-(m+1))*k)) : liftPerm P (exchangePerm _ _ r) (P (.inr i)) =
      P (.inr i) := by simp [liftPerm,Equiv.permCongr_def]
  have endL (i : Fin r) :
      P (.inl (.inl (splitSlot (leftLe r) (.inr i)))) = (slot,(i : Fin k)) := by
    have h : splitSlot (leftLe r) (.inr i) = finProdFinEquiv ((⟨m,by omega⟩ : Fin (m+1)),(i : Fin k)) := by
      apply Fin.ext
      rw [split_right_val]
      change (m+1)*k-k+i.val=i.val+k*m
      exact (congrArg (· + i.val) (penultimate m k)).trans ((Nat.add_comm _ _).trans (congrArg (i.val + ·) (Nat.mul_comm m k)))
    rw [h]
    exact straight _ _ _ _ _
  have endR (i : Fin r) :
      P (.inl (.inr (splitSlot (rightLe r) (.inr i)))) = (3,(i : Fin k)) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (splitSlot (rightLe r) (.inr i)).val = i.val
      rw [split_right_val]; change k-k+i.val=i.val;omega
  apply Equiv.ext
  intro x
  obtain ⟨(i|j)|j,rfl⟩ := P.surjective x
  · obtain ⟨j|j,rfl⟩ := (splitSlot (leftLe r)).surjective i
    · rw [mv,exchange_left_prefix]
      let b := splitSlot (leftLe r) (.inl j)
      let z := b.divNat
      have hlt : z.val < m := by
        change b.val/k<m
        have hk : 0<k := Nat.zero_lt_of_lt b.modNat.isLt
        apply (Nat.div_lt_iff_lt_mul hk).mpr
        change (splitSlot (leftLe r) (.inl j)).val < _
        rw [split_left_val]
        have hj := j.isLt
        change j.val < (m+1)*k-k at hj
        exact hj.trans_eq (penultimate m k)
      let a : Fin 4 := ⟨z.val,by omega⟩
      change (a,b.modNat) = (swap a,b.modNat)
      rw [Equiv.swap_apply_of_ne_of_ne (show a ≠ slot from fun e => by
        have h := congrArg Fin.val e;change z.val=m at h;omega)
        (show a ≠ 3 from fun e => by have h := congrArg Fin.val e;change z.val=3 at h;omega)]
    · rw [mv,exchange_left_suffix,endR,endL]
      exact Prod.ext (Equiv.swap_apply_left slot 3).symm rfl
  · obtain ⟨j|j,rfl⟩ := (splitSlot (rightLe r)).surjective j
    · have h := j.isLt;change j.val<k-k at h;omega
    · rw [mv,exchange_right_suffix,endL,endR]
      exact Prod.ext (Equiv.swap_apply_right slot 3).symm rfl
  · rw [stay]
    let a : Fin 4 := ⟨m+1+j.divNat.val,by have hj := j.divNat.isLt;omega⟩
    change (a,j.modNat)=(swap a,j.modNat)
    rw [Equiv.swap_apply_of_ne_of_ne (show a ≠ slot from fun e => by
      have h := congrArg Fin.val e; change m+1+j.divNat.val=m at h;omega)
      (show a ≠ 3 from fun e => by
        have h := congrArg Fin.val e; change m+1+j.divNat.val=3 at h
        have hj := j.divNat.isLt;omega)]

end
end BlockPermanents.FourThickSlots
