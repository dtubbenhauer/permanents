import BlockPermanents.ThreeGeneralEnds
import BlockPermanents.ThreeLastCap

/-! The last thin resolution on the upright merges of the three-packet operator. -/
namespace BlockPermanents.ThreeLastRouted
open Bend PairBound ThreeGeneralOpen ThreeLastCap
open scoped BigOperators Matrix
noncomputable section

variable {I J : Type*}

private def remaining {d k : ℕ} (h : 1≤k) : Word d 1 ≃ Word d (k-(k-1)) :=
  (finCongr (by omega)).arrowCongr (Equiv.refl _)

def stackLast {d k : ℕ} (hk : 1≤k) (M : Word d k → Matrix (Word d k) I ℂ)
    (N : Matrix (Word d k) J ℂ) : Matrix (Word d k × Pair d) (I×J) ℂ :=
  fun a b => routed M N (ThreeSupport.lastProper k) a.1
    (remaining hk a.2.1,remaining hk a.2.2) b

private def allSlots {d k : ℕ} (hk : 1≤k) : Fin d × Word d (k-1) ≃ Word d k :=
  (((Equiv.funUnique (Fin 1) (Fin d)).symm.trans (remaining hk)).prodCongr (Equiv.refl _)).trans
    (splitWords d k (ThreeSupport.lastProper k))

private theorem first_slot {d k : ℕ} (hk : 1≤k) (b : Fin d) (v : Word d (k-1)) :
    allSlots hk (b,v) ⟨0,by omega⟩ = b := by
  change Fin.append (fun _ : Fin (k-(k-1)) => b) v _ = b
  let i : Fin (k-(k-1)) := ⟨0,by omega⟩
  have hi : Fin.cast (Nat.sub_add_cancel (cut_le (ThreeSupport.lastProper k))).symm
      ⟨0,by omega⟩ = Fin.castAdd (k-1) i := Fin.ext rfl
  rw [hi,Fin.append_left]

private theorem trace_same {d k : ℕ} (hk : 1≤k) (M : Word d k → Matrix (Word d k) I ℂ)
    (N : Matrix (Word d k) J ℂ) (hM : ∀ s i, Symmetric (fun w => M s w i))
    (hN : ∀ j, Symmetric (fun w => N w j)) :
    fullTrace (stackLast hk M N) = terminal (stack M) N := by
  ext s ⟨i,j⟩
  simp only [fullTrace,stackLast,routed_entry M N hM hN]
  have he := (allSlots (d:=d) hk).sum_comp (fun v => M s v i*star (N v j))
  rwa [Fintype.sum_prod_type] at he

private theorem stack_square {d k : ℕ} (hk : 1≤k) (M : Word d k → Matrix (Word d k) I ℂ)
    (N : Matrix (Word d k) J ℂ) :
    ∑ s, Support.reflected (routed M N (ThreeSupport.lastProper k) s) =
      Support.reflected (stackLast hk M N) := by
  ext i j
  simp only [Matrix.sum_apply,Support.reflected,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  exact ((remaining hk).prodCongr (remaining hk)).sum_comp
    (fun v => star (routed M N (ThreeSupport.lastProper k) s v i) *
      routed M N (ThreeSupport.lastProper k) s v j) |>.symm

/-- Resolve precisely the last term of the proper-cut sum on the genuine
three-packet mixed boundary. The two input factors may be entangled. -/
theorem routed_resolution {d k : ℕ} (S : Finset (Fin d)) (hS : 0<S.card) (hk : 1≤k)
    (M : Word d k → Matrix (Word d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ s i, Symmetric (fun w => M s w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (hs : ∀ w j, (∃ t,w t∉S) → N w j=0) :
    ∑ s, Support.reflected (routed M N (ThreeSupport.lastProper k) s) =
      Support.reflected (perpendicular S (stackLast hk M N)) +
      (S.card:ℂ)⁻¹ • Support.reflected (terminal (stack M) N) := by
  rw [stack_square,← trace_same hk M N hM hN]
  apply resolve S hS
  rintro s c ⟨i,j⟩ hc
  simp only [stackLast,routed_entry M N hM hN]
  apply Finset.sum_eq_zero
  intro v _
  change _ * star (N (allSlots hk (c,v)) j)=0
  rw [hs _ _ ⟨_,by rw [first_slot];exact hc⟩,star_zero,mul_zero]

def markedColumns {d k : ℕ} (S : Finset (Fin d)) :
    Matrix (Word d k) {w : Word d k // ∀ t,w t∈S} ℂ :=
  fun x y => symClasp d k x y.1

theorem marked_symmetric {d k : ℕ} (S : Finset (Fin d)) (j : {w : Word d k // ∀ t,w t∈S}) :
    Symmetric (fun w => markedColumns S w j) := by
  have hv : (symClasp d k).mulVec (fun y => if j.val=y then 1 else 0) =
      (fun w => markedColumns S w j) := by
    funext w
    simp [Matrix.mulVec,dotProduct,mul_ite,markedColumns]
  rw [← hv]
  exact projected_symmetric _ _ _

theorem marked_support {d k : ℕ} (S : Finset (Fin d)) (w : Word d k)
    (j : {w : Word d k // ∀ t,w t∈S}) (h : ∃ t,w t∉S) : markedColumns S w j=0 := by
  obtain ⟨t,ht⟩ := h
  have hi (p : Equiv.Perm (Fin k)) : w ≠ j.val ∘ p := fun he => ht (he ▸ j.prop (p t))
  simp [markedColumns,symClasp,hi]

end
end BlockPermanents.ThreeLastRouted
