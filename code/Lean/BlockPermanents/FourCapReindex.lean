import BlockPermanents.FourPortNorm

/-! # Relabeling a supported port on the five-strand raw row -/
namespace BlockPermanents.FourLastCaps
open Equiv
open scoped BigOperators Matrix
noncomputable section
variable {D : Type*} [Fintype D] [DecidableEq D]
abbrev Slots := Option (Fin 4)

private theorem permFix {T : Type*} (q : Perm (Option T)) (h : q none = none) :
    q = q.removeNone.optionCongr := by
  apply Equiv.ext; intro i
  cases i with
  | none => exact h
  | some j =>
    have hn : ∃ a, q (some j) = some a := by
      cases he : q (some j) with
      | none => exact (Option.some_ne_none j (q.injective (he.trans h.symm))).elim
      | some a => exact ⟨a,rfl⟩
    exact (Equiv.removeNone_some q hn).symm

omit [Fintype D] [DecidableEq D] in
private theorem rearrange (q : Perm Slots) (b : Slots) :
    ∃ π : Perm (Fin 4), ∀ (w : Fin 4 → D) c,
      insertAt (q b) w c ∘ q = insertAt b (w ∘ π) c := by
  let s := (swap none b).trans (q.trans (swap none (q b)))
  have hn : s none = none := by simp [s]
  have he := permFix s hn
  refine ⟨s.removeNone,?_⟩
  intro w c; funext i
  have hh := Equiv.congr_fun he ((swap none b) i)
  simp only [s,Equiv.trans_apply,swap_apply_self] at hh
  change ((swap none (q b)) (q i)).elim c w = _
  rw [hh]
  unfold insertAt
  cases hr : (swap none b) i <;> rfl

omit [Fintype D] [DecidableEq D] in
theorem cap_reindex (S : Finset D) (P Q : Finset Slots) (q : Perm Slots)
    (hq : ∀ i, q i ∈ P ↔ i ∈ Q) (z : Raw D) (w : Fin 4 → D) :
    portCap S P (fun t c => z (t ∘ q) c) w = portCap S Q z w := by
  have hc : P.card = Q.card := Finset.card_equiv q.symm (fun a => by simpa using hq (q.symm a))
  unfold portCap; rw [hc]; congr 1
  rw [Finset.sum_comm,Finset.sum_comm (t:=Q)]
  apply Finset.sum_equiv q.symm (fun a => by simpa using hq (q.symm a))
  intro a _
  obtain ⟨π,h⟩ := rearrange (D:=D) q (q.symm a)
  simp only [apply_symm_apply] at h
  simp_rw [h]
  exact (Group.mulRight_bijective π).sum_comp (fun σ : Perm (Fin 4) =>
    ∑ c ∈ S, z (insertAt (q.symm a) (w ∘ σ) c) c)


end
end BlockPermanents.FourLastCaps
