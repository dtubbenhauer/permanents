import BlockPermanents.CycleMatching
import Mathlib.Logic.Equiv.Fintype

/-! Averaging a prescribed family of distinct label positions gives the
same answer for any chosen embedding into the ambient labels. -/
namespace BlockPermanents.FaceSampling
open CycleMatching Matchings
noncomputable section

/-- Extend the correspondence between two equally labeled configurations. -/
theorem perm_between {A : Type*} {m : ℕ} (i j : A ↪ Fin m) :
    ∃ p : Equiv.Perm (Fin m), ∀ a, p (i a) = j a := by
  classical
  letI : Fintype A := Fintype.ofInjective i i.injective
  let e := i.toEquivRange.symm.trans j.toEquivRange
  refine ⟨e.extendSubtype, fun a => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (i a) (Set.mem_range_self a)]
  exact congrArg Subtype.val (show e (i.toEquivRange a) = j.toEquivRange a by simp [e])

/-- Uniformly sampled distinct labels, with zero value for an impossible shape. -/
def sample {A : Type*} (m : ℕ) (F : (A → Fin m) → ℝ) : ℝ := by
  classical
  exact if h : Nonempty (A ↪ Fin m) then
      average m fun σ => F (σ ∘ (Classical.choice h : A ↪ Fin m))
    else 0

theorem sample_eq {A : Type*} {m : ℕ} (e : A ↪ Fin m) (F : (A → Fin m) → ℝ) :
    sample m F = average m (fun σ => F (σ ∘ e)) := by
  classical
  have hn : Nonempty (A ↪ Fin m) := ⟨e⟩
  rw [sample, dif_pos hn]
  obtain ⟨p, hp⟩ := perm_between e (Classical.choice hn)
  have h (σ : S m) : (σ*p) ∘ e = σ ∘ (Classical.choice hn : A ↪ Fin m) := by funext i; simp [hp]
  simpa only [h] using average_relabel (fun σ : S m => F (σ ∘ e)) p

/-- Natural restriction of a uniform injection to a smaller collection of
labeled positions, retaining every internal dependence of F. -/
theorem restrict {A B : Type*} {m : ℕ} (i : A ↪ B) (j : B ↪ Fin m)
    (F : (A → Fin m) → ℝ) :
    sample m (fun v : B → Fin m => F (v ∘ i)) = sample m F := by
  rw [sample_eq j, sample_eq (i.trans j) F]
  rfl

end
end BlockPermanents.FaceSampling
