import BlockPermanents.WireSchur
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fintype

/-! # Double cosets of the two packet permutation groups

The number of left slots sent into the right packet classifies a permutation
up to independent relabeling of the two packets at both ends.
-/

namespace BlockPermanents.SchurClass
open Bend WireSchur
open scoped BigOperators
noncomputable section

/-- The number of left input slots sent to the right packet. -/
def crossCount {p q : ℕ} (g : Equiv.Perm (Slots p q)) : ℕ :=
  (Finset.univ.filter (fun i : Fin p => (g (Sum.inl i)).isRight)).card

private def rightStayed {p q : ℕ} (g : Equiv.Perm (Slots p q)) : ℕ :=
  (Finset.univ.filter (fun i : Fin q => (g (Sum.inr i)).isRight)).card

private theorem right_total {p q : ℕ} (g : Equiv.Perm (Slots p q)) :
    crossCount g + rightStayed g = q := by
  let f (i : Slots p q) : ℕ := if i.isRight then 1 else 0
  have e := Equiv.sum_comp g f
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at e
  simpa [crossCount, rightStayed, f] using e

theorem crossCount_le_min {p q : ℕ} (g : Equiv.Perm (Slots p q)) :
    crossCount g ≤ min p q := by
  have hp : crossCount g ≤ p := by
    simpa [crossCount] using (Finset.card_filter_le Finset.univ (fun i : Fin p => (g (Sum.inl i)).isRight))
  have := right_total g
  omega

/-- The in-range cut corresponding to the crossing count. -/
def crossIndex {p q : ℕ} (g : Equiv.Perm (Slots p q)) : CutIndex p q :=
  ⟨crossCount g, Nat.lt_succ_of_le (crossCount_le_min g)⟩

@[simp] theorem crossCount_exchange {p q : ℕ} (r : CutIndex p q) :
    crossCount (exchangePerm p q r) = r := by
  rw [crossCount, Finset.card_filter]
  rw [← (splitSlot (leftLe r)).sum_comp
    (fun i => if ((exchangePerm p q r) (.inl i)).isRight then 1 else 0)]
  rw [Fintype.sum_sum_type]
  simp

/-- Relabel a finite set so that two equally large classes correspond. -/
private theorem matchBool {I : Type*} [Fintype I] (s t : I → Bool)
    (h : (Finset.univ.filter (fun i => s i)).card =
      (Finset.univ.filter (fun i => t i)).card) :
    ∃ a : Equiv.Perm I, ∀ i, t (a i) = s i := by
  classical
  let S := fun i => s i = true
  let T := fun i => t i = true
  have he : Fintype.card (Subtype S) = Fintype.card (Subtype T) := by
    simpa [Fintype.card_subtype, S, T] using h
  let e := Fintype.equivOfCardEq he
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  by_cases hi : S i
  · exact (e.extendSubtype_mem i hi).trans hi.symm
  · exact (Bool.eq_false_of_not_eq_true (e.extendSubtype_not_mem i hi)).trans
      (Bool.eq_false_of_not_eq_true hi).symm

/-- The standard exchange is a representative of every packet double coset. -/
theorem factorization {p q : ℕ} (g : Equiv.Perm (Slots p q)) :
    ∃ (a c : Equiv.Perm (Fin p)) (b e : Equiv.Perm (Fin q)),
      g = a.sumCongr b * exchangePerm p q (crossIndex g) * c.sumCongr e := by
  let k := exchangePerm p q (crossIndex g)
  have hk : crossCount k = crossCount g := crossCount_exchange (crossIndex g)
  obtain ⟨c, hc⟩ := matchBool (fun i : Fin p => (g (.inl i)).isRight)
    (fun i : Fin p => (k (.inl i)).isRight) hk.symm
  have hv : rightStayed g = rightStayed k := by
    have := right_total g
    have := right_total k
    omega
  obtain ⟨e, he⟩ := matchBool (fun i : Fin q => (g (.inr i)).isRight)
    (fun i : Fin q => (k (.inr i)).isRight) hv
  let m := k * c.sumCongr e
  have color (i : Slots p q) : (m i).isRight = (g i).isRight := by
    cases i with
    | inl i => exact hc i
    | inr i => exact he i
  have h : g * m⁻¹ ∈ (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range := by
    apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
    rintro _ ⟨i, rfl⟩
    have hi := color (m.symm (Sum.inl i))
    rw [m.apply_symm_apply] at hi
    change ∃ j, Sum.inl j = g (m.symm (.inl i))
    cases hgi : g (m.symm (Sum.inl i)) with
    | inl j => exact ⟨j, rfl⟩
    | inr j => simp [hgi] at hi
  obtain ⟨⟨a,b⟩, hab⟩ := h
  change a.sumCongr b = g * m⁻¹ at hab
  refine ⟨a,c,b,e,?_⟩
  rw [hab, mul_assoc]
  exact (inv_mul_cancel_right g m).symm

/-- Relabeling the input and output packets preserves the number of crossed strands. -/
theorem crossCount_relabel {p q : ℕ} (g : Equiv.Perm (Slots p q))
    (a c : Equiv.Perm (Fin p)) (b e : Equiv.Perm (Fin q)) :
    crossCount (a.sumCongr b * g * c.sumCongr e) = crossCount g := by
  have side (x : Slots p q) : (a.sumCongr b x).isRight = x.isRight := by
    cases x <;> rfl
  simp only [crossCount, Finset.card_filter, Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
    Sum.map_inl]
  change (∑ i : Fin p, if ((a.sumCongr b) (g (.inl (c i)))).isRight then 1 else 0) = _
  simp only [side]
  exact Equiv.sum_comp c (fun i => if (g (.inl i)).isRight then 1 else 0)

/-- The crossing count characterizes precisely which standard exchange can occur. -/
theorem factorization_iff {p q : ℕ} (g : Equiv.Perm (Slots p q)) (r : CutIndex p q) :
    (∃ (a c : Equiv.Perm (Fin p)) (b e : Equiv.Perm (Fin q)),
      g = a.sumCongr b * exchangePerm p q r * c.sumCongr e) ↔ crossCount g = r := by
  constructor
  · rintro ⟨a, c, b, e, rfl⟩
    rw [crossCount_relabel, crossCount_exchange]
  · intro h
    have eq : crossIndex g = r := Fin.ext h
    rw [← eq]
    exact factorization g

end
end BlockPermanents.SchurClass
