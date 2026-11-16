import BlockPermanents.LocalAction
import Mathlib.GroupTheory.Perm.Support

/-! # Permutation averages on named sets of thin slots -/
namespace BlockPermanents.LocalGroup
open LocalAction
open scoped BigOperators
noncomputable section

variable {I Z W D : Type*} [Fintype I] [Fintype Z] [Fintype W] [DecidableEq I] [DecidableEq W]
def fixedOutside (P : W → Prop) : Subgroup (Equiv.Perm W) where
  carrier := {σ | ∀ j, ¬ P j → σ j = j}
  one_mem' _ _ := rfl
  mul_mem' ha hb j hj := by rw [Equiv.Perm.mul_apply,hb j hj,ha j hj]
  inv_mem' {σ} ha j hj := σ.injective (by rw [Equiv.Perm.apply_inv_self,ha j hj])

local instance (P : W → Prop) : Fintype (fixedOutside P) := Fintype.ofFinite _
def projector (D : Type*) (P : W → Prop) : EndW W D :=
  Transfer.clasp ((Transfer.tensorAction W D).comp (fixedOutside P).subtype)

theorem avg_eq {A B R : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    [Ring R] [Algebra ℚ R] (e : A ≃ B) (f : A →* R) (g : B →* R) (h : ∀ x, f x = g (e x)) :
    Transfer.clasp f = Transfer.clasp g := by
  simp only [Transfer.clasp,Fintype.card_congr e,Fintype.sum_equiv e f g h]

private def pred_in (e : I ⊕ Z ≃ W) (P : W → Prop)
    (a : ∀ i, P (e (.inl i))) (b : ∀ j, ¬P (e (.inr j))) : I ≃ {w // P w} := by
  let f (i : I) : {w // P w} := ⟨e (.inl i),a i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h; exact Sum.inl.inj (e.injective (congrArg Subtype.val h))
  · intro ⟨w,h⟩; obtain ⟨v,rfl⟩ := e.surjective w
    cases v with
    | inl i => exact ⟨i,rfl⟩
    | inr j => exact (b j h).elim

omit [Fintype Z] [DecidableEq W] in
theorem projector_extend (e : I ⊕ Z ≃ W) (P : W → Prop)
    (a : ∀ i, P (e (.inl i))) (b : ∀ j, ¬P (e (.inr j))) :
    extend e (Transfer.clasp (Transfer.tensorAction I D)) = projector D P := by
  classical
  let ee := pred_in e P a b
  let f := ee.permCongr.trans (Equiv.Perm.subtypeEquivSubtypePerm P)
  let g : Equiv.Perm I ≃ (fixedOutside P) := f
  rw [extend_clasp]
  apply avg_eq g
  intro σ
  apply congrArg (Transfer.tensorAction W D)
  ext w
  obtain ⟨w,rfl⟩ := e.surjective w
  cases w with
  | inl i =>
    change (liftPerm e σ) (e (.inl i)) = (Equiv.Perm.ofSubtype (ee.permCongr σ)) (e (.inl i))
    have hi : e (.inl i) = ((ee i : {w // P w}):W) := rfl
    rw [hi,Equiv.Perm.ofSubtype_apply_coe]
    simp [Equiv.permCongr_def]
    change (liftPerm e σ) (e (.inl i)) = e (.inl (σ i))
    simp [liftPerm,Equiv.permCongr_def]
  | inr j =>
    change (liftPerm e σ) (e (.inr j)) = ((g σ : fixedOutside P):Equiv.Perm W) (e (.inr j))
    rw [(g σ).prop _ (b j)]
    simp [liftPerm,Equiv.permCongr_def]

omit [DecidableEq W] in
theorem conjugate (τ : Equiv.Perm W) (P Q : W → Prop) (h : ∀ i, P i ↔ Q (τ i)) :
    Transfer.tensorAction W D τ * projector D P * Transfer.tensorAction W D τ⁻¹ = projector D Q := by
  classical
  let c (σ : fixedOutside P) : fixedOutside Q := ⟨τ * σ.1 * τ⁻¹,by
    intro j hj
    change τ (σ.val (τ⁻¹ j)) = j
    rw [σ.prop,Equiv.Perm.apply_inv_self]
    simpa using (not_congr (h (τ⁻¹ j))).mpr (by simpa using hj)⟩
  let u (σ : fixedOutside Q) : fixedOutside P := ⟨τ⁻¹ * σ.1 * τ,by
    intro i hi
    change τ⁻¹ (σ.val (τ i)) = i
    rw [σ.prop _ (fun hh => hi ((h i).mpr hh)),Equiv.Perm.inv_apply_self]⟩
  let e : fixedOutside P ≃ fixedOutside Q :=
    ⟨c,u,fun s => Subtype.ext (by simp [c,u,mul_assoc]),fun s => Subtype.ext (by simp [c,u,mul_assoc])⟩
  simp only [projector,Transfer.clasp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,
    ← map_mul,MonoidHom.comp_apply,Fintype.card_congr e]
  congr 1
  apply Fintype.sum_equiv e
  intro i
  rfl

def leftPlacement {J : Type*} (e : (I ⊕ J) ⊕ Z ≃ W) : I ⊕ (J ⊕ Z) ≃ W :=
  (Equiv.sumAssoc I J Z).symm.trans e
def rightPlacement {J : Type*} (e : (I ⊕ J) ⊕ Z ≃ W) : J ⊕ (I ⊕ Z) ≃ W :=
  (Equiv.sumAssoc J I Z).symm.trans (((Equiv.sumComm J I).sumCongr (Equiv.refl Z)).trans e)

omit [Fintype I] [Fintype Z] [Fintype W] [DecidableEq I] [DecidableEq W] in
private theorem lift_pair {J : Type*} (e : (I ⊕ J) ⊕ Z ≃ W)
    (p : Equiv.Perm I) (q : Equiv.Perm J) :
    liftPerm e (p.sumCongr q) = liftPerm (leftPlacement e) p * liftPerm (rightPlacement e) q := by
  ext t
  obtain ⟨t,rfl⟩ := e.surjective t
  rcases t with ((i|j)|z) <;> simp [liftPerm,leftPlacement,rightPlacement,Equiv.permCongr_def]

theorem extend_block {J : Type*} [Fintype J] [DecidableEq J]
    (e : (I ⊕ J) ⊕ Z ≃ W) :
    extend e (Transfer.clasp ((Transfer.tensorAction (I ⊕ J) D).comp (Equiv.Perm.sumCongrHom I J))) =
      extend (leftPlacement e) (Transfer.clasp (Transfer.tensorAction I D)) *
      extend (rightPlacement e) (Transfer.clasp (Transfer.tensorAction J D)) := by
  classical
  simp only [Transfer.clasp,map_smul,map_sum,MonoidHom.comp_apply,extend_perm,
    Fintype.card_prod,Nat.cast_mul,mul_inv,smul_mul_assoc,mul_smul_comm,smul_smul,
    Fintype.sum_prod_type, Finset.sum_mul,Finset.mul_sum,Equiv.Perm.sumCongrHom_apply,
    lift_pair,map_mul]
  rw [← Finset.smul_sum,smul_smul,mul_comm,Finset.sum_comm]


end
end BlockPermanents.LocalGroup
