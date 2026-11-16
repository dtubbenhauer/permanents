import BlockPermanents.FourTarget

/-! # Adding idle wires to an operator identity

A choice of active slots and an ordering of the remaining slots extends a
linear operator by the identity on every spectator. -/
namespace BlockPermanents.LocalAction
open scoped BigOperators
noncomputable section

variable {I Z W D : Type*}
abbrev EndW (I D : Type*) := Module.End ℂ ((I → D) → ℂ)

def join (e : I ⊕ Z ≃ W) (v : I → D) (w : W → D) : W → D :=
  Sum.elim v (fun z => w (e (.inr z))) ∘ e.symm

theorem join_self (e : I ⊕ Z ≃ W) (w : W → D) :
    join e (fun i => w (e (.inl i))) w = w := by
  funext i
  obtain ⟨t,rfl⟩ := e.surjective i
  cases t <;> simp [join]

theorem join_twice (e : I ⊕ Z ≃ W) (u v : I → D) (w : W → D) :
    join e u (join e v w) = join e u w := by simp [join,Function.comp_def]

theorem join_active (e : I ⊕ Z ≃ W) (v : I → D) (w : W → D) :
    (fun i => join e v w (e (.inl i))) = v := by simp [join,Function.comp_def]

def extend (e : I ⊕ Z ≃ W) : EndW I D →ₐ[ℚ] EndW W D where
  toFun A := {
    toFun := fun f w => A (fun v => f (join e v w)) (fun i => w (e (.inl i)))
    map_add' := by intro f g; funext w; exact congrFun (map_add A _ _) _
    map_smul' := by intro r f; funext w; exact congrFun (map_smul A r _) _ }
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := by apply LinearMap.ext; intro f; funext w; exact congrArg f (join_self e w)
  map_mul' A B := by
    apply LinearMap.ext; intro f; funext w
    change A (fun t => B (fun v => f (join e v w)) t) _ =
      A (fun t => B (fun v => f (join e v (join e t w))) (fun i => join e t w (e (.inl i)))) _
    simp only [join_twice,join_active]
  commutes' r := by
    apply LinearMap.ext; intro f; funext w
    change ((r:ℂ) * f (join e (fun i => w (e (.inl i))) w)) = (r:ℂ)*f w
    rw [join_self]

def liftPerm (e : I ⊕ Z ≃ W) : Equiv.Perm I →* Equiv.Perm W where
  toFun σ := e.permCongr (σ.sumCongr (Equiv.refl Z))
  map_one' := by ext j; obtain ⟨t,rfl⟩ := e.surjective j; cases t <;> simp [Equiv.permCongr_def]
  map_mul' p q := by ext j; obtain ⟨t,rfl⟩ := e.surjective j; cases t <;> simp [Equiv.permCongr_def]

theorem extend_perm (e : I ⊕ Z ≃ W) (σ : Equiv.Perm I) :
    extend e (Transfer.tensorAction I D σ) = Transfer.tensorAction W D (liftPerm e σ) := by
  apply LinearMap.ext; intro f; funext w
  apply congrArg f
  funext i
  obtain ⟨t,rfl⟩ := e.surjective i
  cases t <;> simp [join,liftPerm,Equiv.permCongr_def,Function.comp_def]

theorem average_map {A B G : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
    [Fintype G] [Group G] (T : A →ₐ[ℚ] B) (ρ : G →* A) :
    T (Transfer.clasp ρ) = Transfer.clasp (T.toMonoidHom.comp ρ) := by
  simp [Transfer.clasp]

theorem extend_clasp [Fintype I] [DecidableEq I] (e : I ⊕ Z ≃ W) :
    extend e (Transfer.clasp (Transfer.tensorAction I D)) =
      Transfer.clasp ((Transfer.tensorAction W D).comp (liftPerm e)) := by
  simp only [Transfer.clasp,map_smul,map_sum,extend_perm,MonoidHom.comp_apply]

end
end BlockPermanents.LocalAction
