import BlockPermanents.RoutingExits

/-! # The literal spectator attachment of the previous operator -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {n k : ℕ} {R : Type*} [Ring R] [Algebra ℚ R]

/-- Extend a permutation of the old strands by the identity on the spectator. -/
def attach (a : Fin (n+1)) : Wire n k →* Wire (n+1) k where
  toFun := insertWire a a 1
  map_one' := by
    apply Equiv.ext; rintro ⟨i,t⟩
    by_cases hi : i=a
    · subst i; simp
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi; simp
  map_mul' p q := by
    apply Equiv.ext; rintro ⟨i,t⟩
    by_cases hi : i=a
    · subst i; simp [Perm.mul_apply]
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi; simp [Perm.mul_apply]

private theorem attach_within (a : Fin (n+1)) (g : Fin n → Perm (Fin k)) :
    attach a (within g) = within (fun i => ((finSuccEquiv' a) i).elim 1 g) := by
  apply Equiv.ext; rintro ⟨i,t⟩
  change insertWire a a 1 (within g) (i,t) = (i,((finSuccEquiv' a i).elim 1 g) t)
  by_cases hi : i=a
  · subst i; simp
  · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi; simp [within]

private theorem absorb_subclasp (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) :
    internal ρ * internal (ρ.comp (attach a)) = internal ρ ∧
      internal (ρ.comp (attach a)) * internal ρ = internal ρ := by
  let old := (ρ.comp (attach a)).comp within
  have left (g : Fin n → Perm (Fin k)) : internal ρ * old g = internal ρ := by
    dsimp only [old,MonoidHom.comp_apply]
    rw [attach_within]; exact Transfer.absorb_right (ρ.comp within) _
  have right (g : Fin n → Perm (Fin k)) : old g * internal ρ = internal ρ := by
    dsimp only [old,MonoidHom.comp_apply]
    rw [attach_within]; exact Transfer.absorb_left (ρ.comp within) _
  change internal ρ * Transfer.clasp old = internal ρ ∧ Transfer.clasp old * internal ρ = internal ρ
  have hc : (Fintype.card (Fin n → Perm (Fin k)) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Transfer.clasp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,left,right,
    Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ,inv_smul_smul₀ hc,and_self]

/-- The stationary old diagram is precisely the old operator acting on its
old slots with identity on the new packet, then sandwiched between the
internal packet clasps of the enlarged boundary. -/
theorem exit_attachment (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) (hk : 0<k) :
    exitOp ρ a a (fun b => n/b) = internal ρ * iterate (ρ.comp (attach a)) * internal ρ := by
  obtain ⟨hl,hr⟩ := absorb_subclasp ρ a
  simp only [iterate,exitOp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,
    Routing.relativeA_table _ hk]
  apply congrArg (_ • ·)
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (_ • ·)
  unfold compressed
  rw [← mul_assoc,← mul_assoc,hl,mul_assoc _ (internal (ρ.comp (attach a))),hr]
  rfl

/-- The only input packet always travels whole, giving the initial operator A₁=0. -/
theorem iterate_one (ρ : Wire 1 k →* R) (hk : 0<k) : iterate ρ = 0 := by
  rw [iterate_expand _ hk]
  apply Finset.sum_eq_zero; intro M _
  have row (i : Fin 1) : M.entries i 0=k := by simpa only [Fin.sum_univ_one] using M.rowSum i
  have empty : M.splitInputs=∅ := Finset.eq_empty_iff_forall_not_mem.mpr
    (fun i hi => (split_mem M i).mp hi 0 (row i))
  simp [empty]

end
end BlockPermanents.RoutingFibres
