import BlockPermanents.FourWireCut

/-! The spectator clasp on the unbent ordinary boundary descends
through a complete marked cap to the four-strand output clasp. -/
namespace BlockPermanents.FourWireCut
open Bend Closures FourTarget FourCapOrbit FourCapValues FourFullValues FourLastCaps Equiv
open LocalGroup LocalAction
open scoped BigOperators Matrix
noncomputable section

private def spectatorPlace : Fin 4 ⊕ Fin 2 ≃ Pos :=
  Equiv.ofBijective (Sum.elim ![(0,1),(1,0),(1,1),(0,0)] ![(2,0),(2,1)]) (by decide)

private def allWord {d : ℕ} (v : Word d 4) (b t : Fin d) :=
  ordinaryWord (insertAt anchor v b) t

private theorem spectator_read {d : ℕ} (v : Word d 4) (b t : Fin d) (i : Fin 4) :
    allWord v b t (spectatorPlace (.inl i)) = v i := by
  fin_cases i <;> rfl

private theorem choose_output {d : ℕ} (u v : Word d 4) (b t : Fin d) :
    join spectatorPlace u (allWord v b t) = allWord u b t := by
  funext i
  obtain ⟨i,rfl⟩ := spectatorPlace.surjective i
  rcases i with i|j
  · simp [join,spectator_read]
  · simp only [join,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    fin_cases j <;> rfl

private theorem sp_eval {d : ℕ} (U : (Pos → Fin d) → ℂ) (v : Word d 4) (b t : Fin d) :
    spectator U (allWord v b t) =
      (24:ℂ)⁻¹ * ∑ p : Perm (Fin 4), U (allWord (v ∘ p) b t) := by
  have h := projector_extend (D:=Fin d) spectatorPlace (fun j : Pos => j.1.val<2)
    (by decide) (by decide)
  rw [spectator,← h]
  change Transfer.clasp (Transfer.tensorAction (Fin 4) (Fin d))
      (fun u => U (join spectatorPlace u (allWord v b t)))
      (fun i => allWord v b t (spectatorPlace (.inl i))) = _
  simp only [choose_output,spectator_read,Transfer.clasp,LinearMap.smul_apply,
    LinearMap.sum_apply,Finset.sum_apply,Pi.smul_apply,Rat.smul_def,smul_eq_mul,
    Rat.cast_inv,Rat.cast_natCast,Fintype.card_perm,Fintype.card_fin]
  norm_num [Transfer.tensorAction,Nat.factorial]

theorem closed_spectator {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) :
    closedCut (spectator U) H = clasp (closedCut U H) := by
  funext v
  change (∑ b, ∑ t, spectator U (allWord v b t) * star (H ![b,t])) = _
  simp only [sp_eval,mul_assoc,Finset.sum_mul,← Finset.mul_sum,clasp,sumSlots,Fintype.card_fin]
  norm_num only [show (4:ℕ).factorial = 24 by decide,Nat.cast_ofNat]
  congr 1
  let g (p : Perm (Fin 4)) (b t : Fin d) := U (allWord (v ∘ p) b t) * star (H ![b,t])
  change (∑ b, ∑ t, ∑ p, g p b t) = ∑ p : Perm (Fin 4), ∑ b, ∑ t, g p.symm b t
  have inv := Equiv.sum_comp (Equiv.inv (Perm (Fin 4))) (fun p => ∑ b, ∑ t, g p b t)
  change (∑ p : Perm (Fin 4), ∑ b, ∑ t, g p.symm b t) = _ at inv
  rw [inv]
  conv_lhs =>
    enter [2,b]
    rw [Finset.sum_comm]
  exact Finset.sum_comm

end
end BlockPermanents.FourWireCut
