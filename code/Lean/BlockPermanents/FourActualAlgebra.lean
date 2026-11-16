import BlockPermanents.FourWireAlgebra
import BlockPermanents.FourTarget

namespace BlockPermanents.FourActualAlgebra
open FourTarget FourWireAlgebra TransferBlocks
open scoped BigOperators
noncomputable section

private theorem absorb_average {R H : Type*} [Ring R] [Algebra ℚ R] [Group H] [Fintype H]
    (π : H →* R) (E : R) (hL : ∀ h, π h*E=E) (hR : ∀ h, E*π h=E) :
    Transfer.clasp π * E=E ∧ E * Transfer.clasp π=E := by
  have hc : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · simp only [Transfer.clasp,smul_mul_assoc,Finset.sum_mul,hL,Finset.sum_const,Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]
  · simp only [Transfer.clasp,mul_smul_comm,Finset.mul_sum,hR,Finset.sum_const,Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]

private theorem swap_spectator_commutes {k : ℕ} (p : group k 2) :
    wires k swap34 * (p : Wire k) = (p : Wire k) * wires k swap34 := by
  ext x : 1
  change wires k swap34 (p.val x) = p.val (wires k swap34 x)
  by_cases hx : x.1.val < 2
  · have hp : (p.val x).1.val < 2 := by
      by_contra! he
      have h : p.val x=x := p.val.injective (p.property (p.val x) he)
      rw [h] at he
      omega
    have fix (z : Slot k) (hz : z.1.val < 2) : wires k swap34 z=z := by
      rcases z with ⟨i,j⟩
      change (Equiv.swap (2:Fin 4) 3 i,j)=(i,j)
      rw [Equiv.swap_apply_of_ne_of_ne (by intro h; subst i; norm_num at hz)
        (by intro h; subst i; exact (by decide : ¬ (3:Fin 4).val < 2) hz)]
    rw [fix _ hp,fix _ hx]
  · have hx' : 2 ≤ x.1.val := Nat.le_of_not_gt hx
    have hq : 2 ≤ (wires k swap34 x).1.val := by
      rcases x with ⟨i,j⟩
      change 2 ≤ (Equiv.swap (2:Fin 4) 3 i).val
      change 2 ≤ i.val at hx'
      fin_cases i <;> first | contradiction | decide
    rw [p.property x hx',p.property _ hq]

/-- All the projector and support hypotheses of the four-packet calculation
hold for the concrete averages over the first four and first six thin slots. -/
theorem fine_clasps (d k : ℕ) : FineClasps (packets d k) (localClasp d k 2) (localClasp d k 3) := by
  letI (j : ℕ) : Fintype (group k j) := Fintype.ofFinite _
  let π := (act d k).comp (group k 2).subtype
  let τ := (act d k).comp (group k 3).subtype
  let E := localClasp d k 3
  let w := packets d k swap34
  have sub (p : group k 2) : p.val ∈ group k 3 := fun i hi => p.property i (by omega)
  have a (p : group k 2) : π p * E=E :=
    Transfer.absorb_left τ (⟨p.val,sub p⟩ : group k 3)
  have b (p : group k 2) : E * π p=E :=
    Transfer.absorb_right τ (⟨p.val,sub p⟩ : group k 3)
  have ⟨pe,ep⟩ := absorb_average π E a b
  have ⟨up,pu⟩ := local_absorption d k 2 swap12 (first_two k 2 le_rfl)
  have ⟨ue,eu⟩ := local_absorption d k 3 swap12 (first_two k 3 (by decide))
  have ⟨ve,ev⟩ := local_absorption d k 3 swap23 (next_two k)
  have cp (p : group k 2) : w*π p=π p*w := by
    change act d k (wires k swap34) * act d k p.val = act d k p.val * act d k (wires k swap34)
    rw [←map_mul,←map_mul,swap_spectator_commutes]
  have move : w*Transfer.clasp π=Transfer.clasp π*w := by
    simp only [Transfer.clasp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,cp]
  have ss : w*w=1 := by
    change packets d k swap34*packets d k swap34=1
    rw [←map_mul,show swap34*swap34=1 by decide,map_one]
  refine ⟨Transfer.clasp_sq π,up,pu,?_,pe,ep,ue,eu,ve,ev⟩
  change w*Transfer.clasp π*w=Transfer.clasp π
  rw [move,mul_assoc,ss,mul_one]

/-- The original named Q on the exact same slot indexing as the PSD
matrix, opened into its seven fixed-mark four-quadratic terms. -/
theorem actual_open {M : Type*} [AddCommGroup M] [Module ℚ M] (d : ℕ)
    (φ : Op d 2 →ₗ[ℚ] M) (e : Op d 2)
    (h : Openings φ (packets d 2) (localClasp d 2 2) (localClasp d 2 3) (fineClasp d 2) e) :
    φ (Q d 2) = φ (raw (ordinary (packets d 2)) (localClasp d 2 3) (localClasp d 2 2)
      (movedPair (packets d 2) (localClasp d 2 2)) e (packets d 2 swap14)) := by
  have h' := four_quadratic_open φ (packets d 2) _ _ _ e (fine_clasps d 2) h
  simpa only [Q,X₃,X₄,ordinary,show (2+2).choose 2=6 by decide,
    show (((4*2).factorial : ℚ) / (2:ℕ).factorial^4)=2520 by norm_num [Nat.factorial],
    show (((3*2).factorial : ℚ) / (2:ℕ).factorial^3)=90 by norm_num [Nat.factorial],
    Nat.cast_ofNat] using h'

end
end BlockPermanents.FourActualAlgebra
