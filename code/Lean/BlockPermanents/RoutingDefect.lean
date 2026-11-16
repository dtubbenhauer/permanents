import BlockPermanents.RoutingOperators

/-! # Whole routing tables and the packet-class subtraction -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {m k : ℕ}

def packetHom (m k : ℕ) : Perm (Fin m) →* Wire m k where
  toFun p := p.prodCongr (Equiv.refl _)
  map_one' := rfl
  map_mul' _ _ := rfl

def packetTable (p : Perm (Fin m)) (k : ℕ) := table (packetHom m k p)

theorem packet_entry (p : Perm (Fin m)) (i j : Fin m) :
    (packetTable p k).entries i j = if p i=j then k else 0 := by
  change Fintype.card {t : Fin k // p i=j} = _
  split_ifs with h <;> simp [h]

private theorem split_zero_iff (M : Routing m k) :
    M.splitInputs.card=0 ↔ ∀ i, ∃ j, M.entries i j=k := by
  rw [Finset.card_eq_zero]
  constructor
  · intro h i
    by_contra! hn
    have hi : i ∈ M.splitInputs := by
      simp only [Routing.splitInputs,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_image]
      rintro ⟨⟨i',j⟩,hij,rfl⟩
      exact hn j (Finset.mem_filter.mp hij).2
    simp [h] at hi
  · intro h;apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    obtain ⟨j,hj⟩ := h i
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_image.mpr
      ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩)

private theorem packet_nosplit (p : Perm (Fin m)) : (packetTable p k).splitInputs.card = 0 :=
  (split_zero_iff _).mpr fun i => ⟨p i,by simp [packet_entry]⟩

private theorem other_zero (M : Routing m k) (i j l : Fin m) (hj : M.entries i j = k) (hl : j≠l) :
    M.entries i l = 0 := by
  have he := Finset.sum_erase_add Finset.univ (M.entries i) (Finset.mem_univ j)
  rw [M.rowSum,hj] at he
  have h0 : ∑ a ∈ Finset.univ.erase j, M.entries i a = 0 := by omega
  exact Finset.sum_eq_zero_iff_of_nonneg (f:=M.entries i) (fun _ _ => Nat.zero_le _) |>.mp h0 l
    (Finset.mem_erase.mpr ⟨hl.symm,Finset.mem_univ _⟩)

/-- A table with no split input is uniquely a packet permutation. -/
def unsplitEquiv (m k : ℕ) (hk : 0<k) :
    Perm (Fin m) ≃ {M : Routing m k // M.splitInputs.card = 0} := by
  let f := fun p : Perm (Fin m) => (⟨packetTable p k,packet_nosplit p⟩ :
    {M : Routing m k // M.splitInputs.card = 0})
  apply Equiv.ofBijective f
  constructor
  · intro p q h;apply Equiv.ext;intro i
    have he := congrArg (fun M : {M : Routing m k // M.splitInputs.card = 0} => M.val.entries i (p i)) h
    change (packetTable p k).entries i (p i) = (packetTable q k).entries i (p i) at he
    simp only [packet_entry,if_pos rfl] at he
    by_contra hh; simp [Ne.symm hh] at he;omega
  · rintro ⟨M,hM⟩
    choose l hl using (split_zero_iff M).mp hM
    have hli : Function.Injective l := by
      intro i j he
      have hi : (i,l i) ∈ M.whole := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl i⟩
      have hj : (j,l j) ∈ M.whole := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl j⟩
      exact congrArg Prod.fst (M.whole_outputs_injective hk hi hj he)
    let p := Equiv.ofBijective l ⟨hli,Finite.injective_iff_surjective.mp hli⟩
    refine ⟨p,Subtype.ext (table_ext fun i j => ?_)⟩
    change (packetTable p k).entries i j = _
    rw [packet_entry]
    change (if l i=j then k else 0)=_
    split_ifs with hij
    · rw [← hij,hl]
    · exact (other_zero _ _ _ _ (hl i) hij).symm

theorem packet_weight (p : Perm (Fin m)) : weight (packetTable p k) = 1 := by
  have hr (i : Fin m) : (∏ j, (((packetTable p k).entries i j).factorial : ℚ)) = k.factorial := by
    rw [Finset.prod_eq_single (p i)] <;> simp_all [packet_entry,Ne.symm]
  unfold weight
  simp [hr, Nat.factorial_ne_zero]

variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem packet_expand (ρ : Wire m k →* R) (hk : 0<k) :
    (m.factorial:ℚ) • (internal ρ * Transfer.clasp (ρ.comp (packetHom m k)) * internal ρ) =
      ∑ M : Routing m k, (if M.splitInputs.card=0 then weight M else 0) • routingOp ρ M := by
  classical
  have h : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [Transfer.clasp,Fintype.card_perm,Fintype.card_fin,mul_smul_comm,smul_mul_assoc,
    smul_smul, mul_inv_cancel₀ h,one_smul,Finset.mul_sum,Finset.sum_mul,MonoidHom.comp_apply]
  change (∑ p : Perm (Fin m), compressed ρ (packetHom m k p))=_
  rw [← Fintype.sum_subtype_add_sum_subtype (fun M : Routing m k => M.splitInputs.card=0)
    (fun M => (if M.splitInputs.card=0 then weight M else 0) • routingOp ρ M)]
  have pos (v : {M : Routing m k // M.splitInputs.card=0}) : (if v.val.splitInputs.card=0 then weight v.val else 0) = weight v.val := if_pos v.property
  have neg (v : {M : Routing m k // ¬M.splitInputs.card=0}) : (if v.val.splitInputs.card=0 then weight v.val else 0) = 0 := if_neg v.property
  simp only [pos,neg,zero_smul,Finset.sum_const_zero,add_zero]
  rw [← Equiv.sum_comp (unsplitEquiv m k hk)]
  apply Finset.sum_congr rfl
  intro p _
  change compressed ρ (packetHom m k p) = weight (packetTable p k) • routingOp ρ (table (packetHom m k p))
  rw [packet_weight,one_smul,routingOp_table]

/-- The coarse packet clasp removes exactly the whole thin-routing tables
from the permanent-normalized fine clasp. -/
theorem defect_expand (ρ : Wire m k →* R) (hk : 0<k) :
    (((m*k).factorial : ℚ)/(k.factorial:ℚ)^m) • (internal ρ * Transfer.clasp ρ * internal ρ) -
      (m.factorial:ℚ) • (internal ρ * Transfer.clasp (ρ.comp (packetHom m k)) * internal ρ) =
      ∑ M : Routing m k, (if M.splitInputs.card=0 then 0 else weight M) • routingOp ρ M := by
  rw [fine_expand,packet_expand _ hk,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro M _
  split_ifs <;> simp

end
end BlockPermanents.RoutingFibres
