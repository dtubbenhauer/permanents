import BlockPermanents.OnePort
import BlockPermanents.RoutedClasp
import Mathlib.Logic.Equiv.Prod

/-! # Averaging the return of the last marked strand within its original cable -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℂ) : ℂ :=
  (∑ a,f a)/(Fintype.card A : ℂ)

private theorem mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℂ) :
    mean (fun a => f (e a)) = mean f := by
  simp [mean,Equiv.sum_comp e f,Fintype.card_congr e]

private theorem mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℂ) :
    mean (fun _ : A => c)=c := by
  simp [mean,nsmul_eq_mul,Fintype.card_ne_zero]

private theorem mean_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (f : A → ℂ) :
    mean (fun x : A×B => f x.1) = mean f := by
  simp only [mean,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.mul_sum,Fintype.card_prod,Nat.cast_mul]
  have hb : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_comm (Fintype.card A : ℂ),mul_div_mul_left _ _ hb]

private theorem mean_coord {H : Type*} [Fintype H] [DecidableEq H]
    (K : H → Type*) [∀ i,Fintype (K i)] [∀ i,Nonempty (K i)] (i : H) (f : K i → ℂ) :
    mean (fun p : (i : H) → K i => f (p i))=mean f := by
  let e := Equiv.piSplitAt i K
  exact (mean_equiv e (fun x => f x.1)).trans (mean_fst f)

private theorem eval_perm (n : ℕ) (x : Fin (n+1)) (f : Fin (n+1) → ℂ) :
    mean (fun p : Perm (Fin (n+1)) => f (p x)) = mean f := by
  have e := mean_equiv (Equiv.mulRight (Equiv.swap 0 x)) (fun p : Perm (Fin (n+1)) => f (p 0))
  have h : mean (fun p : Perm (Fin (n+1)) => f (p x)) =
      mean (fun p : Perm (Fin (n+1)) => f (p 0)) := by
    change mean (fun p : Perm (Fin (n+1)) => f (p ((Equiv.swap 0 x) 0))) = _ at e
    simpa only [Equiv.swap_apply_left] using e
  rw [h]
  unfold mean
  rw [Finset.univ_perm_fin_succ,← Finset.univ_product_univ]
  simp only [Finset.sum_map,Equiv.toEmbedding_apply,Finset.sum_product,
    Equiv.Perm.decomposeFin_symm_apply_zero,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul,← Finset.mul_sum,Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [mul_comm (n+1 : ℂ),mul_div_mul_left _ _ hf]

variable {H : Type*} [Fintype H] [DecidableEq H]
abbrev Positive (d : H → ℕ) := (Σ i,Fin (d i+1))
abbrev Inside (d : H → ℕ) := (i : H) → Perm (Fin (d i+1))

/-- All opens of the positive clasps. The base layout simply gives common
coordinates to the input. Each output reads the chosen last slot as none. -/
def lastWiring {N} {d : H → ℕ} (base L : Positive d ≃ Option (Fin (N+1)))
    (g : Inside d) :=
  base.symm.trans ((Equiv.sigmaCongrRight g).trans L)

private theorem returned {N} {d : H → ℕ} (base : Positive d ≃ Option (Fin (N+1)))
    (L : H → Positive d ≃ Option (Fin (N+1))) (hl : ∀ i,L i ⟨i,0⟩=none)
    (i j : H) (g h : Inside d) :
    (lastWiring base (L i) g) ((lastWiring base (L j) h).symm none)=none ↔
      (⟨j,g j ((h j).symm 0)⟩ : Positive d)=⟨i,0⟩ := by
  have hj : (L j).symm none = ⟨j,0⟩ := (L j).symm_apply_eq.mpr (hl j).symm
  have e : (lastWiring base (L i) g) ((lastWiring base (L j) h).symm none) =
      L i ⟨j,g j ((h j).symm 0)⟩ := by simp [lastWiring,hj]
  rw [e,← hl i,(L i).injective.eq_iff]

set_option maxHeartbeats 1200000 in
/-- Slot-return law on the actual independent positive-cable permutations.
This calculation includes two distinct compatible internal orderings in
the lower and upper halves. -/
theorem return_mean {N} {d : H → ℕ} (base : Positive d ≃ Option (Fin (N+1)))
    (L : H → Positive d ≃ Option (Fin (N+1))) (hl : ∀ i,L i ⟨i,0⟩=none)
    (i j : H) (s ρ : ℂ) :
    mean (fun h : Inside d => mean (fun g : Inside d =>
      if (lastWiring base (L i) g) ((lastWiring base (L j) h).symm none)=none then s else ρ)) =
      ρ + (if i=j then s-ρ else 0)/(d i+1 : ℂ) := by
  simp_rw [returned base L hl]
  by_cases hij : i=j
  · subst j
    simp only [if_true,Sigma.mk.inj_iff,heq_eq_eq,true_and]
    have e (h : Inside d) : mean (fun g : Perm (Fin (d i+1)) =>
        if g ((h i).symm 0)=0 then s else ρ) = mean (fun x : Fin (d i+1) =>
          if x=0 then s else ρ) := eval_perm (d i) ((h i).symm 0) (fun x => if x=0 then s else ρ)
    have inner (h : Inside d) : mean (fun g : Inside d =>
        if g i ((h i).symm 0)=0 then s else ρ) = mean (fun x : Fin (d i+1) =>
          if x=0 then s else ρ) :=
      (mean_coord (fun i => Perm (Fin (d i+1))) i
        (fun a => if a ((h i).symm 0)=0 then s else ρ)).trans (e h)
    simp_rw [inner,mean_const]
    unfold mean
    simp [Fin.sum_univ_succ,nsmul_eq_mul]
    field_simp [show (d i : ℂ)+1≠0 by exact_mod_cast (Nat.succ_ne_zero (d i))]
    ring
  · have ne (a : Fin (d j+1)) : (⟨j,a⟩ : Positive d)≠⟨i,0⟩ :=
      fun e => hij (congrArg Sigma.fst e).symm
    simp only [ne,if_false,hij,mean_const,zero_div,add_zero]

end
end BlockPermanents.RoutedTrace
