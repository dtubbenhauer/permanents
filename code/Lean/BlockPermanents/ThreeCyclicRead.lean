import BlockPermanents.ThreeOrbitGap
import BlockPermanents.ThreeGram

/-! The two orders of the ordinary packets give the same marked closure,
so the six-term simultaneous average is the displayed cyclic average. -/
namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen ThreeTransfer TransferBlocks Equiv
open scoped Matrix BigOperators
noncomputable section

theorem front_absorption (d k : ℕ) :
    swapFront d k * original d k * swapFront d k = original d k := by
  let A := allFine d k
  let p := firstFine d k
  let u := swapFront d k
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  have pa : p*A=A := by
    have h : (allFine d k)ᴴ=allFine d k := by ext i j;exact column_star _ _
    simpa only [Matrix.conjTranspose_mul,fine_star,h] using congrArg Matrix.conjTranspose (all_first d k)
  have up : u*p=p := first_front d k
  have pu : p*u=p := by simpa only [Matrix.conjTranspose_mul,front_star,fine_star] using congrArg Matrix.conjTranspose (first_front d k)
  have ua : u*A=A := by calc
    _ = u*(p*A) := by rw [pa]
    _ = _ := by rw [← mul_assoc,up,pa]
  have au : A*u=A := by calc
    _ = (A*p)*u := by rw [show A*p=A from all_first d k]
    _ = _ := by rw [mul_assoc,pu];exact all_first d k
  let f := pair u
  let F := triple u t
  have uf : u*f=f := pair_left u (front_sq d k)
  have fu : f*u=f := pair_right u (front_sq d k)
  have uF : u*F=F := triple_left u t (front_sq d k)
  have Fu : F*u=F := triple_right u t (front_sq d k)
  let a : ℂ := (k+k).choose k
  let b : ℂ := (k+k+k).choose (k+k)
  let q := secondFine d k
  let g := pair t
  change u*(a • (b • A) - (6:ℚ) • F + a • ((2:ℂ) • (f*q*f)-p*g*f-f*g*p))*u=_
  simp only [mul_add,mul_sub,mul_smul_comm,← mul_assoc u,uf,up,ua,uF]
  simp only [add_mul,sub_mul,smul_mul_assoc,mul_assoc,fu,pu,au,Fu]
  simp only [original,a,b,A,F,f,p,g,q,u,t,mul_assoc]

theorem front_value {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :
    quadratic (original d k) (data (x ∘ firstSwap)) = quadratic (original d k) (data x) := by
  have h := conjugate_eval firstSwap (original d k) (data x)
  simp only [data_reorder,show firstSwap⁻¹=firstSwap by decide,front,front_absorption] at h
  exact h.symm

private theorem cyclic_of_pair (q : G→ℂ) (h : ∀ p, q (p*firstSwap)=q p) :
    ∑ p : G, q p = 2*(q 1 + q (firstSwap*lastSwap) + q (lastSwap*firstSwap)) := by
  have hu : q firstSwap=q 1 := by simpa only [one_mul] using h 1
  rw [six q]
  linear_combination hu - h lastSwap + h (firstSwap*lastSwap)

def markedValue {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :=
  quadratic (original d k) (data x)

theorem cyclic_sum {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :
    ∑ p : G, markedValue (x ∘ p) = 2*(markedValue (x ∘ (1:G)) +
      markedValue (x ∘ (firstSwap*lastSwap : G)) + markedValue (x ∘ (lastSwap*firstSwap : G))) := by
  let q (p:G) := markedValue (x ∘ p)
  have he (p:G) : q (p*firstSwap) = q p := by
    exact (congrArg (@markedValue d k) (show x ∘ (p*firstSwap : G) = (x ∘ p) ∘ firstSwap from rfl)).trans
      (front_value (x ∘ p))
  exact cyclic_of_pair q he

/-- The three cyclic markings have average equal to the original matrix gap. -/
theorem cyclic_gap {d k : ℕ} (x : Fin 3→Fin k→Fin d→ℂ) :
    gap x = (markedValue (x ∘ (1:G)) + markedValue (x ∘ (firstSwap*lastSwap : G)) +
      markedValue (x ∘ (lastSwap*firstSwap : G)))/3 := by
  have h := sum_original x
  change (∑ p : G, markedValue (x ∘ p)) = _ at h
  rw [cyclic_sum] at h
  have vv (p : G) : quadratic (target d k) (data (x ∘ p)) = gap x :=
    (ThreeGram.target_gap (x ∘ p)).trans (gap_permute x p)
  simp only [vv,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    show (3:ℕ).factorial=6 by decide,nsmul_eq_mul,Nat.cast_ofNat] at h
  linear_combination -(1/6:ℂ) * h

end
end BlockPermanents.ThreeMarkedAverage
