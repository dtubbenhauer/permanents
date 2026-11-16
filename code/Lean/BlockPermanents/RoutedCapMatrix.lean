import BlockPermanents.RoutedClasp
import BlockPermanents.RoutedAdjoint

/-! Matrices of actual averaged caps and their reflected cups on all words. -/
namespace BlockPermanents.RoutedCapMatrix
open RoutedTrace Equiv
open scoped Matrix
noncomputable section
variable {d N : ℕ} {α : Type*} [Fintype α]

def A (S : Finset (Fin d)) (r : ℕ) (p : α → Perm (Cable (Fin N) r)) (a : α → ℚ) :
    Matrix (Bend.Word d N) ((Cable (Fin N) r → Fin d) × Mark S r) ℂ :=
  fun w v => ∑ i, (a i : ℂ) * capMatrix S r (p i) w v

private theorem eval_cap (S : Finset (Fin d)) (r : ℕ) (p : Perm (Cable (Fin N) r))
    (x : ((Cable (Fin N) r → Fin d) × Mark S r) → ℂ) (w : Bend.Word d N) :
    (capMatrix S r p).mulVec x w = routedCap S r p (fun v c => x (v,c)) w := by
  classical
  rw [routedCap,contract_apply]
  change (∑ v, capMatrix S r p w v * x v) = _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [capMatrix,ite_mul,Finset.sum_ite_eq]

theorem apply_cap (S : Finset (Fin d)) (r : ℕ) (p : α → Perm (Cable (Fin N) r)) (a : α → ℚ)
    (x : ((Cable (Fin N) r → Fin d) × Mark S r) → ℂ) :
    (A S r p a).mulVec x = capAverage S r p a (fun v c => x (v,c)) := by
  funext w
  unfold Matrix.mulVec dotProduct A capAverage
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => congrArg ((a i : ℂ) * ·) (eval_cap S r (p i) x w)

private theorem reflect_expand (S : Finset (Fin d)) (r : ℕ) (f : Bend.Word d N → ℂ)
    (v : Cable (Fin N) r → Fin d) (c : Mark S r) :
    (∑ w, reflect S r (fun u => if u=w then 1 else 0) v c * f w) = reflect S r f v c := by
  classical
  induction r with
  | zero => simp [reflect,ite_mul]
  | succ r ih =>
    change (∑ w, (if v none = c.2.val then reflect S r (fun u => if u=w then 1 else 0) (v ∘ some) c.1 else 0) * f w) =
      (if v none = c.2.val then reflect S r f (v ∘ some) c.1 else 0)
    by_cases h : v none = c.2.val <;> simp [h, ih]

theorem apply_reflect (S : Finset (Fin d)) (r : ℕ) (p : α → Perm (Cable (Fin N) r)) (a : α → ℚ)
    (f : Bend.Word d N → ℂ) :
    (A S r p a)ᴴ.mulVec f = fun v => reflectedAverage S r p a f v.1 v.2 := by
  funext ⟨v,c⟩
  change (∑ w, star (∑ i, (a i : ℂ) * capMatrix S r (p i) w (v,c)) * f w) = _
  simp only [star_sum,star_mul',star_ratCast,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg ((a i : ℂ) * ·)
  change (∑ w, (capMatrix S r (p i))ᴴ (v,c) w * f w) = _
  simp_rw [reflect_adjoint]
  exact reflect_expand S r f _ c

end
end BlockPermanents.RoutedCapMatrix
