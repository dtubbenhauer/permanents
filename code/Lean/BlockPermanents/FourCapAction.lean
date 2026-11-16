import BlockPermanents.FourRoutes
import BlockPermanents.ThreeSupport

/-! # Coefficients of the marked four-packet halves

The horizontal packet average is taken before the indicated fine merge.
Slicing at the spectators below is a bijective change of word coordinates.
-/
namespace BlockPermanents.FourCapAction
open Bend Closures FourRoutes
open scoped BigOperators Matrix
noncomputable section

def blocks (n : ℕ) (hn : n ≤ 3) : Fin (3-n) ⊕ Fin n ≃ Fin 3 :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hn))

def split {d k n : ℕ} (hn : n ≤ 3) (σ : Equiv.Perm (Fin 3)) :
    Triple d k ≃ Spectator d k n × Word d (n*k) where
  toFun x := (fun i => x (σ (blocks n hn (.inl i))),
    fun t => let ij := finProdFinEquiv.symm t
             x (σ (blocks n hn (.inr ij.1))) ij.2)
  invFun u i := (blocks n hn |>.symm (σ.symm i)).elim u.1
    (fun j t => u.2 (finProdFinEquiv (j,t)))
  left_inv x := by
    funext i
    obtain ⟨v,h⟩ := (blocks n hn).surjective (σ.symm i)
    have hi : σ ((blocks n hn) v) = i := by rw [h,σ.apply_symm_apply]
    subst i
    cases v <;> simp
  right_inv := by
    rintro ⟨s,w⟩
    apply Prod.ext <;> funext i <;> simp
    exact congrArg w (finProdFinEquiv.apply_symm_apply i)

def averaged {d k n : ℕ} (hn : n ≤ 3) (F : Triple d k → ℂ)
    (s : Spectator d k n) (v : Word d (n*k)) : ℂ :=
  6⁻¹ * ∑ σ : Equiv.Perm (Fin 3), F ((split hn σ).symm (s,v))

theorem merge_action {d k n : ℕ} (hn : n ≤ 3) (F : Triple d k → ℂ)
    (s : Spectator d k n) :
    (merge d k n hn s).mulVec F = clasp (averaged hn F s) := by
  classical
  rw [← Bridges.symClasp_action]
  funext w
  simp only [Matrix.mulVec,dotProduct,merge,averaged,mul_assoc,Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have step (σ : Equiv.Perm (Fin 3)) :
      (∑ x : Triple d k, (if ((split hn σ x).1 = s) then
        symClasp d (n*k) w (split hn σ x).2 else 0) * F x) =
      ∑ v, symClasp d (n*k) w v * F ((split hn σ).symm (s,v)) := by
    rw [← (split hn σ).symm.sum_comp (fun x => (if (split hn σ x).1 = s then
        symClasp d (n*k) w (split hn σ x).2 else 0) * F x)]
    simp [Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]
  change (6:ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin 3), (∑ x : Triple d k,
    (if ((split hn σ x).1 = s) then symClasp d (n*k) w (split hn σ x).2 else 0) * F x) = _
  simp_rw [step]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum]; ring

theorem upright_product {A B K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (M : Matrix B A ℂ) (F : A → ℂ) (H : K → ℂ) :
    (ThreeTransfer.upright M).mulVec (product F H) = product (M.mulVec F) H := by
  classical
  funext i
  simp [ThreeTransfer.upright,product,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    ite_mul,← mul_assoc,Finset.sum_mul]

theorem merge_symmetric {d k n : ℕ} (hn : n ≤ 3) (F : Triple d k → ℂ) (s : Spectator d k n) :
    Symmetric ((merge d k n hn s).mulVec F) := by
  rw [merge_action,← Bridges.symClasp_action]
  exact PairBound.projected_symmetric _ _ _

/-- Acting with the concrete r-cap amounts to a trace on r letters of
the merged upright coefficient and the marked coefficient. -/
theorem capHalf_entry {d k n : ℕ} (hn : n ≤ 3) (F : Triple d k → ℂ)
    (H : Word d k → ℂ) (hH : Symmetric H) (r : CutIndex (n*k) k) (s : Spectator d k n)
    (a : Word d (n*k-r)) (b : Word d (k-r)) :
    (capHalf d k n hn r s).mulVec (product F (fun v => star (H v))) (a,b) =
      ∑ t : Word d r,
        clasp (averaged hn F s) (fun i => Fin.append a t (Fin.cast
          (Nat.sub_add_cancel (le_trans (Nat.le_of_lt_succ r.isLt) (min_le_left _ _))).symm i)) *
        star (H (fun i => Fin.append b t (Fin.cast
          (Nat.sub_add_cancel (le_trans (Nat.le_of_lt_succ r.isLt) (min_le_right _ _))).symm i))) := by
  rw [capHalf, route, ← Matrix.mulVec_mulVec,upright_product,wordCap,cap_product]
  apply Finset.sum_congr rfl
  intro t _
  rw [split_symmetric _ (merge_symmetric hn F s),split_symmetric _ hH,merge_action]

end
end BlockPermanents.FourCapAction
