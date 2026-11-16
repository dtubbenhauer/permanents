import BlockPermanents.Routings
import BlockPermanents.Transfer
import Mathlib.GroupTheory.Perm.Fin

/-! # Independent packet-clasp averages on the two spectator ends -/
namespace BlockPermanents.ExitAverage
open Equiv Finset
open scoped BigOperators
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℚ R]

def average {A : Type*} [Fintype A] (f : A → R) : R :=
  (Fintype.card A : ℚ)⁻¹ • ∑ i,f i

theorem avg_const {A : Type*} [Fintype A] [Nonempty A] (v : R) :
    average (fun _ : A => v) = v := by
  simp only [average,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) v

/-- A finite group clasp sends a fixed slot uniformly over all packets. -/
theorem orbit {I : Type*} [Fintype I] [DecidableEq I] (a : I) (f : I → R) :
    average (fun g : Perm I => f (g a))=average f := by
  letI : Nonempty I := ⟨a⟩
  have equ (b : I) : (∑ g : Perm I, f (g b)) = ∑ g : Perm I,f (g a) := by
    have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap a b)) (fun g : Perm I => f (g a))
    change (∑ g : Perm I,f (g ((Equiv.swap a b) a))) = _ at h
    simpa only [Equiv.swap_apply_left] using h
  have eqn : (Fintype.card I : ℚ) • (∑ g : Perm I,f (g a)) =
      (Fintype.card (Perm I) : ℚ) • ∑ i,f i := by
    calc
      _ = ∑ b : I, ∑ g : Perm I,f (g b) := by simp_rw [equ]; simp only [Finset.sum_const,Finset.card_univ,Nat.cast_smul_eq_nsmul]
      _ = ∑ g : Perm I,∑ b,f (g b) := Finset.sum_comm
      _ = _ := by simp only [Equiv.sum_comp,Finset.sum_const,Finset.card_univ,Nat.cast_smul_eq_nsmul]
  let c := (Fintype.card I : ℚ)
  let t := (Fintype.card (Perm I) : ℚ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht : t ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change c • _ = t • _ at eqn
  change t⁻¹ • _ = c⁻¹ • _
  calc
    _ = (c*t)⁻¹ • (c • (∑ g : Perm I,f (g a))) := by
          rw [smul_smul];congr 1; field_simp
    _ = _ := by rw [eqn,smul_smul];congr 1;field_simp;ring

theorem orbit_inv {I : Type*} [Fintype I] [DecidableEq I] (a : I) (f : I → R) :
    average (fun g : Perm I => f (g.symm a))=average f := by
  rw [← orbit a f]
  apply congrArg (_ • ·)
  exact Equiv.sum_comp (Equiv.inv (Perm I)) (fun g : Perm I => f (g a))

def keep (n : ℕ) : Perm (Fin n) →* Perm (Fin (n+1)) where
  toFun g := finSuccEquivLast.symm.permCongr (Transfer.liftPerm g)
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' g h := by ext x; simp [Equiv.permCongr_apply,Perm.mul_apply]

@[simp] theorem keep_cast {n} (g : Perm (Fin n)) (i : Fin n) :
    keep n g i.castSucc=(g i).castSucc := by
  change finSuccEquivLast.symm (Option.map g (finSuccEquivLast i.castSucc))=(g i).castSucc
  simp

@[simp] theorem keep_last {n} (g : Perm (Fin n)) :
    keep n g (Fin.last n) = Fin.last n := by
  change finSuccEquivLast.symm (Option.map g (finSuccEquivLast (Fin.last n))) = Fin.last n
  simp

@[simp] theorem keep_symm_cast {n} (g : Perm (Fin n)) (i : Fin n) :
    (keep n g).symm i.castSucc = (g.symm i).castSucc := by
  apply (keep n g).injective
  simp

@[simp] theorem keep_symm_last {n} (g : Perm (Fin n)) :
    (keep n g).symm (Fin.last n) = Fin.last n := by
  apply (keep n g).injective
  simp

theorem right {I : Type*} [Fintype I] [Group I] (π : I →* R) (x : R) :
    x*Transfer.clasp π=average (fun g => x*π g) := by
  simp [Transfer.clasp,average,mul_smul_comm,Finset.mul_sum]

theorem left {I : Type*} [Fintype I] [Group I] (π : I →* R) (x : R) :
    Transfer.clasp π*x=average (fun g => π g*x) := by
  simp [Transfer.clasp,average,smul_mul_assoc,Finset.sum_mul]

/-- The four signed weights of a prescribed whole edge, expanded into
stationary, moved, and two crossed packet families. -/
theorem weights {n : ℕ} (hn : 0<n) (X : Fin (n+1) → Fin (n+1) → R) :
    ∑ ij : Fin (n+1) × Fin (n+1),
      (Routings.Routing.exitWeight (Fin.last n) ij / n) • X ij.1 ij.2 =
    -X (Fin.last n) (Fin.last n) +
      (n:ℚ) • average (fun i : Fin n => average (fun j : Fin n => X i.castSucc j.castSucc)) -
      (((n:ℚ)-1)/2) • (average (fun j : Fin n => X (Fin.last n) j.castSucc) +
        average (fun i : Fin n => X i.castSucc (Fin.last n))) := by
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_castSucc (n:=n)]
  simp only [Routings.Routing.exitWeight,Fin.castSucc_ne_last,if_false,if_true,Nat.cast_succ,
    add_sub_cancel_right,Finset.sum_add_distrib,average,Fintype.card_fin,← Finset.smul_sum,
    neg_div,neg_smul,smul_add,smul_neg,smul_smul]
  have hc : (((n:ℚ)+1-2)/2)/n=((n:ℚ)-1)/2*(n:ℚ)⁻¹ := by ring
  simp [hc,hn',div_eq_mul_inv,mul_assoc,← Finset.smul_sum,smul_smul]
  match_scalars <;> field_simp [hn'] <;> ring

end
end BlockPermanents.ExitAverage
