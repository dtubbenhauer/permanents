import BlockPermanents.OccupationSplit
import Mathlib.Data.Fintype.Perm

/-! The occupation basis for any number of colours. A clasp sends a word
to the uniform vector on its orbit, of squared norm equal to the printed
product of occupation factorials divided by the word length factorial. -/
namespace BlockPermanents.OccupationBasis
open OccupationSplit Bend
open scoped BigOperators
noncomputable section

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq D]
abbrev Fiber (x : I → D) (j : D) := {i // x i=j}

def occ (x : I → D) : D → ℕ := counts x Finset.univ

omit [Fintype D] in
theorem fiber_card (x : I → D) (j : D) : Fintype.card (Fiber x j) = occ x j := by
  simp [Fiber,Fintype.card_subtype,occ,counts]

private def restrictPerm {x y : I → D} (p : Equiv.Perm I) (h : x=y ∘ p) (j : D) :
    Fiber x j ≃ Fiber y j where
  toFun a := ⟨p a.val, h ▸ a.prop⟩
  invFun b := ⟨p.symm b.val, by rw [h];simpa using b.prop⟩
  left_inv a := Subtype.ext (p.symm_apply_apply a)
  right_inv b := Subtype.ext (p.apply_symm_apply b)

private def unitePerm {x y : I → D} (f : (j : D) → Fiber x j ≃ Fiber y j) : Equiv.Perm I :=
  ((Equiv.sigmaFiberEquiv x).symm.trans (Equiv.sigmaCongrRight f)).trans (Equiv.sigmaFiberEquiv y)

omit [Fintype I] [Fintype D] [DecidableEq D] in
private theorem unite_matches {x y : I → D} (f : (j : D) → Fiber x j ≃ Fiber y j) :
    x=y ∘ unitePerm f := by
  funext i
  exact ((f (x i) ⟨i,rfl⟩).prop).symm

private def permFiber (x y : I → D) :
    {p : Equiv.Perm I // x=y ∘ p} ≃ ((j : D) → Fiber x j ≃ Fiber y j) where
  toFun p j := restrictPerm p.val p.prop j
  invFun f := ⟨unitePerm f,unite_matches f⟩
  left_inv p := by apply Subtype.ext; ext i; rfl
  right_inv f := by
    funext j
    ext ⟨i,hi⟩ : 1
    subst j
    apply Subtype.ext
    rfl

def weight (n : D → ℕ) (length : ℕ) : ℚ :=
  (∏ j, ((n j).factorial : ℚ)) / length.factorial

variable [DecidableEq I]

theorem kernel_count (x y : I → D) :
    Fintype.card {p : Equiv.Perm I // x=y ∘ p} =
      if occ x=occ y then ∏ j,(occ x j).factorial else 0 := by
  classical
  rw [Fintype.card_congr (permFiber x y)]
  by_cases h : occ x=occ y
  · rw [if_pos h,Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro j _
    let e := Fintype.equivOfCardEq (by rw [fiber_card x j,fiber_card y j,h] :
      Fintype.card (Fiber x j)=Fintype.card (Fiber y j))
    rw [Fintype.card_equiv e,fiber_card]
  · rw [if_neg h,Fintype.card_eq_zero_iff]
    constructor
    intro f
    apply h
    funext j
    rw [← fiber_card,← fiber_card,Fintype.card_congr (f j)]

/-- Normalized kernel on an arbitrary finite set of slots. -/
def kernel (x y : I → D) : ℚ :=
  (Fintype.card {p : Equiv.Perm I // x=y ∘ p} : ℚ) / (Fintype.card I).factorial

theorem kernel_eq (x y : I → D) :
    kernel x y = if occ x=occ y then weight (occ x) (Fintype.card I) else 0 := by
  rw [kernel,kernel_count]
  split_ifs <;> simp [weight]

theorem kernel_word {d n : ℕ} (x y : Word d n) :
    (kernel x y : ℂ) = symClasp d n x y := by
  classical
  simp only [symClasp,Finset.sum_boole,kernel,Rat.cast_div,Rat.cast_natCast,Fintype.card_fin,
    Fintype.card_subtype,div_eq_mul_inv]
  simp only [Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,mul_comm]

/-- Orbit weights sum to one: every slot permutation gives exactly one word. -/
theorem column_sum (y : I → D) : ∑ x,kernel x y = 1 := by
  classical
  simp only [kernel,Fintype.card_subtype,← Finset.sum_boole,← Finset.sum_div]
  rw [Finset.sum_comm]
  simp [Fintype.card_perm,Nat.factorial_ne_zero]

omit [DecidableEq D] in
theorem weight_pos (a : D → ℕ) (n : ℕ) : 0 < weight a n := by
  exact div_pos (Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _)))
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- The squared norm of the orthogonal occupation vector. -/
theorem norm_sq (y : I → D) : ∑ x,(kernel x y)^2= weight (occ y) (Fintype.card I) := by
  have hi (x : I → D) : (kernel x y)^2=weight (occ y) (Fintype.card I)*kernel x y := by
    rw [kernel_eq];split_ifs with h <;> simp_all [pow_two]
  simp only [hi,← Finset.mul_sum,column_sum,mul_one]

end
end BlockPermanents.OccupationBasis
