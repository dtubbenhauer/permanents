import BlockPermanents.ThreeGeneralRaw

/-! # Absorption of smaller symmetrizers by the all-strand word clasp -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend Equiv
open scoped Matrix BigOperators
noncomputable section

def permJoin {p q : ℕ} (u : Perm (Fin p)) (v : Perm (Fin q)) : Perm (Fin (p+q)) :=
  finSumFinEquiv.symm.trans ((u.sumCongr v).trans finSumFinEquiv)

theorem append_permute {D : Type*} {p q : ℕ} (a : Fin p → D) (b : Fin q → D)
    (u : Perm (Fin p)) (v : Perm (Fin q)) :
    Fin.append (a ∘ u) (b ∘ v) = Fin.append a b ∘ permJoin u v := by
  funext i;obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i|i <;> simp [permJoin,Function.comp_apply,-Fin.natAdd_eq_addNat]

theorem symClasp_right_perm {d n : ℕ} (x y : K d n) (σ : Perm (Fin n)) :
    symClasp d n x (y ∘ σ) = symClasp d n x y := by
  unfold symClasp;congr 1
  exact (Group.mulLeft_bijective σ).sum_comp
    (fun p : Perm (Fin n) => if x=y ∘ p then (1:ℂ) else 0)

theorem avg_right {d n : ℕ} (f : K d n → ℂ) (i : K d n) :
    (∑ a, f a * symClasp d n a i) = ((n.factorial:ℂ)⁻¹) * ∑ σ : Perm (Fin n), f (i ∘ σ) := by
  simp only [symClasp,← mul_assoc,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro σ _
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _),mul_comm]

theorem avg_fixed {d n : ℕ} (f : K d n → ℂ) (w : K d n)
    (h : ∀ p : Perm (Fin n), f (w ∘ p) = f w) :
    (∑ i, f i * symClasp d n i w) = f w := by
  rw [avg_right]
  simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,
    ←mul_assoc,inv_mul_cancel₀ (show (n.factorial:ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),one_mul]

/-- A row symmetric in both sets of positions absorbs their two independent
normalized packet clasps, before any spectral or Schur hypothesis. -/
theorem absorb_rows {d p q : ℕ} {T : Type*} (A : Matrix T (K d p × K d q) ℂ)
    (h : ∀ i a b (u : Perm (Fin p)) (v : Perm (Fin q)), A i (a ∘ u,b ∘ v) = A i (a,b)) :
    A * legs (symClasp d p) (symClasp d q) = A := by
  ext i ⟨a,b⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,legs]
  have hh (x : K d p) (y : K d q) :
      A i (x,y) * (symClasp d p x a * symClasp d q y b) = (A i (x,y) * symClasp d q y b)*symClasp d p x a := by ring
  have hb (x : K d p) := avg_fixed (fun y => A i (x,y)) b (fun v => h i x b 1 v)
  simp_rw [hh,← Finset.sum_mul,hb]
  exact avg_fixed (fun x => A i (x,b)) a (fun u => h i a b u 1)

theorem total_absorbs (d p q : ℕ) :
    totalClasp d p q * legs (symClasp d p) (symClasp d q) = totalClasp d p q := by
  apply absorb_rows;intro i a b u v
  simp only [totalClasp,append_permute,symClasp_right_perm]

theorem column_star {d n : ℕ} (u v : Word d n) :
    star (symClasp d n u v) = symClasp d n v u := by
  classical
  simp only [symClasp,star_mul',star_inv₀,star_natCast,star_sum,apply_ite,star_one,star_zero]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n)))
  intro a
  congr 1
  change (u = v ∘ a) = (v = u ∘ a.symm)
  apply propext
  constructor <;> rintro rfl <;> funext j <;> simp

theorem total_absorbs_left (d p q : ℕ) :
    legs (symClasp d p) (symClasp d q) * totalClasp d p q = totalClasp d p q := by
  have h := congrArg Matrix.conjTranspose (total_absorbs d p q)
  have htotal : (totalClasp d p q)ᴴ = totalClasp d p q := by
    ext i j; exact column_star _ _
  have hlegs : (legs (symClasp d p) (symClasp d q))ᴴ = legs (symClasp d p) (symClasp d q) := by
    ext i j; simp only [Matrix.conjTranspose_apply,legs,star_mul',column_star]
  simpa only [Matrix.conjTranspose_mul,htotal,hlegs] using h

end
end BlockPermanents.ThreeGeneralOpen
