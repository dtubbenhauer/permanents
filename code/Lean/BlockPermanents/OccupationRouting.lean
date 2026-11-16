import BlockPermanents.OccupationSeam

/-! The same occupation matrix expressed in ordinary split, cap and merge
coordinates. The summation variables are the supported and surviving words
on the actual output and marked slots of the route. -/
namespace BlockPermanents.OccupationRouting
open OccupationBasis OccupationCoefficient OccupationSeam
open scoped BigOperators
noncomputable section

variable {H J Z : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Fintype Z] [DecidableEq Z] {d : ℕ} {n : H→ℕ}

private theorem positive_kernel (x : Atom n d) (f : Atom n d→ℚ) :
    (∑ p : (i:H)→Equiv.Perm (Fin (n i)),f (fun i => x i ∘ p i)) /
      ∏ i,((n i).factorial : ℚ) = ∑ y : Atom n d, f y * ∏ i,kernel (y i) (x i) := by
  have h := independent (fun i (p : Equiv.Perm (Fin (n i))) => x i ∘ p) f
  simp only [Fintype.card_perm,Fintype.card_fin] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [kernel,Finset.sum_boole,Fintype.card_subtype,Fintype.card_fin]
  have he : Finset.univ.filter (fun p : Equiv.Perm (Fin (n i)) => x i ∘ p=y i) =
      Finset.univ.filter (fun p : Equiv.Perm (Fin (n i)) => y i=x i ∘ p) := by ext p;simp [eq_comm]
  rw [he]

/-- Split the true thin word into the two groups of positions selected by
the routing. No permutation multiplicity arises in this reindexing. -/
def split (s : (i:H)→Finset (Fin (n i))) :
    Atom n d ≃ (Ports s→Fin d) × (Ports (survivors s)→Fin d) where
  toFun y := (read y s 1, read y (survivors s) 1)
  invFun z i a := if h : a∈s i then z.1 ⟨i,⟨a,h⟩⟩ else
    z.2 ⟨i,⟨a,Finset.mem_compl.mpr h⟩⟩
  left_inv y := by funext i a;by_cases h : a∈s i <;> simp [h,OccupationCoefficient.read]
  right_inv z := by
    apply Prod.ext
    · funext ⟨i,⟨a,ha⟩⟩
      simp [OccupationCoefficient.read,ha]
    · funext ⟨i,⟨a,ha⟩⟩
      change a ∈ (s i)ᶜ at ha
      simp [OccupationCoefficient.read,Finset.mem_compl.mp ha]

omit [Fintype J] [DecidableEq J] [Fintype Z] [DecidableEq Z] in
/-- Thin-coordinate expansion. Insert each marked word at its assigned cap
slot, multiply the positive occupation-vector entries, and clasp the
output word. -/
theorem operator_split (r : Route n J Z) (x : Atom n d) (b : J→Fin d) (o : Z→Fin d) :
    operator r o (x,b) =
      ∑ v : Ports r.slots → Fin d, ∑ u : Ports (survivors r.slots)→Fin d,
        kernel (b ∘ r.marked) v * kernel (o ∘ r.output) u *
          ∏ i,kernel ((split r.slots).symm (v,u) i) (x i) := by
  let f (y : Atom n d) := kernel (b ∘ r.marked) ((split r.slots y).1) *
    kernel (o ∘ r.output) ((split r.slots y).2)
  change ((∑ p : (i:H)→Equiv.Perm (Fin (n i)),f (fun i=>x i ∘ p i)) /
    ∏ i,((n i).factorial : ℚ))=_
  rw [positive_kernel]
  let g (v : (Ports r.slots→Fin d) × (Ports (survivors r.slots)→Fin d)) :=
    kernel (b ∘ r.marked) v.1 * kernel (o ∘ r.output) v.2 *
      ∏ i,kernel ((split r.slots).symm v i) (x i)
  have h := (split r.slots).sum_comp g
  rw [Fintype.sum_prod_type] at h
  simpa only [g,Equiv.symm_apply_apply,f] using h
def complexOperator (S : Finset (Fin d)) (r : Route n J Z) :
    Matrix (Z→Fin d) (Atom n d × (J→Fin d)) ℂ := (supportedOperator S r).map (Rat.castHom ℂ)

omit [Fintype Z] [DecidableEq Z] in
theorem complex_gluing (S : Finset (Fin d)) (r t : Route n J Z) :
    complexOperator S r * (complexOperator S t).conjTranspose =
      (glued S r t).map (Rat.castHom ℂ) := by
  ext i j
  simp [complexOperator,glued,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.transpose_apply,Matrix.map_apply,Rat.cast_sum]

/-- The coefficients of the word operators are real rationals. This gives the same
occupation formula for the actual conjugate-transpose Gram matrix over ℂ. -/
theorem complex_seam (S : Finset (Fin d)) (r t : Route n J Z) (o : Z→Fin d) :
    (∑ u,∑ v,(kernel u o : ℂ) *
        (complexOperator S r * (complexOperator S t).conjTranspose) u v * (kernel v o : ℂ)) /
      (weight (occ o) (Fintype.card Z) : ℂ) =
    ((weight (occ o) (Fintype.card Z) *
      ∑ a : Data n d, ∑ b : Class J (Fin d),
        (if allowed S b.val ∧ balances a b o then value r a b * value t a b else 0) /
        (weight b.val (Fintype.card J)*∏ i,weight (a i).val (n i)) : ℚ) : ℂ) := by
  rw [complex_gluing,← supported_gram]
  simp [tested,Matrix.map_apply,Rat.cast_sum]

end
end BlockPermanents.OccupationRouting
