import BlockPermanents.Bridges
import BlockPermanents.SchurNormalization
import BlockPermanents.ThreeFine

/-! # The straight cut for two groups of arbitrary sizes -/
namespace BlockPermanents.StraightCut
open Bend Closures Bridges SchurNormalization
open scoped BigOperators ComplexOrder
noncomputable section

private def firstCut (p q : ℕ) : CutIndex p q := ⟨0, Nat.zero_lt_succ _⟩

/-- The straight cut has squared norm equal to the product of the two
squared norms, also when the two cable sizes differ. -/
theorem straight_energy {d p q : ℕ} {F : Word d p → ℂ} {H : Word d q → ℂ}
    (hF : Symmetric F) (hH : Symmetric H) :
    energy ((wordCap d p q (firstCut p q)).mulVec (product F (fun j => star (H j)))) =
      energy F * energy H := by
  have he (a : Word d p) (b : Word d q) :
      (wordCap d p q (firstCut p q)).mulVec (product F (fun j => star (H j))) (a,b) =
        F a * star (H b) := by
    rw [wordCap, cap_product]
    simp only [firstCut, split_symmetric _ hF, split_symmetric _ hH]
    simp [Fin.append_right_nil _ _ rfl, Function.comp_def]
  unfold energy
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [he, Complex.normSq_mul]
  exact congrArg _ (Complex.normSq_conj (H b))

/-- Keeping the zero-cap term in the reflected Schur expansion for two
symmetric tensors gives the straight-cut bound. -/
theorem straight_bound {d p q : ℕ} (schur : HomogeneousSchur d p q)
    {F : Word d p → ℂ} {H : Word d q → ℂ} (hF : Symmetric F) (hH : Symmetric H) :
    energy F * energy H ≤ (((p+q).choose p : ℂ) * quadratic (totalClasp d p q) (product F H)).re := by
  rw [closed_bent_schur d p q (homogeneousSchur_implies_unbent _ _ _ schur), Complex.re_sum]
  let term (r : CutIndex p q) : ℝ := (weight p q r : ℝ) *
    energy ((wordCap d p q r).mulVec (product F (fun j => star (H j))))
  have hr (r : CutIndex p q) : (((weight p q r : ℂ) *
      (energy ((wordCap d p q r).mulVec (product F (fun j => star (H j)))) : ℂ))).re = term r := by
    simp [term, Complex.mul_re]
  simp_rw [hr]
  have hn (r : CutIndex p q) (_ : r ∈ Finset.univ) : 0 ≤ term r :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  have hz : term (firstCut p q) = energy F * energy H := by
    unfold term; rw [straight_energy hF hH]; simp [weight, firstCut]
  rw [← hz]
  exact Finset.single_le_sum hn (Finset.mem_univ _)

variable {I J D : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def paired (x : I → D → ℂ) (y : J → D → ℂ) (w : I ⊕ J → D) : ℂ :=
  packet x (w ∘ Sum.inl) * packet y (w ∘ Sum.inr)

private theorem paired_expansion (x : I → D → ℂ) (y : J → D → ℂ) :
    paired x y = fun w => (packetScale I * packetScale J) *
      ∑ a : Equiv.Perm I × Equiv.Perm J,
        pureWord (Sum.elim x y) (w ∘ (a.1.sumCongr a.2).symm) := by
  funext w
  simp_rw [pure_reindex]
  simp only [paired, packet, orderSum, Fintype.sum_prod_type, pure_reindex,
    Finset.sum_mul, Finset.mul_sum, pureWord, Fintype.prod_sum_type, Equiv.sumCongr_apply,
    Sum.map_inl, Sum.map_inr, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intros
  ring

def c (I : Type*) [Fintype I] := packetScale I * ((Fintype.card I).factorial : ℂ)

theorem absorb_pair (x : I → D → ℂ) (y : J → D → ℂ) :
    clasp (paired x y) = fun w => (c I * c J) * clasp (pureWord (Sum.elim x y)) w := by
  unfold clasp
  rw [paired_expansion, sumSlots_scale, sumSlots_sum]
  simp_rw [sumSlots_absorb]
  funext w
  simp [c, Fintype.card_prod, Fintype.card_perm, mul_assoc, mul_comm, mul_left_comm]

theorem c_sq (I : Type*) [Fintype I] :
    (starRingEnd ℂ) (c I) * c I = ((Fintype.card I).factorial : ℂ) := by
  simp only [c, map_mul, map_natCast]
  rw [show ∀ a b t : ℂ, a*t*(b*t) = a*b*t*t by intros; ring, scale_cancel, one_mul]

/-- Fine permanent after symmetrizing individually in two groups, whose
sizes and index types may be different. -/
private theorem paired_fine [Fintype D] (x : I → D → ℂ) (y : J → D → ℂ) :
    (((Fintype.card I + Fintype.card J).choose (Fintype.card I)) : ℂ) *
      bracket (paired x y) (clasp (paired x y)) =
      (crossGram (Sum.elim x y) (Sum.elim x y)).permanent := by
  rw [← bracket_clasp, absorb_pair, bracket_scale, map_mul,
    show ∀ a b c d : ℂ, a*b*(c*d) = (a*c)*(b*d) by intros; ring, c_sq, c_sq, ← mul_assoc]
  have h := clasp_pure_closure (Sum.elim x y) (Sum.elim x y)
  rw [Fintype.card_sum] at h
  rw [← h]
  congr 1
  rw [← mul_assoc]
  have hf := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (Fintype.card I) (Fintype.card J))
  rw [Nat.add_sub_cancel_left] at hf
  exact_mod_cast hf

/-- In the finite word model the fine closure for arbitrary packet sizes
is the permanent of the combined Gram matrix. -/
theorem fine_permanent {p q d : ℕ} (x : Fin p → Fin d → ℂ) (y : Fin q → Fin d → ℂ) :
    ((p+q).choose p : ℂ) * quadratic (totalClasp d p q) (product (packet x) (packet y)) =
      (crossGram (Sum.elim x y) (Sum.elim x y)).permanent := by
  let e : (Fin p ⊕ Fin q) ≃ Fin (p+q) := finSumFinEquiv
  let z := fun w : Word d (p+q) => paired x y (w ∘ e)
  have he : product (packet x) (packet y) = z ∘ Fin.appendEquiv p q := by
    funext w
    simp [z, e, product, paired, Function.comp_def, -Fin.natAdd_eq_addNat]
  have hq := quadratic_reindex (Fin.appendEquiv p q) (symClasp d (p+q)) z
  change quadratic (totalClasp d p q) _ = _ at hq
  rw [he, hq, quadratic_bracket, symClasp_action]
  change _ * bracket (fun w => paired x y (w ∘ e)) (clasp (fun w => paired x y (w ∘ e))) = _
  rw [bracket_transport]
  simpa only [Fintype.card_fin] using paired_fine x y

/-- The straight cut in ordinary Gram matrix language, with arbitrary
positive-semidefinite data and group sizes including zero. -/
theorem principal_gram {p q d : ℕ} (h : HomogeneousSchur d p q)
    (x : Fin p → Fin d → ℂ) (y : Fin q → Fin d → ℂ) :
    (crossGram x x).permanent.re * (crossGram y y).permanent.re ≤
      (crossGram (Sum.elim x y) (Sum.elim x y)).permanent.re := by
  have he := straight_bound h (packet_symmetric _ _ x) (packet_symmetric _ _ y)
  rw [fine_permanent] at he
  simpa only [← packet_gram, Coarse.bracket_self, Complex.ofReal_re] using he


/-- The principal-block permanent inequality for an arbitrary finite complex
PSD matrix, derived from the coefficient-one homogeneous Schur relation. -/
theorem principal_blocks (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (schur : HomogeneousSchur (Fintype.card I + Fintype.card J) (Fintype.card I) (Fintype.card J)) :
    ThreeFine.LiebPrincipalBlocks I J := by
  intro A hA
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  let eI := Fintype.equivFin I
  let eJ := Fintype.equivFin J
  let e := eI.sumCongr eJ
  let full := e.trans finSumFinEquiv
  let raw (i : I ⊕ J) (r : Fin (Fintype.card I + Fintype.card J)) := B (full.symm r) i
  have hraw : A = crossGram raw raw := by
    rw [hB]
    ext i j
    exact (full.symm.sum_comp (fun r => star (B r i) * B r j)).symm
  let x := fun i => raw (Sum.inl (eI.symm i))
  let y := fun j => raw (Sum.inr (eJ.symm j))
  have hx : crossGram x x = (A.submatrix Sum.inl Sum.inl).submatrix eI.symm eI.symm := by
    rw [hraw]; rfl
  have hy : crossGram y y = (A.submatrix Sum.inr Sum.inr).submatrix eJ.symm eJ.symm := by
    rw [hraw]; rfl
  have hxy : crossGram (Sum.elim x y) (Sum.elim x y) = A.submatrix e.symm e.symm := by
    rw [hraw]; ext i j; cases i <;> cases j <;> rfl
  have h := principal_gram schur x y
  rwa [hx, hy, hxy, permanent_reindex, permanent_reindex, permanent_reindex] at h


end
end BlockPermanents.StraightCut
