import BlockPermanents.TwoCapExample
import BlockPermanents.Quadratic

/-! # The supported thin strand and the factor at the seam (4A.1 and BA.2) -/
namespace BlockPermanents.SupportRouteExamples
open Bend Closures Matrix
open scoped Matrix ComplexConjugate InnerProductSpace
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The dual has its unique supported basis covector. Its two neighbors are
the two coordinates of the product index. -/
def left (e : I → ℂ) : Matrix I (I × I) ℂ := fun i w =>
  if w.2=i then star (e w.1) else 0

def right (e : I → ℂ) : Matrix I (I × I) ℂ := fun i w =>
  if w.1=i then star (e w.2) else 0

theorem left_on_product (e x y : I → ℂ) (i : I) :
    (left e).mulVec (product x y) i = bracket e x * y i := by
  simp [left, product, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, bracket,
    Finset.sum_mul, mul_assoc]

theorem right_on_product (e x y : I → ℂ) (i : I) :
    (right e).mulVec (product x y) i = bracket e y * x i := by
  simp [right, product, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, bracket,
    Finset.sum_mul, mul_left_comm, mul_comm, mul_assoc, Finset.mul_sum]

theorem reflected_left (e z : I → ℂ) (w : I × I) :
    (left e)ᴴ.mulVec z w = e w.1 * z w.2 := by
  simp [left, Matrix.mulVec, conjTranspose_apply, dotProduct, apply_ite star, ite_mul]

theorem reflected_right (e z : I → ℂ) (w : I × I) :
    (right e)ᴴ.mulVec z w = e w.2 * z w.1 := by
  simp [right, Matrix.mulVec, conjTranspose_apply, dotProduct, apply_ite star, ite_mul]

theorem supported_bubble (e : I → ℂ) (unit : bracket e e = 1) : left e * (left e)ᴴ = 1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simpa [Matrix.mul_apply, left, conjTranspose_apply, Fintype.sum_prod_type, apply_ite star,
      ite_mul, mul_ite, bracket] using unit
  · simp [Matrix.mul_apply, left, conjTranspose_apply, Fintype.sum_prod_type, apply_ite star,
      ite_mul, mul_ite, h, Ne.symm h, Matrix.one_apply]

/-- Crossing the two reflected partners gives the kernel of projection onto e. -/
theorem crossed_gluing (e : I → ℂ) (i j : I) :
    (left e * (right e)ᴴ) i j = e i * star (e j) := by
  simp [Matrix.mul_apply, left, right, conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite star, ite_mul, mul_ite, mul_comm]

/-- The crossed gluing acts as Mathlib's orthogonal projection onto the supported line. -/
theorem crossed_projection (e z : EuclideanSpace ℂ I) (unit : ‖e‖ = 1) (j : I) :
    (left (fun i => e i) * (right (fun i => e i))ᴴ).mulVec (fun i => z i) j =
      (((ℂ ∙ e).orthogonalProjection z : EuclideanSpace ℂ I) j) := by
  rw [Submodule.orthogonalProjection_singleton]
  simp [Matrix.mulVec, dotProduct, crossed_gluing, unit, PiLp.inner_apply, RCLike.inner_apply,
    Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

theorem reflected_agree (e : I → ℂ) : (left e)ᴴ.mulVec e = (right e)ᴴ.mulVec e := by
  funext w
  rw [reflected_left, reflected_right, mul_comm]

omit [DecidableEq I] in
private theorem pair_bracket (a b c d : I → ℂ) :
    bracket (product a b) (product c d) = bracket a c * bracket b d := by
  calc
    _ = ∑ i, ∑ j, (star (a i) * c i) * (star (b j) * d j) := by
      simp only [bracket, product, Fintype.sum_prod_type, map_mul, Complex.star_def]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [bracket, ← Finset.mul_sum, ← Finset.sum_mul, Complex.star_def]

/-- For a unit output perpendicular to e, the two actual reflected rows are orthonormal. -/
theorem perpendicular_rows (e z : I → ℂ) (ue : bracket e e = 1) (uz : bracket z z = 1)
    (orth : bracket e z = 0) :
    let l := (left e)ᴴ.mulVec z
    let r := (right e)ᴴ.mulVec z
    bracket l l = 1 ∧ bracket r r = 1 ∧ bracket l r = 0 := by
  have hl : (left e)ᴴ.mulVec z = product e z := funext fun w => reflected_left e z w
  have hr : (right e)ᴴ.mulVec z = product z e := funext fun w => (reflected_right e z w).trans (mul_comm ..)
  simp only [hl, hr, pair_bracket, ue, uz, orth, one_mul, zero_mul, and_self]

/-- The two-order average on the exposed strands of a 2-cable. -/
def pairClasp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun w v =>
  ((if w=v then 1 else 0) + (if w=v.swap then 1 else 0))/2

/-- The displayed two-order average is the native symmetric clasp on word coordinates. -/
theorem pair_clasp_words (w v : Fin 2 × Fin 2) :
    pairClasp w v = symClasp 2 2 ![w.1,w.2] ![v.1,v.2] := by
  let a (z : Fin 2 × Fin 2) : Word 2 2 := ![z.1,z.2]
  have count : (Finset.univ.filter (fun p : Equiv.Perm (Fin 2) => a w = a v ∘ p)).card =
      (if w=v then 1 else 0) + (if w=v.swap then 1 else 0) := by
    rcases w with ⟨i,j⟩; rcases v with ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
  simp only [symClasp, Finset.sum_boole]
  change pairClasp w v = ((2).factorial:ℂ)⁻¹ *
    ((Finset.univ.filter (fun p : Equiv.Perm (Fin 2) => a w = a v ∘ p)).card : ℂ)
  rw [count, pairClasp]
  split_ifs <;> norm_num

def cap := left (![1,0] : Fin 2 → ℂ) * pairClasp

abbrev PairSpace := EuclideanSpace ℂ (Fin 2 × Fin 2)

def seam : PairSpace := (1/2 : ℂ) •
  (EuclideanSpace.single (0,1) 1 + EuclideanSpace.single (1,0) 1)

/-- The reflected supported cap on f is exactly (e⊗f+f⊗e)/2. -/
theorem reflected_seam (w : Fin 2 × Fin 2) :
    capᴴ.mulVec (![0,1] : Fin 2 → ℂ) w = seam w := by
  rcases w with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [cap, left, pairClasp, Matrix.mulVec, Matrix.mul_apply, conjTranspose_apply,
      dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, seam, EuclideanSpace.single_apply, Prod.ext_iff]

theorem seam_energy : ‖seam‖^2 = 1/2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [seam, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  norm_num

theorem glued_seam : (cap * capᴴ) 1 1 = 1/2 := by
  norm_num [cap, left, pairClasp, Matrix.mul_apply, conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The inverse squared seam norm gives the coefficient of the true line projector. -/
theorem seam_projection (v : PairSpace) :
    (((ℂ ∙ seam).orthogonalProjection v) : PairSpace) = (2 * @inner ℂ _ _ seam v) • seam := by
  rw [Submodule.orthogonalProjection_singleton, seam_energy]
  congr 1
  push_cast
  ring

end
end BlockPermanents.SupportRouteExamples
