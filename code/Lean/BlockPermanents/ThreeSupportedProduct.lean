import BlockPermanents.ThreeOriginalSupported

/-! # Testing the supported three-packet bend on unbent product states -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend SchurNormalization Matrix
open scoped Matrix ComplexOrder BigOperators
noncomputable section

private theorem legs_product {A B I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix A I ℂ) (N : Matrix B J ℂ) (F : I → ℂ) (G : J → ℂ) :
    (legs M N).mulVec (product F G) = product (M.mulVec F) (N.mulVec G) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, legs, product, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun j i => M x.1 i * F i * (N x.2 j * G j))]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

private theorem qdot {I : Type*} [Fintype I] (M : Matrix I I ℂ) (v : I → ℂ) :
    quadratic M v = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

private theorem compressed_quad {I : Type*} [Fintype I] (M C : Matrix I I ℂ) (z : I → ℂ)
    (h : C.mulVec z=z) : quadratic (Cᴴ*M*C) z = quadratic M z := by
  rw [qdot,qdot,← Matrix.mulVec_mulVec,h,← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,← Matrix.star_mulVec,h]

private theorem restrict_sum {I : Type*} [Fintype I] (s : I → Prop) [DecidablePred s]
    (f : I → ℂ) (h : ∀ i, ¬s i → f i=0) : (∑ i,f i) = ∑ i : {i // s i}, f i := by
  rw [← Fintype.sum_subtype_add_sum_subtype s f]
  simp only [fun (i : {i // ¬s i}) => h i i.property, Finset.sum_const_zero,add_zero]

private theorem supported_quad {I J : Type*} [Fintype I] [Fintype J]
    (s : J → Prop) [DecidablePred s] (h : J → ℂ) (hs : ∀ i, ¬s i → h i=0)
    (v : I → ℂ) (M : Matrix (I×J) (I×J) ℂ) :
    quadratic M (product v h) = quadratic (M.submatrix (fun i : I × {j // s j} => (i.1,i.2.val))
      (fun i : I × {j // s j} => (i.1,i.2.val))) (product v (fun j => h j.val)) := by
  simp only [quadratic,product,Matrix.submatrix_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [restrict_sum s _ (fun j hj => by simp [hs j hj])]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro a _
  exact restrict_sum s _ (fun b hb => by simp [hs b hb])

/-- The original unbent marked operator is nonnegative on three symmetric
packet vectors when the marked vector is supported on at most k basis labels. -/
theorem original_product_nonnegative {d k : ℕ} (hk : 2≤k)
    (hs : HomogeneousSchur d k k) (hb : HomogeneousSchur d (k+k) k)
    (S : Finset (Fin d)) (hS : 0<S.card) (hSk : S.card≤k)
    (F G H : K d k → ℂ) (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H)
    (hSupport : ∀ w, (∃ i, w i∉S) → H w=0) :
    0 ≤ (quadratic (original d k) (product (product F G) H)).re := by
  let z := product (product F G) H
  have fixed : (internal d k).mulVec z=z := by
    unfold Bend.Symmetric at hF hG hH
    simp only [internal,z,legs_product,hF,hG,hH]
  have pos := original_supported hk hs hb S hS hSk
  let v := product (product F G) (fun j : {w : K d k // ∀ t,w t∈S} => star (H j.val))
  have he := (Complex.nonneg_iff.mp (pos.2 v)).1
  change 0 ≤ (quadratic (original d k) z).re
  rw [← compressed_quad _ _ _ fixed, evaluate_bend]
  have zero (w : K d k) (hw : ¬ ∀ t,w t∈S) : star (H w)=0 := by
    rw [hSupport w (Classical.not_forall.mp hw),star_zero]
  rw [supported_quad (fun w : K d k => ∀ t,w t∈S) _ zero, qdot]
  exact he

end
end BlockPermanents.ThreeGeneralOpen
