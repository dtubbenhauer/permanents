import BlockPermanents.ZeroCap
import BlockPermanents.HomogeneousSchurProof
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # The interchange and the explicit cut tables, Examples 2C.4, 2C.9, 3A.4 -/
namespace BlockPermanents.IntroExamples
open Bend SchurNormalization ThreeGeneralOpen Support
open scoped Matrix BigOperators ComplexOrder
noncomputable section

/-- Interchange the two copies of W, before bending. -/
def interchange (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if j = i.swap then 1 else 0

/-- The single evaluation cap W ⊗ W* → ℂ. -/
def evaluation (d : ℕ) : Matrix Unit (Fin d × Fin d) ℂ :=
  fun _ i => if i.1 = i.2 then 1 else 0

/-- The antisymmetric product in coordinates. -/
def alternating {d : ℕ} (x y : Fin d → ℂ) (i : Fin d × Fin d) :=
  x i.1 * y i.2 - y i.1 * x i.2

theorem interchange_alternating {d : ℕ} (x y : Fin d → ℂ) :
    (interchange d).mulVec (alternating x y) = (-1:ℂ) • alternating x y := by
  funext i
  simp [Matrix.mulVec, dotProduct, interchange, alternating, ite_mul]
  ring

theorem alternating_ne_zero {d : ℕ} (x y : Fin d → ℂ) (h : LinearIndependent ℂ ![x,y]) :
    alternating x y ≠ 0 := by
  obtain ⟨hy,hxy⟩ := linearIndependent_fin2.mp h
  change y ≠ 0 at hy
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hy
  change y j ≠ 0 at hj
  intro hz
  apply hxy (x j/y j)
  funext i
  change (x j/y j)*y i = x i
  have he := congrFun hz (i,j)
  change x i*y j - y i*x j = 0 at he
  field_simp
  linear_combination -he

theorem bend_interchange (d : ℕ) :
    partialTranspose (interchange d) = reflected (evaluation d) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hij : i=j <;> by_cases hkl : k=l <;>
    simp [partialTranspose, interchange, evaluation, reflected, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Prod.ext_iff, hij, hkl, Ne.symm]

/-- The action in Lemma 2C.1: w ⊗ φ is sent to φ(w) times the coevaluation
vector, whose (i,j) entry is the Kronecker delta. -/
theorem cap_cup_action {d : ℕ} (w φ : Fin d → ℂ) :
    (partialTranspose (interchange d)).mulVec (product w φ) =
      (∑ a, φ a * w a) • (fun i : Fin d × Fin d => if i.1 = i.2 then (1 : ℂ) else 0) := by
  rw [bend_interchange, reflected, ← Matrix.mulVec_mulVec]
  have hc (t : Unit) : (evaluation d).mulVec (product w φ) t = ∑ a, φ a * w a := by
    simp [evaluation, Matrix.mulVec, dotProduct, product, Fintype.sum_prod_type,
      ite_mul, mul_comm]
  rw [show (evaluation d).mulVec (product w φ) = (fun _ : Unit => ∑ a, φ a*w a) from funext hc]
  funext i
  by_cases h : i.1 = i.2 <;>
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, evaluation, h]

theorem bent_interchange_psd (d : ℕ) : (partialTranspose (interchange d)).PosSemidef := by
  rw [bend_interchange]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The two rows of (2C.9) as equalities between the actual open matrices. -/
theorem two_strands (d : ℕ) :
    (6 : ℂ) • partialTranspose (totalClasp d 2 2) = reflected (wordCap d 2 2 0) +
      (4:ℂ) • reflected (wordCap d 2 2 1) + reflected (wordCap d 2 2 2) := by
  ext x y
  have h := bent_schur d 2 2 (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d 2 2)) x y
  change _ = ∑ r : Fin 3, _ at h
  rw [Fin.sum_univ_three] at h
  norm_num [weight, Nat.choose, reflected, Matrix.smul_apply] at h ⊢
  exact h

theorem three_strands (d : ℕ) :
    (20 : ℂ) • partialTranspose (totalClasp d 3 3) = reflected (wordCap d 3 3 0) +
      (9:ℂ) • reflected (wordCap d 3 3 1) + (9:ℂ) • reflected (wordCap d 3 3 2) +
      reflected (wordCap d 3 3 3) := by
  ext x y
  have h := bent_schur d 3 3 (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d 3 3)) x y
  change _ = ∑ r : Fin 4, _ at h
  rw [Fin.sum_univ_four] at h
  norm_num [weight, Nat.choose, reflected, Matrix.smul_apply] at h ⊢
  exact h

/-- The two upright contributions inside X₂ have weights six and two. -/
theorem upright_two (d : ℕ) : ZeroCap.oldX d 2 2 =
    (6:ℂ) • reflected (ZeroCap.merge d 2 2) - (2:ℂ) • reflected (ZeroCap.coarseMerge d 2 2) := by
  norm_num [ZeroCap.oldX, ZeroCap.a, Nat.factorial]

/-- The physical marked three-quadratic opening of Example 3A.4, including
the one proper thin cut, the full thin cut, and the full packet cut. -/
theorem three_quadratic (d : ℕ) : partialTranspose (ZeroCap.newX d 2 2) =
    legs (ZeroCap.oldX d 2 2) (symClasp d 2) +
    (48:ℂ) • reflected (routed (fun _ : Unit => ZeroCap.merge d 2 2) (ZeroCap.mark d 2) 1 ()) +
    (36:ℂ) • reflected (ZeroCap.fullCut (ZeroCap.thinRows d 2 1) (ZeroCap.mark d 2)) -
    (4:ℂ) • reflected (ZeroCap.fullCut (ZeroCap.packetRows d 2 1) (ZeroCap.mark d 2)) := by
  have h := ZeroCap.opening d 2 1 (by decide) (homogeneousSchur _ _ _) (homogeneousSchur _ _ _)
  have hm : middle 4 2 (by decide) = {1} := by decide
  norm_num [ZeroCap.proper, properSquares, hm, ZeroCap.a, Nat.factorial, weight, Nat.choose,
    smul_smul] at h
  exact h

end
end BlockPermanents.IntroExamples
