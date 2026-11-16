import BlockPermanents.FourGeneralProduct
import BlockPermanents.FourFormKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The supported compression of the actual partially transposed transfer -/
namespace BlockPermanents.FourCompression
open FourTarget FourUpright FourRoutes FourCapOrbit FourFullValues FourSupportedTensor
open Closures Bend SchurNormalization Polarization
open scoped BigOperators Matrix
noncomputable section
attribute [local irreducible] FourTarget.Q

abbrev Index (d : ℕ) := Triple d 2 × Word d 2

/-- Oriented ordinary triple and marked packet, in the order used in the cap calculation. -/
def layout (d : ℕ) : (Slot 2 → Fin d) ≃ Index d :=
  (((wires 2 ori).symm.arrowCongr (Equiv.refl _)).trans
    (last.symm.arrowCongr (Equiv.refl _))).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans ((Equiv.curry _ _ _).prodCongr (Equiv.refl _)))

def pull {A B : Type*} (e : A ≃ B) : (B → ℂ) →ₗ[ℂ] (A → ℂ) where
  toFun v := v ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Matrix of the marked transfer in ordinary-triple × marked-packet coordinates. -/
def markedMatrix (d : ℕ) : Matrix (Index d) (Index d) ℂ :=
  LinearMap.toMatrix' ((pull (layout d).symm).comp ((Q d 2).comp (pull (layout d))))

theorem marked_action {d : ℕ} (v : Boundary d) :
    (markedMatrix d).mulVec v = pull (layout d).symm (Q d 2 (pull (layout d) v)) := by
  rw [← Matrix.toLin'_apply,markedMatrix,Matrix.toLin'_toMatrix']
  rfl

theorem marked_quadratic {d : ℕ} (z : Boundary d) :
    quadratic (markedMatrix d) z = bracket (pull (layout d) z) (Q d 2 (pull (layout d) z)) := by
  rw [Bridges.quadratic_bracket,marked_action]
  exact ((layout d).sum_comp (fun a => star (z a) * Q d 2 (pull (layout d) z) ((layout d).symm a))).symm.trans
    (Finset.sum_congr rfl fun w _ => by
      change _ * Q d 2 _ ((layout d).symm (layout d w)) = _; rw [Equiv.symm_apply_apply]; rfl)

theorem ordinary_product {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) :
    pull (layout d) (product F H) = FourGeneralProduct.upright F H := rfl

def ordinarySpace (d : ℕ) : Submodule ℂ (Triple d 2 → ℂ) where
  carrier := {F | Inner F}
  zero_mem' := by intros t w; rfl
  add_mem' h g := by intro t w; exact congrArg₂ (· + ·) (h t w) (g t w)
  smul_mem' a _ h := by intro t w; exact congrArg (a * ·) (h t w)

def dual {T : Type*} (y : T → ℂ) : T → ℂ := fun t => star (y t)
@[simp] theorem dual_dual {T : Type*} (y : T → ℂ) : dual (dual y) = y := by ext; simp [dual]
@[simp] theorem dual_add {T : Type*} (y y' : T → ℂ) : dual (y+y') = dual y + dual y' := by
  ext; simp [dual]
@[simp] theorem dual_smul {T : Type*} (a : ℂ) (y : T → ℂ) : dual (a • y) = star a • dual y := by
  ext; simp [dual,mul_comm]

def markedSpace {d : ℕ} (S : Finset (Fin d)) : Submodule ℂ (Word d 2 → ℂ) where
  carrier := {y | Bend.Symmetric (dual y) ∧ Supported S (dual y)}
  zero_mem' := by
    have h : dual (0 : Word d 2 → ℂ) = 0 := by ext; simp [dual]
    rw [Set.mem_setOf_eq,h]; exact ⟨by simp [Bend.Symmetric],fun _ _ _ => rfl⟩
  add_mem' := by
    intro v w ⟨hv,hv'⟩ ⟨hw,hw'⟩
    change Bend.Symmetric (dual (v+w)) ∧ Supported S (dual (v+w))
    rw [dual_add]; constructor
    · unfold Bend.Symmetric at *; rw [Matrix.mulVec_add,hv,hw]
    · intro b hb t; simp [hv' b hb t,hw' b hb t]
  smul_mem' := by
    intro a v ⟨hv,hv'⟩
    change Bend.Symmetric (dual (a • v)) ∧ Supported S (dual (a • v))
    rw [dual_smul]; constructor
    · unfold Bend.Symmetric at *; rw [Matrix.mulVec_smul,hv]
    · intro b hb t; simp [hv' b hb t]

private theorem simple_eq {d : ℕ} (S : Finset (Fin d)) :
    simple S = {u | ∃ x ∈ ordinarySpace d, ∃ y ∈ markedSpace S, product x y = u} := by
  ext z; constructor
  · rintro ⟨x,y,hx,hy,hS,rfl⟩
    refine ⟨x,hx,dual y,?_,rfl⟩
    change Bend.Symmetric (dual (dual y)) ∧ Supported S (dual (dual y))
    simpa only [dual_dual] using And.intro hy hS
  · rintro ⟨x,hx,y,⟨hy,hS⟩,rfl⟩
    exact ⟨x,dual y,hx,hy,hS,congrArg (product x) (dual_dual _)⟩

/-- The entangled cut form is exactly the real expectation of the actual
partial transpose of Q, restricted to the specified packet subspaces. -/
theorem quadratic_eq {d : ℕ} (S : Finset (Fin d)) (h₂ : HomogeneousSchur d 2 2)
    (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) {z : Boundary d}
    (hz : z ∈ Submodule.span ℂ (simple S)) :
    (quadratic (partialTranspose (markedMatrix d)) z).re = form z := by
  let M := partialTranspose (markedMatrix d)
  let K : Kernel (Boundary d) := pair LinearMap.id (Matrix.mulVecLin M)
  have read (v : Boundary d) : K v v = quadratic M v := (Bridges.quadratic_bracket M v).symm
  rw [simple_eq] at hz
  rw [← FourFormKernel.kernel_form,← read]
  apply product_ext (ordinarySpace d) (markedSpace S) K (FourFormKernel.kernel d) _ hz
  intro x hx y hy
  obtain ⟨hy,_⟩ := hy
  have h := FourGeneralProduct.marked_product x hx (dual y) hy h₂ h₄ h₆
  rw [read,FourFormKernel.kernel_form]
  have b := evaluate_bend (markedMatrix d) x (dual y)
  change quadratic (markedMatrix d) (product x (dual y)) = quadratic M (product x (dual (dual y))) at b
  rw [dual_dual] at b
  rw [← b,marked_quadratic,ordinary_product,h]
  have g := (FourFormKernel.form_product x (dual y)).symm
  change _ = form (product x (dual (dual y))) at g
  rwa [dual_dual] at g

/-- Theorem 5D.1 on the whole supported tensor product, including mixed inputs. -/
theorem nonnegative {d : ℕ} (S : Finset (Fin d)) (hc : S.card = 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2)
    {z : Boundary d} (hz : z ∈ Submodule.span ℂ (simple S)) :
    0 ≤ (quadratic (partialTranspose (markedMatrix d)) z).re :=
  (quadratic_eq S h₂ h₄ h₆ hz).symm ▸ FourSupportedTensor.nonnegative S hc hz

end
end BlockPermanents.FourCompression
