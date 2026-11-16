import BlockPermanents.FourSupportedTensor
import BlockPermanents.Polarization

/-! # Sesquilinear representation of the four-block cut form -/
namespace BlockPermanents.FourFormKernel
open Bend Closures FourRoutes FourCapOrbit FourCapValues FourFullValues FourLastCaps
open FourSupportedTensor Polarization
open scoped BigOperators Matrix
noncomputable section

def properLin {d : ℕ} (r : Fin 3) : Boundary d →ₗ[ℂ] ((Port → Fin d) × Fin d → ℂ) where
  toFun z uv := proper r z uv.1 uv.2
  map_add' _ _ := by ext; simp [proper,Matrix.mulVec_add]
  map_smul' _ _ := by ext; simp [proper,Matrix.mulVec_smul]

def completeLin {d : ℕ} (r : Fin 3) : Boundary d →ₗ[ℂ] (Word d 4 → ℂ) where
  toFun := complete r
  map_add' _ _ := by ext; simp [complete,Matrix.mulVec_add]
  map_smul' _ _ := by ext; simp [complete,Matrix.mulVec_smul]

def fourthClasp {d : ℕ} : Boundary d →ₗ[ℂ] (Word d 4 → ℂ) :=
  (Matrix.mulVecLin (symClasp d 4)).comp (completeLin 0)

theorem fourthClasp_apply {d : ℕ} (z : Boundary d) : fourthClasp z = clasp (complete 0 z) :=
  Bridges.symClasp_action _ _ _

def corrected {d : ℕ} : Boundary d →ₗ[ℂ] (Word d 4 → ℂ) :=
  completeLin 2 - (15 : ℂ)⁻¹ • fourthClasp

theorem corrected_apply {d : ℕ} (z : Boundary d) :
    corrected z = fun w => complete 2 z w - clasp (complete 0 z) w / 15 := by
  funext w
  change _ - (15 : ℂ)⁻¹ * fourthClasp z w = _
  rw [fourthClasp_apply,div_eq_mul_inv,mul_comm]
  rfl

def kernel (d : ℕ) : Kernel (Boundary d) :=
  24 • pair (properLin 0) (properLin 0) + 144 • pair (properLin 1) (properLin 1) +
  1080 • pair (properLin 2) (properLin 2) + 1350 • pair corrected corrected +
  108 • pair (completeLin 1) (completeLin 1) - 12 • pair (completeLin 0) (completeLin 0) -
  24 • pair fourthClasp fourthClasp

theorem kernel_form {d : ℕ} (z : Boundary d) : (kernel d z z).re = form z := by
  have pr (r : Fin 3) : energy (properLin r z) = rawEnergy Finset.univ (proper r z) := by
    simp [energy,Fintype.sum_prod_type,rawEnergy,properLin]
  simp only [kernel,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Complex.add_re,Complex.sub_re,Complex.re_nsmul,pair_energy,pr,corrected_apply,fourthClasp_apply]
  simp [form,completeLin,nsmul_eq_mul]

theorem form_product {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) :
    form (product F (fun v => star (H v))) = cutForm F H := by
  unfold form cutForm
  simp_rw [proper_eq_raw]
  rfl

end
end BlockPermanents.FourFormKernel
