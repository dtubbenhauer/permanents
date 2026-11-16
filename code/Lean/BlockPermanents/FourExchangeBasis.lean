import BlockPermanents.FourThickSlots
import BlockPermanents.FourRoutes
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Convert operators on all 4k slots to matrices on the ordinary-triple
and marked-packet word basis, preserving products and rational coefficients. -/
namespace BlockPermanents.FourExchangeKernel
open FourTarget FourRoutes Bend Equiv
open scoped Matrix BigOperators
noncomputable section
abbrev Index (d k : ℕ) := Triple d k × Word d k

def layout (d k : ℕ) : (Slot k → Fin d) ≃ Index d k where
  toFun w := (fun i j => w (i.castSucc,j),fun j => w (3,j))
  invFun u a := ![u.1 0,u.1 1,u.1 2,u.2] a.1 a.2
  left_inv w := by funext ⟨i,j⟩;fin_cases i <;> rfl
  right_inv w := by
    apply Prod.ext
    · funext i j;fin_cases i <;> rfl
    · rfl

def matrix (d k : ℕ) : Op d k →ₐ[ℚ] Matrix (Index d k) (Index d k) ℂ :=
  ((Matrix.reindexAlgEquiv ℂ ℂ (layout d k)).toAlgHom.comp
    (algEquivMatrix' (R:=ℂ)).toAlgHom).restrictScalars ℚ

theorem matrix_entry {d k : ℕ} (T : Op d k) (x y : Index d k) :
    matrix d k T x y = T (fun v => if v=(layout d k).symm y then 1 else 0) ((layout d k).symm x) := by
  exact LinearMap.toMatrix'_apply T _ _

theorem matrix_perm_apply {d k : ℕ} (p : Wire k) (x y : Index d k) :
    matrix d k (act d k p) x y = if (layout d k) (((layout d k).symm x) ∘ p)=y then 1 else 0 := by
  rw [matrix_entry]
  change (if ((layout d k).symm x) ∘ p = (layout d k).symm y then _ else _) = _
  simp only [(layout d k).apply_eq_iff_eq_symm_apply]

end
end BlockPermanents.FourExchangeKernel
