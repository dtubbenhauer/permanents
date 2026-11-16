import BlockPermanents.FourNativeFull
import BlockPermanents.ZeroCapDefs
import BlockPermanents.ThreeEvaluation

/-! On a packet-symmetric boundary the four internal clasps act as the identity. -/
namespace BlockPermanents.FourNative
open Bend FourTarget FourRoutes FourExchangeKernel FourThickCompression ThreeGeneralOpen
open scoped BigOperators Matrix
noncomputable section

/-- The ordinary triple may be entangled. Each ordinary packet is independently
symmetric and each marked column is symmetric. -/
theorem boundary_fixed {d k : ℕ} {I J : Type*}
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hm : ∀ (p : Fin 3 → Equiv.Perm (Fin k)) u i, M (fun t => u t ∘ p t) i = M u i)
    (hn : ∀ j, Symmetric (fun w => N w j)) :
    matrix d k (W d k) * legs M N = legs M N := by
  classical
  have fixp (p : Fin 4 → Equiv.Perm (Fin k)) :
      matrix d k (act d k (withinHom k p)) * legs M N = legs M N := by
    ext x c
    rw [Matrix.mul_apply]
    simp only [matrix_perm_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    have hr : layout d k ((layout d k).symm x ∘ withinHom k p) =
        (fun t => x.1 t ∘ p t.castSucc, x.2 ∘ p 3) := by
      apply Prod.ext
      · funext t j
        exact layout_read x t (p t.castSucc j)
      · rfl
    rw [hr]
    exact congrArg₂ (· * ·) (hm (fun t => p t.castSucc) x.1 c.1)
      (ThreeWire.symmetric_word_perm (hn c.2) x.2 (p 3))
  simp only [W,Transfer.clasp,map_smul,map_sum,Matrix.smul_mul,Matrix.sum_mul,
    MonoidHom.comp_apply,fixp,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) _

/-- In word coordinates these four clasped inputs span the packet-symmetric boundary. -/
theorem clasps_fixed (d k : ℕ) :
    matrix d k (W d k) * legs (ZeroCap.inner d k 3) (symClasp d k) =
      legs (ZeroCap.inner d k 3) (symClasp d k) := by
  apply boundary_fixed
  · intro p u i
    apply Finset.prod_congr rfl
    intro t _
    exact ThreeWire.symmetric_word_perm (column_symmetric d k (i t)) (u t) (p t)
  · exact column_symmetric d k

end
end BlockPermanents.FourNative
