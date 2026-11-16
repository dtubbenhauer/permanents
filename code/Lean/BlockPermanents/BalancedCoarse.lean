import BlockPermanents.BalancedSigned
import BlockPermanents.Quadratic

/-! # Opening the packet-scale side of a balanced bend -/
namespace BlockPermanents.BalancedCoarse
open Closures Bend BalancedSigned
open scoped ComplexConjugate Matrix
noncomputable section

private def normalized (a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,a,b,c; conj a,1,d,e; conj b,conj d,1,f; conj c,conj e,conj f,1]

private theorem open_polynomial (a b c d e f : ℂ) :
    let α : Fin 4 → ℂ := ![conj b,conj c,conj d,conj e]
    (normalized a b c d e f).permanent =
      ((1+Complex.normSq a)*(1+Complex.normSq f):ℝ) +
        dotProduct (star α) ((gram (conj a) f).mulVec α) +
        (Complex.normSq (conj b*conj e + conj c*conj d):ℂ) := by
  dsimp only
  simp only [Quadratic.permanent_succ, Matrix.permanent_isEmpty, Matrix.of_apply,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
  norm_num [normalized, gram, Equiv.swap_apply_def, Fin.succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.star_def,
    Complex.normSq_eq_conj_mul_self]
  ring

def leftSide {D : Type*} (X : Fin 4 → D → ℂ) : Fin 2 → D → ℂ := ![X 0,X 1]
def rightSide {D : Type*} (X : Fin 4 → D → ℂ) : Fin 2 → D → ℂ := ![X 2,X 3]

/-- With a unit packet at each foot, the straight term, one-cap term,
and two-cap term sum to the actual four-packet Gram permanent. -/
theorem open_coarse {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ)
    (h : ∀ i, energy (X i) = 1) :
    let g := crossGram X X
    let U := leftSide X
    let V := rightSide X
    let α := caps U V
    g.permanent.re =
      (1+Complex.normSq (g 0 1))*(1+Complex.normSq (g 2 3)) +
      energy ((survivors U V).mulVec α) + Complex.normSq (α 0*α 3 + α 1*α 2) := by
  let g := crossGram X X
  let U := leftSide X
  let V := rightSide X
  let α := caps U V
  let M := survivors U V
  have symm (i j : Fin 4) : conj (g i j) = g j i := by simp [g,crossGram,bracket,map_sum,mul_comm]
  have diag (i) : g i i = 1 := by simp [g,crossGram,Coarse.bracket_self,h]
  have hg : g = normalized (g 0 1) (g 0 2) (g 0 3) (g 1 2) (g 1 3) (g 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [normalized,diag,symm]
  have a (i) : energy (U i)=1 := by fin_cases i <;> simp [U,leftSide,h]
  have b (i) : energy (V i)=1 := by fin_cases i <;> simp [V,rightSide,h]
  have hM : Mᴴ*M = gram (conj (g 0 1)) (g 2 3) := by
    rw [survivors_gram _ _ a b]
    change gram (g 1 0) (conj (g 3 2)) = _
    simp [symm]
  have hα : α = ![conj (g 0 2),conj (g 0 3),conj (g 1 2),conj (g 1 3)] := by
    funext i
    simp only [symm]
    fin_cases i <;> rfl
  have hh := open_polynomial (g 0 1) (g 0 2) (g 0 3) (g 1 2) (g 1 3) (g 2 3)
  dsimp only at hh
  rw [← hg, ← hα, ← hM, PairSquares.gram_eval] at hh
  have hx : (α 0*α 3+α 1*α 2) = conj (g 0 2)*conj (g 1 3) + conj (g 0 3)*conj (g 1 2) := by
    rw [hα]; rfl
  rw [← hx] at hh
  exact_mod_cast congrArg Complex.re hh

end
end BlockPermanents.BalancedCoarse
