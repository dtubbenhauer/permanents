import BlockPermanents.PairSquares
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # The four surviving routes of a two-against-two bend

The route basis is ordered 00, 01, 10, 11. On a route the two uncontracted
packets have the complementary row and column labels. -/
namespace BlockPermanents.BalancedSigned
open Closures Bend
open scoped ComplexConjugate Matrix BigOperators
noncomputable section

private def rows {D : Type*} (U : Fin 2 → D → ℂ) : Fin 4 → D → ℂ :=
  ![U 1,U 1,U 0,U 0]
private def cols {D : Type*} (V : Fin 2 → D → ℂ) : Fin 4 → D → ℂ :=
  ![V 1,V 0,V 1,V 0]

/-- Each column is the surviving ordinary packet tensored with the dual
of the surviving turned packet. -/
def survivors {D : Type*} (U V : Fin 2 → D → ℂ) : Matrix (D×D) (Fin 4) ℂ :=
  fun w i => rows U i w.1 * star (cols V i w.2)

def phases : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]

def both (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,a*b; 0,0,a*conj b,0; 0,conj a*b,0,0; conj a*conj b,0,0,0]

def gram (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,b,a,a*b; conj b,1,a*conj b,a; conj a,conj a*b,1,b; conj a*conj b,conj a,conj b,1]

def residual (t : ℝ) (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (t:ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - ((t:ℂ)⁻¹) • both a b

private theorem gram_entry {D : Type*} [Fintype D] (U V : Fin 2 → D → ℂ) (i j : Fin 4) :
    ((survivors U V)ᴴ * survivors U V) i j =
      bracket (rows U i) (rows U j) * star (bracket (cols V i) (cols V j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, survivors, Fintype.sum_prod_type,
    bracket, star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Complex.star_def, Complex.conj_conj]
  ring

theorem survivors_gram {D : Type*} [Fintype D] (U V : Fin 2 → D → ℂ)
    (hU : ∀ i, energy (U i) = 1) (hV : ∀ i, energy (V i) = 1) :
    (survivors U V)ᴴ * survivors U V = gram (bracket (U 1) (U 0)) (star (bracket (V 1) (V 0))) := by
  have hsym (X Y : D → ℂ) : conj (bracket X Y) = bracket Y X := by simp [bracket,map_sum,mul_comm]
  ext i j
  rw [gram_entry]
  fin_cases i <;> fin_cases j <;> simp [rows,cols,gram,Coarse.bracket_self,hU,hV,Complex.star_def,hsym]

private theorem change_sign (a b : ℂ) :
    gram a b + phasesᴴ * gram a b * phases = (2:ℂ) • 1 + (2:ℂ) • both a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram,phases,both,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ] <;> ring

private theorem both_sq (a b : ℂ) : both a b * both a b =
    ((Complex.normSq a * Complex.normSq b:ℝ):ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [both,Matrix.mul_apply,Fin.sum_univ_succ,Complex.normSq_eq_conj_mul_self] <;> ring

private theorem both_herm (a b : ℂ) : (both a b)ᴴ = both a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [both,Matrix.conjTranspose_apply,Complex.star_def]

private theorem signed_operator (t : ℝ) (ht : 0<t) (a b : ℂ) :
    gram a b + phasesᴴ * gram a b * phases + (residual t a b)ᴴ * residual t a b =
      ((2+t^2+(Complex.normSq a * Complex.normSq b)/t^2:ℝ):ℂ) • 1 := by
  rw [change_sign]
  simp only [residual,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    both_herm,star_inv₀,Complex.star_def,Complex.conj_ofReal,sub_mul,mul_sub,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,both_sq]
  have hn : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [mul_inv_cancel₀ hn, inv_mul_cancel₀ hn, one_smul]
  ext i j
  by_cases he : i=j <;> simp [he,Matrix.one_apply,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_add,Complex.ofReal_ofNat] <;> ring

/-- The signed gluing of Section 6.3, on arbitrary route coefficients.
In particular it applies to the four actual cross-pair contractions. -/
theorem signed_gluing {D : Type*} [Fintype D] (U V : Fin 2 → D → ℂ)
    (hU : ∀ i, energy (U i) = 1) (hV : ∀ i, energy (V i) = 1) (t : ℝ) (ht : 0<t)
    (α : Fin 4 → ℂ) :
    let M := survivors U V
    let a := bracket (U 1) (U 0)
    let b := star (bracket (V 1) (V 0))
    (2+t^2+(Complex.normSq a * Complex.normSq b)/t^2)*energy α - energy (M.mulVec α) =
      energy ((M*phases).mulVec α) + energy ((residual t a b).mulVec α) := by
  dsimp only
  let M := survivors U V
  let a := bracket (U 1) (U 0)
  let b := star (bracket (V 1) (V 0))
  have hg : Mᴴ*M = gram a b := survivors_gram U V hU hV
  have he := signed_operator t ht a b
  rw [← hg] at he
  have hr : phasesᴴ*(Mᴴ*M)*phases = (M*phases)ᴴ*(M*phases) := by
    rw [Matrix.conjTranspose_mul]; simp [Matrix.mul_assoc]
  rw [hr] at he
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => dotProduct (star α) (A.mulVec α)) he
  simp only [Matrix.add_mulVec,dotProduct_add,PairSquares.gram_eval,Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec,dotProduct_smul,smul_eq_mul] at h
  have hα : dotProduct (star α) α = (energy α:ℂ) := by
    simp [dotProduct,energy,Complex.normSq_eq_conj_mul_self]
  rw [hα, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_add] at h
  have hreal := Complex.ofReal_injective h
  change _ - energy (M.mulVec α) = _
  linarith only [hreal]

/-- The route coefficients supplied by the two ordinary and two turned
packet inputs, in the same ordering as the survivor matrix. -/
def caps {D : Type*} [Fintype D] (U V : Fin 2 → D → ℂ) : Fin 4 → ℂ :=
  ![bracket (V 0) (U 0),bracket (V 1) (U 0),bracket (V 0) (U 1),bracket (V 1) (U 1)]

end
end BlockPermanents.BalancedSigned
