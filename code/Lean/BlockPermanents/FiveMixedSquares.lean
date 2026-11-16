import BlockPermanents.FiveResidualGram
import BlockPermanents.FiveProjection
import BlockPermanents.FiveMixed

/-! The single squared norm and diagonal subtraction in Lemma 8B.3. -/
namespace BlockPermanents.FiveMixedSquares
open Closures Bend FiveProjection Support
open scoped Matrix BigOperators ComplexOrder
noncomputable section

/-- Columns of the two test halves, the ordinary packet and its full cap at H. -/
def testRows {d k : ℕ} {I : Type*} (l m : ℝ) (H : Word d k → ℂ) (F : I → Word d k → ℂ) :
    Matrix (Word d k ⊕ Unit) I ℂ :=
  fun a i => Sum.elim (fun w => (Real.sqrt l : ℂ) * F i w)
    (fun _ => (Real.sqrt m : ℂ) * bracket H (F i)) a

private theorem test_scale (t : ℝ) (ht : 0 ≤ t) (a b : ℂ) :
    star ((Real.sqrt t : ℂ) * a) * ((Real.sqrt t : ℂ) * b) = (t : ℂ) * (star a * b) := by
  have h : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = t := by
    exact_mod_cast Real.mul_self_sqrt ht
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [← h]
  ring

open private pairStar from BlockPermanents.FiveProjection in
theorem test_gram {d k : ℕ} {I : Type*} (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (H : Word d k → ℂ) (F : I → Word d k → ℂ) :
    reflected (testRows l m H F) = testForm l m H F := by
  ext i j
  simp only [reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_sum_type,
    testRows,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,test_scale l hl,test_scale m hm]
  rw [← Finset.mul_sum, pairStar]
  simp [testForm,bracket,mul_assoc]

/-- The conjugate test exit tensored with its corresponding residual exit,
summed over all available packet labels. -/
def mixedHalf {I A B : Type*} [Fintype I] (Y : Matrix A I ℂ) (T : Matrix B I ℂ)
    (p : A × B) : ℂ := ∑ i, star (Y p.1 i) * T p.2 i

/-- Closing the two halves retains every mixed entry, including its complex phase. -/
theorem mixed_gram {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (Y : Matrix A I ℂ) (T : Matrix B I ℂ) :
    (energy (mixedHalf Y T) : ℂ) = ∑ i, ∑ j, star (reflected Y i j) * reflected T i j := by
  rw [← Coarse.bracket_self]
  unfold mixedHalf
  rw [bracket_sum_left]
  simp_rw [bracket_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [bracket,Fintype.sum_prod_type,reflected,Matrix.mul_apply,
    Matrix.conjTranspose_apply,star_sum,star_mul',star_star,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change star (star (Y a i) * T b i) * (star (Y a j) * T b j) = _
  simp only [star_mul',star_star]
  ring

private theorem reflected_diag {A I : Type*} [Fintype A] (C : Matrix A I ℂ) (i : I) :
    reflected C i i = (energy (fun a => C a i) : ℂ) := Coarse.bracket_self _

/-- Removing equal labels costs two copies of the diagonal mixed cap. -/
private theorem off_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (Y T : Matrix I I ℂ) (hdiag : ∀ i, star (Y i i) = ((Y i i).re : ℂ)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y j i) * T j i).re)) =
      (∑ i, ((Fintype.card I : ℝ) - 1 - 2 * (Y i i).re) * (T i i).re) +
      2 * ∑ i, ∑ j, (star (Y i j) * T i j).re := by
  have row (i : I) : (∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y j i) * T j i).re)) =
      ((Fintype.card I : ℝ) - 1 - 2 * (Y i i).re) * (T i i).re +
        2 * ∑ j, (star (Y j i) * T j i).re := by
    have hi : Nonempty I := ⟨i⟩
    have hc : ((Fintype.card I - 1 : ℕ) : ℝ) = (Fintype.card I : ℝ) - 1 := by
      rw [Nat.cast_sub (Fintype.card_pos (α := I)), Nat.cast_one]
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,nsmul_eq_mul,hc,← Finset.mul_sum,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i),hdiag i]
    simp only [Complex.re_ofReal_mul]
    ring
  simp_rw [row]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (f := fun i j => (star (Y j i) * T j i).re)]

/-- The physical tensor sum in the proof of Lemma 8B.3. -/
def physicalHalf {d k : ℕ} {I : Type*} [Fintype I] (l m : ℝ) (a : ℂ)
    (x : Fin k → Fin d → ℂ) (F : I → Word d k → ℂ) :=
  mixedHalf (testRows l m (PairResidual.scaled a x) F) (FiveResidualGram.rows a x F)

/-- Equation (8B.4) before dropping the reflected square. The inside edge has
order G,F; the diagonal depends only on F. -/
theorem physical_trace {d k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (hk : 3 ≤ k) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (a : ℂ)
    (x : Fin k → Fin d → ℂ) (hu : energy (PairResidual.scaled a x) = 1)
    (F : I → Word d k → ℂ) (hs : ∀ i, Symmetric (F i)) :
    let H := PairResidual.scaled a x
    let Y := testForm l m H F
    let T := remainderForm H F
    (∑ i, ∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y j i) * T j i).re)) =
      (∑ i, ((Fintype.card I : ℝ) - 1 - 2 * (Y i i).re) * (T i i).re) +
        2 * energy (physicalHalf l m a x F) := by
  dsimp only
  let H := PairResidual.scaled a x
  have htest := test_gram l m hl hm H F
  have hres := FiveResidualGram.rows_gram hk a x hu F hs
  have hdiag (i : I) : star (testForm l m H F i i) = ((testForm l m H F i i).re : ℂ) := by
    rw [← htest]
    simp only [reflected_diag, Complex.ofReal_re, Complex.star_def, Complex.conj_ofReal]
  have h := congrArg Complex.re (mixed_gram (testRows l m H F) (FiveResidualGram.rows a x F))
  rw [htest,hres] at h
  simp only [Complex.re_sum,Complex.ofReal_re] at h
  exact (off_diagonal _ _ hdiag).trans (by rw [← h]; rfl)

/-- The remaining diagonal is nonnegative under the coefficient condition in
Lemma 8B.3, so the off-diagonal sum bounds twice its physical square. -/
theorem physical_trace_lower {d k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (hk : 3 ≤ k) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hq : 2*(l+m) ≤ (Fintype.card I : ℝ) - 1) (a : ℂ)
    (x : Fin k → Fin d → ℂ) (hu : energy (PairResidual.scaled a x) = 1)
    (F : I → Word d k → ℂ) (hs : ∀ i, Symmetric (F i)) (hF : ∀ i, energy (F i) = 1) :
    let H := PairResidual.scaled a x
    let Y := testForm l m H F
    let T := remainderForm H F
    2 * energy (physicalHalf l m a x F) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y j i) * T j i).re) := by
  dsimp only
  rw [physical_trace hk l m hl hm a x hu F hs]
  apply le_add_of_nonneg_left
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · have ht := test_diagonal_le l m hm _ hu F hF i
    linarith
  · rw [← FiveResidualGram.rows_gram hk a x hu F hs]
    rw [reflected_diag, Complex.ofReal_re]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end
end BlockPermanents.FiveMixedSquares
