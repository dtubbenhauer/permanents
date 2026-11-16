import BlockPermanents.FiveProjection
import BlockPermanents.PairResidualOperator

/-! The reflected halves giving the five-packet mixed remainder in (8A.4). -/
namespace BlockPermanents.FiveResidualGram
open Bend Closures PairResidual Support
open scoped BigOperators Matrix
noncomputable section

variable {d k : ℕ} {I : Type*}

def columns (y : I → Word d k → ℂ) : Matrix (Word d k) I ℂ := fun w i => y i w

/-- The full cap closed against each column. -/
def full (a : ℂ) (x : Fin k → Fin d → ℂ) (y : I → Word d k → ℂ) :=
  PairSquares.pairingRow (scaled a x) * columns y

/-- An actual orthogonal trace-cup complement acting on the whole family. -/
def cut (a : ℂ) (x : Fin k → Fin d → ℂ) (y : I → Word d k → ℂ) (r : CutIndex k k) :=
  residualMatrix a x r * columns y

def excess (x : Fin k → Fin d → ℂ) (r : CutIndex k k) : ℝ :=
  (k.choose r : ℝ)^2 / rank x r - k.choose r

open private gram_cols tested_gram product_gram from BlockPermanents.FiveProjection in
/-- The matrix of mixed entries of the remainder: the nonzero cuts of Lemma
7A.1 and the unused full-cap coefficient after reserving seven copies. -/
theorem remainder_gram [Fintype I] (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hu : energy (scaled a x) = 1) (y : I → Word d k → ℂ) (hy : ∀ i, Symmetric (y i)) :
    FiveProjection.remainderForm (scaled a x) y =
      ((2:ℂ)^k - 8) • reflected (full a x y) +
      ∑ r ∈ Finset.univ.erase (zeroCut k),
        ((k.choose r : ℂ)^2 • reflected (cut a x y r) +
          (excess x r : ℂ) • reflected (full a x y)) := by
  let H := scaled a x
  let A := PairBound.symmetricProductMatrix H * columns y
  have hform : FiveProjection.remainderForm H y =
      ((k+k).choose k : ℂ) • reflected A - reflected (columns y) -
        (7 : ℂ) • reflected (full a x y) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show reflected A i j = _ from product_gram H y i j,
      show reflected (columns y) i j = _ from gram_cols y i j,
      show reflected (full a x y) i j = _ from tested_gram H y i j]
    simp [FiveProjection.remainderForm, FiveProjection.pairGram, mul_assoc]
  change FiveProjection.remainderForm H y = _
  rw [hform]
  have h := full_caps_residual_operator a x hu (columns y) hy
  simp only [excess, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  change _ = _ + ∑ r ∈ Finset.univ.erase (zeroCut k),
    ((k.choose r : ℂ)^2 • reflected (residualMatrix a x r * columns y) +
    ((k.choose r : ℂ)^2 / (rank x r : ℂ) - k.choose r) • reflected (PairSquares.pairingRow H * columns y))
  rw [← h]
  change _ = ((2:ℂ)^k - 8) • reflected (full a x y) + (((k+k).choose k : ℂ) •
    reflected A - reflected (columns y) - ((2:ℂ)^k - 1) • reflected (full a x y))
  module

abbrev Cuts (k : ℕ) := ↥(Finset.univ.erase (zeroCut k))
abbrev Index (x : Fin k → Fin d → ℂ) :=
  Unit ⊕ (Σ r : Cuts k, SupportCup.Seam (space x r.val) ⊕ Unit)

private def stack {J K : Type*} (M : Matrix J I ℂ) (N : Matrix K I ℂ) :
    Matrix (J ⊕ K) I ℂ := Sum.elim M N

private theorem stack_gram {J K : Type*} [Fintype J] [Fintype K]
    (M : Matrix J I ℂ) (N : Matrix K I ℂ) :
    reflected (stack M N) = reflected M + reflected N := by
  ext i j
  simp only [reflected, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, stack, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply]

private def collect {R : Type*} {J : R → Type*} (M : (r : R) → Matrix (J r) I ℂ) :
    Matrix (Σ r, J r) I ℂ := fun u => M u.1 u.2

private theorem collect_gram {R : Type*} [Fintype R] {J : R → Type*} [∀ r, Fintype (J r)]
    (M : (r : R) → Matrix (J r) I ℂ) : reflected (collect M) = ∑ r, reflected (M r) := by
  ext i j
  simp only [reflected, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sigma,
    collect, Matrix.sum_apply]

private theorem scale_gram {J : Type*} [Fintype J] (c : ℝ) (M : Matrix J I ℂ) :
    reflected ((c : ℂ) • M) = ((c : ℂ)^2) • reflected M := by
  simp only [reflected, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

private theorem sqrt_gram {J : Type*} [Fintype J] (c : ℝ) (hc : 0 ≤ c) (M : Matrix J I ℂ) :
    reflected ((Real.sqrt c : ℂ) • M) = (c : ℂ) • reflected M := by
  rw [scale_gram, ← Complex.ofReal_pow, Real.sq_sqrt hc]

/-- One output for the extra full cap, followed by each nonzero cut's
perpendicular seam and its unused trace component. -/
def rows (a : ℂ) (x : Fin k → Fin d → ℂ) (y : I → Word d k → ℂ) : Matrix (Index x) I ℂ :=
  stack ((Real.sqrt ((2:ℝ)^k - 8) : ℂ) • full a x y) (collect (fun r : Cuts k =>
    stack ((k.choose r.val : ℂ) • cut a x y r.val)
      ((Real.sqrt (excess x r.val) : ℂ) • full a x y)))

/-- The mixed remainder is the Gram matrix of the explicit stacked halfweb
outputs, with their original seam coordinates retained. -/
theorem rows_gram [Fintype I] (hk : 3 ≤ k) (a : ℂ) (x : Fin k → Fin d → ℂ)
    (hu : energy (scaled a x) = 1) (y : I → Word d k → ℂ) (hy : ∀ i, Symmetric (y i)) :
    reflected (rows a x y) = FiveProjection.remainderForm (scaled a x) y := by
  have hpow : 0 ≤ (2 : ℝ)^k - 8 := by
    have hb : (2 : ℝ)^3 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    linarith
  have he (r : CutIndex k k) : 0 ≤ excess x r :=
    surplus_nonneg x r (rank_pos x (packet_ne_zero_of_unit hu) r)
  rw [rows, stack_gram, collect_gram, sqrt_gram _ hpow, remainder_gram a x hu y hy]
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  rw [← Finset.sum_attach (Finset.univ.erase (zeroCut k))]
  apply Finset.sum_congr rfl
  intro r _
  rw [stack_gram, sqrt_gram _ (he _)]
  exact_mod_cast congrArg (· + (excess x r.val : ℂ) • reflected (full a x y))
    (scale_gram (k.choose r.val : ℝ) (cut a x y r.val))

end
end BlockPermanents.FiveResidualGram
