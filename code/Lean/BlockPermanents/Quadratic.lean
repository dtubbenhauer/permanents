import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The one-cap square, from the permanent of a four-by-four Gram matrix.
The Gram space may have any finite dimension. -/
namespace BlockPermanents.Quadratic

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

/-- Expand the first column, retaining the order given by the transposition (0,j). -/
theorem permanent_succ {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    A.permanent = ∑ j, A j 0 *
      (Matrix.of (fun u v : Fin n => A (Equiv.swap 0 j u.succ) v.succ)).permanent := by
  classical
  unfold Matrix.permanent
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp (fun σ => ∏ i, A (σ i) i),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fin.prod_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Matrix.of_apply]

variable {D : Type*} [Fintype D]

/-- The paper takes the first entry of an inner product conjugate-linearly. -/
def pair (a b : D → ℂ) : ℂ := ∑ t, conj (a t) * b t

theorem pair_conj (a b : D → ℂ) : conj (pair a b) = pair b a := by
  simp [pair, map_sum, mul_comm]

/-- Coordinates of the Gram matrix of four vectors in their given order. -/
def gram4 (x : Fin 4 → D → ℂ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => pair (x i) (x j)

/-- Position of the t-th strand of packet i in the two-packet ordering. -/
def strand (i t : Fin 2) : Fin 4 := ⟨2*i.val+t.val, by omega⟩

def blockMatrix (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (A.submatrix (strand i) (strand j)).permanent

/-- A finite sum of rank-one matrices written in the free-end coordinates. -/
def mixed {L : Type*} [Fintype L] (left right : L → D → ℂ) (w : L → ℂ)
    (i j : D) : ℂ := ∑ s, w s * left s i * conj (right s j)

omit [Fintype D] in
private theorem mixed_entry {L : Type*} [Fintype L] (a b : L → D → ℂ) (w : L → ℂ) (i j : D) :
    conj (mixed a b w i j) * mixed a b w i j =
    ∑ r, ∑ s, (conj (w r) * w s) * (conj (a r i) * a s i) * (conj (b s j) * b r j) := by
  simp only [mixed, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring

theorem mixed_square {L : Type*} [Fintype L] (a b : L → D → ℂ) (w : L → ℂ) :
    (∑ i, ∑ j, (Complex.normSq (mixed a b w i j) : ℂ)) =
    ∑ r, ∑ s, conj (w r) * w s * pair (a r) (a s) * pair (b s) (b r) := by
  simp_rw [Complex.normSq_eq_conj_mul_self, mixed_entry]
  calc
    _ = ∑ r, ∑ s, ∑ i, ∑ j, (conj (w r) * w s) * (conj (a r i) * a s i) *
        (conj (b s j) * b r j) := by
          conv_lhs => enter [2,i]; rw [Finset.sum_comm]; enter [2,r]; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      simp only [pair, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private def leftLeg : Fin 4 → Fin 4 := ![0,0,1,1]
private def rightLeg : Fin 4 → Fin 4 := ![2,3,2,3]
private def otherLeft : Fin 4 → Fin 4 := ![1,1,0,0]
private def otherRight : Fin 4 → Fin 4 := ![3,2,3,2]

/-- Twice the normalized one-cap halfweb in its free-end coordinates.
Each ordered choice leaves one strand from each packet free. -/
def capNumerator (x : Fin 4 → D → ℂ) (i j : D) : ℂ :=
  mixed (fun r => x (leftLeg r)) (fun r => x (rightLeg r))
    (fun r => pair (x (otherRight r)) (x (otherLeft r))) i j

private theorem gap_expansion (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.permanent - (blockMatrix A).permanent =
    ∑ r, ∑ s, A (otherLeft r) (otherRight r) * A (otherRight s) (otherLeft s) *
      A (leftLeg r) (leftLeg s) * A (rightLeg s) (rightLeg r) := by
  classical
  simp only [blockMatrix, permanent_succ, Matrix.permanent_isEmpty, Matrix.of_apply,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    mul_one]
  norm_num [leftLeg, rightLeg, otherLeft, otherRight, strand, Equiv.swap_apply_def,
    Fin.succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [show (2 : Fin 4) = ⟨2, by decide⟩ from rfl,
    show (3 : Fin 4) = ⟨3, by decide⟩ from rfl]
  ring

/-- The fine permanent minus the packet permanent is the square of the
unnormalized one-cap halfweb. All four columns are arbitrary. -/
theorem gram_gap_square (x : Fin 4 → D → ℂ) :
    (gram4 x).permanent - (blockMatrix (gram4 x)).permanent =
      ∑ i, ∑ j, (Complex.normSq (capNumerator x i j) : ℂ) := by
  unfold capNumerator
  rw [gap_expansion, mixed_square]
  simp only [gram4, pair_conj]


/-- Contract the two symmetric quadratic packets on their common thin index.
Each matrix packet is the sum of its two orders divided by √2, giving 1/2
for the pair of packets. The indices i and j are the two free ends. -/
def singleCap (x : Fin 4 → D → ℂ) (i j : D) : ℂ :=
  (∑ t, (x 0 i * x 1 t + x 1 i * x 0 t) *
    conj (x 2 j * x 3 t + x 3 j * x 2 t)) / 2

theorem twice_singleCap (x : Fin 4 → D → ℂ) (i j : D) :
    capNumerator x i j = 2 * singleCap x i j := by
  unfold singleCap
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℂ) ≠ 0)]
  simp [capNumerator, mixed, Fin.sum_univ_succ, leftLeg, rightLeg, otherLeft, otherRight,
    pair, Finset.sum_mul, ← Finset.sum_add_distrib, map_add, map_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Lemma 1B.2, in the matrix packet normalization of the paper. -/
theorem four_times_one_cap (x : Fin 4 → D → ℂ) :
    (gram4 x).permanent - (blockMatrix (gram4 x)).permanent =
      ((4 * ∑ i, ∑ j, Complex.normSq (singleCap x i j) : ℝ) : ℂ) := by
  rw [gram_gap_square]
  simp_rw [twice_singleCap, Complex.normSq_mul, Complex.normSq_ofNat]
  norm_num only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_ofNat]
  simp only [Finset.mul_sum]

/-- The two-by-two block case for every Hermitian PSD matrix, including singular matrices. -/
theorem psd_gap (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    ∃ s : ℝ, 0 ≤ s ∧ A.permanent - (blockMatrix A).permanent = (s : ℂ) := by
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  let x (i t : Fin 4) := B t i
  have h : A = gram4 x := by rw [hB]; rfl
  rw [h]
  exact ⟨_, mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (singleCap x i j)), four_times_one_cap x⟩

theorem psd_inequality (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) :
    (blockMatrix A).permanent.re ≤ A.permanent.re := by
  obtain ⟨s, hs, h⟩ := psd_gap A hA
  have he := congrArg Complex.re h
  rw [Complex.sub_re, Complex.ofReal_re] at he
  exact sub_nonneg.mp (he ▸ hs)

end
end BlockPermanents.Quadratic
