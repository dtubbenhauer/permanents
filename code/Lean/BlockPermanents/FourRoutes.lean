import BlockPermanents.FourBend
import BlockPermanents.ThreeTransfer
import BlockPermanents.SchurNormalization
import Mathlib.Algebra.BigOperators.Fin

/-! # The one-, two-, and three-packet proper cut families

A spectator label specifies a slice of the merge matrix. Opening the total
clasp on each slice gives a genuine matrix square for every cap number.
The specialization below constructs all three merges on the same three-packet
input, with its normalized horizontal packet symmetrizer.
-/
namespace BlockPermanents.FourRoutes
open Bend ThreeTransfer SchurNormalization
open scoped BigOperators Matrix
noncomputable section

variable {A S : Type*} [Fintype S]

/-- For a spectator output `s`, merge one group of ordinary cables, open
the total clasp with the marked packet, and close the ordinary merge. -/
def opening (d p k : ℕ) (M : S → Matrix (Word d p) A ℂ) :=
  ∑ s, upright (M s)ᴴ * totalClasp d p k * upright (M s)

/-- A routed half: the visible spectators pass through while the two active
cables undergo the standard contraction. -/
def route (d p k : ℕ) (M : S → Matrix (Word d p) A ℂ) (r : CutIndex p k) (s : S) :=
  wordCap d p k r * upright (M s)

private lemma upright_star {T U K : Type*} [DecidableEq K] (F : Matrix T U ℂ) :
    (upright (K := K) F)ᴴ = upright Fᴴ := by
  ext ⟨i,j⟩ ⟨a,b⟩
  by_cases h : j=b <;> simp [upright, Matrix.conjTranspose_apply, h, Ne.symm]

/-- Opening a merge with arbitrary spectators, as an exact identity of
matrices on entangled inputs. -/
theorem open_routes (d p k : ℕ) (h : HomogeneousSchur d p k) (M : S → Matrix (Word d p) A ℂ) :
    (((p+k).choose p : ℂ) • partialTranspose (opening d p k M)) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • ∑ s, (route d p k M r s)ᴴ * route d p k M r s := by
  classical
  have hsch : ((p+k).choose p : ℂ) • partialTranspose (totalClasp d p k) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • ((wordCap d p k r)ᴴ*(wordCap d p k r)) := by
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply] using
      bent_schur d p k (homogeneousSchur_implies_unbent _ _ _ h) i j
  have hsum : partialTranspose (opening d p k M) =
      ∑ s, upright (M s)ᴴ * partialTranspose (totalClasp d p k) * upright (M s) := by
    simp_rw [← show ∀ s, partialTranspose (upright (M s)ᴴ * totalClasp d p k * upright (M s)) =
       upright (M s)ᴴ * partialTranspose (totalClasp d p k) * upright (M s) from
       fun s => bend_sandwich _ _ _]
    ext i j; simp only [partialTranspose, opening, Matrix.sum_apply]
  have hs (s : S) : ((p+k).choose p : ℂ) • (upright (M s)ᴴ * partialTranspose (totalClasp d p k) * upright (M s)) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • ((route d p k M r s)ᴴ * route d p k M r s) := by
    calc
      _ = upright (M s)ᴴ * (((p+k).choose p : ℂ) • partialTranspose (totalClasp d p k)) * upright (M s) :=
        by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by rw [hsch, Matrix.mul_sum, Matrix.sum_mul]; simp only [route, Matrix.conjTranspose_mul,
                  upright_star, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hsum, Finset.smul_sum]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

/-- Ordinary boundary of the marked operator, before bending packet four. -/
abbrev Triple (d k : ℕ) := Fin 3 → Word d k
abbrev Spectator (d k n : ℕ) := Fin (3-n) → Word d k

private def idleIndex (n : ℕ) (j : Fin (3-n)) : Fin 3 := ⟨j, by omega⟩
private def activeIndex (n : ℕ) (hn : n ≤ 3) (j : Fin n) : Fin 3 := ⟨3-n+j, by omega⟩

/-- Merge the last `n` ordinary packets after averaging the order of all
three. The kernel includes the orthogonal symmetric projector on the
`n*k` active strands and identity wires on the remaining packet labels. -/
def merge (d k n : ℕ) (hn : n ≤ 3) (s : Spectator d k n) : Matrix (Word d (n*k)) (Triple d k) ℂ :=
  fun w x => (6:ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin 3),
    if (fun j => x (σ (idleIndex n j))) = s then
      symClasp d (n*k) w (fun t => let ij : Fin n × Fin k := finProdFinEquiv.symm t
                         x (σ (activeIndex n hn ij.1)) ij.2)
    else 0

/-- The three concrete half diagrams in 5C, indexed by `n=1,2,3`. The
spectator word and the two through-word parts are precisely their free ends. -/
def capHalf (d k n : ℕ) (hn : n ≤ 3) (r : CutIndex (n*k) k) :=
  route d (n*k) k (merge d k n hn) r

/-- All three cable sizes share this opening, on the same entangled marked
input space. The outer scalar absorbs the digon normalization. -/
theorem three_openings (d k n : ℕ) (hn : n ≤ 3) (h : HomogeneousSchur d (n*k) k) :
    (((n*k+k).choose (n*k) : ℂ) • partialTranspose (opening d (n*k) k (merge d k n hn))) =
      ∑ r : CutIndex (n*k) k, (weight (n*k) k r : ℂ) •
        ∑ s, (capHalf d k n hn r s)ᴴ * capHalf d k n hn r s :=
  open_routes d (n*k) k h _

/-- Coefficients on the three quadratic proper cuts, before taking their
sum of reflected squares. -/
theorem proper_weights : 6 * weight 2 2 1 = 24 ∧
    3 * ((4:ℕ).choose 2) * weight 4 2 1 = 144 ∧
    (((4:ℕ).choose 2)*((6:ℕ).choose 2)) * weight 6 2 1 = 1080 := by decide

end
end BlockPermanents.FourRoutes
