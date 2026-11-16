import BlockPermanents.BalancedLastBubble
import BlockPermanents.BalancedTrace
import BlockPermanents.PairResidualProjection

/-! Completing a proper cut when its turned packet lies in a fixed plane. -/
namespace BlockPermanents.BalancedLastTrace
open Bend BalancedSupport BalancedTrace
open scoped Matrix
noncomputable section

variable {d k r : ℕ}

/-- Every turned survivor slice still lies in the symmetric power of the same plane. -/
theorem survivor_mem (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (A : Matrix (Word d k) (Word d k) ℂ) (hs : ∀ w, A w ∈ space k U)
    (w : Word d (k-r)) : (cutMatrix h A) w ∈ space (k-r) U := by
  have hs' {a b : ℕ} (hab : a + b = k) (j : Word d k) (c : Word d b) :
      (fun v => A j (fun i => Fin.append v c (Fin.cast hab.symm i))) ∈ space a U := by
    subst k
    exact slice_mem U (hs j) c
  change (fun v => ∑ c, A (join h w c) (join h v c)) ∈ _
  rw [show (fun v => ∑ c, A (join h w c) (join h v c)) =
       ∑ c, (fun v => A (join h w c) (join h v c)) by ext; simp]
  exact Submodule.sum_mem _ fun c _ => hs' (Nat.sub_add_cancel h) (join h w c) c

/-- Read the marked survivor in an orthonormal basis of its symmetric power. -/
def seam (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (A : Matrix (Word d k) (Word d k) ℂ) :=
  SupportCup.coords (space (k-r) U) (cutMatrix h A).transpose

/-- Remove the component along the trace cup from the partially contracted matrix. -/
def residual (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (A : Matrix (Word d k) (Word d k) ℂ) :=
  (SupportCup.J (space (k-r) U)).mulVec (seam h U A)

/-- Closing the seam recovers the full cap before the cut. -/
theorem close (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (A : Matrix (Word d k) (Word d k) ℂ) (hs : ∀ w, A w ∈ space k U) :
    (SupportCup.cap (space (k-r) U)).mulVec (seam h U A) () = A.trace := by
  rw [seam, SupportCup.close _ (cutMatrix h A).transpose (survivor_mem h U A hs), Matrix.trace_transpose, partial_trace]

/-- Pythagoras on the actual cut, before substituting the dimension of the symmetric power. -/
theorem rank_resolution (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (hr : 0 < SupportCup.Rank (space (k-r) U))
    (A : Matrix (Word d k) (Word d k) ℂ) (hs : ∀ w, A w ∈ space k U) :
    (∑ w, ∑ v, Complex.normSq (cutMatrix h A w v)) =
      energy (residual h U A) + Complex.normSq A.trace / SupportCup.Rank (space (k-r) U) := by
  have he := SupportCup.resolution _ hr (cutMatrix h A).transpose (survivor_mem h U A hs)
  rw [Matrix.trace_transpose, partial_trace] at he
  rw [Finset.sum_comm]
  exact he

/-- The proper cut supplies the full cap divided by the dimension of its symmetric
survivors, and an explicit squared norm from the complement of that cap. -/
theorem resolution (hk : 0 < k) (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (A : Matrix (Word d k) (Word d k) ℂ)
    (hs : ∀ w, A w ∈ space k U) :
    (∑ w, ∑ v, Complex.normSq (cutMatrix h A w v)) =
      energy (residual h U A) + Complex.normSq A.trace / ((k+(k-r)-1).choose (k-r) : ℝ) := by
  have hd := (SupportCup.rank_eq (space (k-r) U)).trans (BalancedLast.dimension (k-r) U hU)
  have hr : 0 < SupportCup.Rank (space (k-r) U) := by
    rw [hd]
    exact Nat.choose_pos (by omega)
  simpa only [hd] using rank_resolution h U hr A hs

/-- Closing the complementary halfweb gives zero. -/
theorem residual_closes (h : r ≤ k) (U : Matrix (Fin d) (Fin k) ℂ)
    (hr : 0 < SupportCup.Rank (space (k-r) U)) (A : Matrix (Word d k) (Word d k) ℂ) :
    (SupportCup.cap (space (k-r) U)).mulVec (residual h U A) = 0 := by
  rw [residual, Matrix.mulVec_mulVec, PairResidual.cap_J _ hr, Matrix.zero_mulVec]

end
end BlockPermanents.BalancedLastTrace
