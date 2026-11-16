import BlockPermanents.BalancedExtremes
import BlockPermanents.BalancedLastTrace

/-! The surviving trace-cup complement on either edge of a balanced pairing.
The map on the opposite edge may be any finite matrix, including an empty
cap, a full cap, or a further proper cut. -/
namespace BlockPermanents.BalancedLastJoint
open Bend BalancedOpen BalancedPairTrace BalancedTrace BalancedSupport BalancedExtremes
open scoped Matrix
noncomputable section

open private otherCap joint_action edge_mem in_fixed from BlockPermanents.BalancedPairTrace

/-- Matrix left on the chosen edge after taking one output of the opposite map. -/
def slice {d k : ℕ} {T : Type*} (flip : Bool) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) (y : T) : Matrix (Word d k) (Word d k) ℂ :=
  otherCap C (z ∘ unpack flip) y

theorem slice_supported {d k : ℕ} {T : Type*} (flip : Bool) (U : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) (C : Matrix T (Word d k × Word d k) ℂ)
    (hz : EdgeSupported U (z ∘ unpack flip)) (y : T) (i : Word d k) :
    slice flip z C y i ∈ space k U :=
  edge_mem _ (C y) _ (fun q => hz.plane q i)

theorem joint_entry {d k : ℕ} {T : Type*} (flip : Bool) (r : CutIndex k k)
    (U : Matrix (Fin d) (Fin k) ℂ) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) (hz : EdgeSupported U (z ∘ unpack flip))
    (w v : Word d (k-r)) (y : T) :
    (productRows flip (wordCap d k k r) C).mulVec z ((w,v),y) =
      cutMatrix (PairBound.cut_le r) (slice flip z C y) w v := by
  rw [joint_action]
  apply partial_action
  · intro i
    exact in_fixed.mp (edge_mem _ (C y) _ (fun q => hz.turned q i))
  · intro j
    exact in_fixed.mp (edge_mem _ (C y) _ (fun q => hz.ordinary q j))

theorem joint_energy {d k : ℕ} {T : Type*} [Fintype T] (flip : Bool) (r : CutIndex k k)
    (U : Matrix (Fin d) (Fin k) ℂ) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) (hz : EdgeSupported U (z ∘ unpack flip)) :
    energy ((productRows flip (wordCap d k k r) C).mulVec z) =
      ∑ y, ∑ w, ∑ v, Complex.normSq (cutMatrix (PairBound.cut_le r) (slice flip z C y) w v) := by
  unfold energy
  rw [Fintype.sum_prod_type_right]
  simp only [Fintype.sum_prod_type, joint_entry flip r U z C hz]

theorem terminal_energy {d k : ℕ} {T : Type*} [Fintype T] (flip : Bool)
    (U : Matrix (Fin d) (Fin k) ℂ) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) (hz : EdgeSupported U (z ∘ unpack flip)) :
    energy ((productRows flip (wordCap d k k (fullCut k)) C).mulVec z) =
      ∑ y, Complex.normSq (slice flip z C y).trace := by
  rw [joint_energy flip _ U z C hz]
  letI : Unique (Word d (k-(fullCut k).val)) := by
    simp only [fullCut, Nat.sub_self]
    infer_instance
  apply Finset.sum_congr rfl
  intro y _
  have h := partial_trace (PairBound.cut_le (fullCut k)) (slice flip z C y)
  simpa [Matrix.trace, Matrix.diag] using congrArg Complex.normSq h

/-- The sum of squared complementary halfwebs, one for each spectator output. -/
def jointSquares {d k : ℕ} {T : Type*} [Fintype T] (flip : Bool) (r : CutIndex k k)
    (U : Matrix (Fin d) (Fin k) ℂ) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) : ℝ :=
  ∑ y, energy (BalancedLastTrace.residual (PairBound.cut_le r) U (slice flip z C y))

theorem jointSquares_nonneg {d k : ℕ} {T : Type*} [Fintype T] (flip : Bool) (r : CutIndex k k)
    (U : Matrix (Fin d) (Fin k) ℂ) (z : Boundary (Word d k) → ℂ)
    (C : Matrix T (Word d k × Word d k) ℂ) : 0 ≤ jointSquares flip r U z C :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Complete the first cap while keeping the linear map on the other edge fixed. -/
theorem joint_split {d k : ℕ} {T : Type*} [Fintype T] (hk : 0 < k)
    (flip : Bool) (r : CutIndex k k) (U : Matrix (Fin d) (Fin k) ℂ) (hU : Uᴴ * U = 1)
    (z : Boundary (Word d k) → ℂ) (C : Matrix T (Word d k × Word d k) ℂ)
    (hz : EdgeSupported U (z ∘ unpack flip)) :
    energy ((productRows flip (wordCap d k k r) C).mulVec z) =
      energy ((productRows flip (wordCap d k k (fullCut k)) C).mulVec z) /
        ((k+(k-r)-1).choose (k-r) : ℝ) + jointSquares flip r U z C := by
  rw [joint_energy flip r U z C hz, terminal_energy flip U z C hz, Finset.sum_div]
  unfold jointSquares
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  conv_rhs => rw [add_comm]
  exact BalancedLastTrace.resolution hk (PairBound.cut_le r) U hU (slice flip z C y)
    (slice_supported flip U z C hz y)

/-- Complement on the first edge of the crossing pairing. -/
def firstSquares {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) (r t : CutIndex k k) : ℝ :=
  jointSquares flip r (if flip then V else U) z (wordCap d k k t)

/-- Complement on the second edge, using its own turned packet's plane. -/
def secondSquares {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) (r t : CutIndex k k) : ℝ :=
  jointSquares flip t (if flip then U else V) (reverse flip z) (wordCap d k k r)

theorem firstSquares_nonneg {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) (r t : CutIndex k k) : 0 ≤ firstSquares flip U V z r t :=
  jointSquares_nonneg ..

theorem secondSquares_nonneg {d k : ℕ} (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (z : Boundary (Word d k) → ℂ) (r t : CutIndex k k) : 0 ≤ secondSquares flip U V z r t :=
  jointSquares_nonneg ..

theorem first_split {d k : ℕ} (hk : 0 < k) (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (z : Boundary (Word d k) → ℂ)
    (hz : Supported U V z) (r t : CutIndex k k) :
    E flip z r t = E flip z (fullCut k) t / ((k+(k-r)-1).choose (k-r) : ℝ) +
      firstSquares flip U V z r t :=
  joint_split hk flip r _ (by cases flip <;> assumption) z _ (first_supported flip hz)

theorem second_split {d k : ℕ} (hk : 0 < k) (flip : Bool) (U V : Matrix (Fin d) (Fin k) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (z : Boundary (Word d k) → ℂ)
    (hz : Supported U V z) (r t : CutIndex k k) :
    E flip z r t = E flip z r (fullCut k) / ((k+(k-t)-1).choose (k-t) : ℝ) +
      secondSquares flip U V z r t := by
  unfold E productCap
  rw [energy_reverse flip _ _ z, energy_reverse flip _ _ z]
  exact joint_split hk flip t _ (by cases flip <;> assumption) (reverse flip z) _
    (second_supported flip hz)

end
end BlockPermanents.BalancedLastJoint
