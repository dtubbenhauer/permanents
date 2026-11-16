import BlockPermanents.BalancedBorder
import BlockPermanents.BalancedExtremes
import BlockPermanents.BalancedEvaluation

/-! # Positivity of the balanced operator on the fixed supported space -/
namespace BlockPermanents.BalancedPositive
open Bend BalancedOpen BalancedPairTrace BalancedExtremes BalancedSupport BalancedRoutes
open BalancedEvaluation SchurNormalization
noncomputable section

private theorem en {I : Type*} [Fintype I] (f : I → ℂ) : 0 ≤ energy f :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem two (a b : ℂ) : Complex.normSq (a+b) ≤ 2*(Complex.normSq a+Complex.normSq b) := by
  have h := Complex.normSq_nonneg (a-b)
  simp only [Complex.normSq_add,Complex.normSq_sub] at *
  linarith

private theorem four (a b c d : ℂ) :
    Complex.normSq (a+b+c+d) ≤ 4*(Complex.normSq a+Complex.normSq b+Complex.normSq c+Complex.normSq d) := by
  rw [add_assoc (a+b)]
  linarith only [two (a+b) (c+d),two a b,two c d]

private theorem single_bound {K : Type*} [Fintype K] (z : Boundary K → ℂ) :
    energy (BalancedPacket.oneSum z) ≤ 4*(energy (L00 z)+energy (L01 z)+energy (L10 z)+energy (L11 z)) := by
  unfold energy BalancedPacket.oneSum
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => four .. 

theorem edge_lower {d k} (hk : 0 < k) (flip : Bool) {U V}
    {z : Boundary (Word d k) → ℂ} (hs : Supported U V z) :
    lastWeight k * (energy (if flip then L01 z else L00 z) +
      energy (if flip then L10 z else L11 z) + 2*Complex.normSq (if flip then Ncross z else Ndirect z))
      ≤ edgeEnergy flip z := by
  rw [← first flip hs,← second flip hs,← full flip hs]
  exact border_sum hk (E flip z) (fun r t => en _) (fun r t =>
    complete_first flip r _ z (wordCap d k k t) (first_supported flip hs)) (fun r t =>
    complete_second flip r t _ z (second_supported flip hs))

/-- Section 6.2: the corrected partial transpose is nonnegative on every
joint state with two symmetric ordinary slots and two symmetric slots
supported on the indicated planes. The two planes have independent bases. -/
theorem operator_positive {d k : ℕ} (hk : 4 ≤ k) (U V : Fin d → Fin k → ℂ)
    (hs : HomogeneousSchur d k k) (hb : HomogeneousSchur d (k+k) (k+k))
    (hp : HomogeneousSchur (Fintype.card (Word d k)) 2 2)
    (z : Boundary (Word d k) → ℂ) (hz : Supported U V z) :
    0 ≤ (quadratic (partialTranspose (BalancedAssembly.marked d k)) z).re := by
  rw [opening (by omega) hs hb hp]
  have lo := edge_lower (by omega : 0<k) false hz
  have hi := edge_lower (by omega : 0<k) true hz
  simp only [Bool.false_eq_true,if_false,if_true] at lo hi
  have extra (f g : (Word d k×Word d k)→ℂ) (n : ℂ) :
      8*(energy f+energy g+2*Complex.normSq n) ≤ lastWeight k*(energy f+energy g+2*Complex.normSq n) :=
    mul_le_mul_of_nonneg_right (eight_le hk) (add_nonneg (add_nonneg (en _) (en _))
      (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
  have l := (extra _ _ _).trans lo
  have r := (extra _ _ _).trans hi
  have hF : 0 ≤ ((k+k).choose k : ℝ)^2 * fineEnergy z :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (en _))
  linarith only [hF,l,r,single_bound z,two (Ndirect z) (Ncross z),Complex.normSq_nonneg (Ndirect z),
    Complex.normSq_nonneg (Ncross z)]

end
end BlockPermanents.BalancedPositive
