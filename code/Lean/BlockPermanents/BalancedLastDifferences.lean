import BlockPermanents.BalancedPositive

/-! Difference squares of the four edge routes and two matching routes in Section 6B. -/
namespace BlockPermanents.BalancedLastDifferences
open Bend BalancedRoutes
noncomputable section

variable {I K : Type*} [Fintype I] [Fintype K]

/-- One term for every unordered pair of crossing edges. -/
def sixDifferences (a b c d : I → ℂ) : ℝ :=
  energy (a-b) + energy (a-c) + energy (a-d) +
  energy (b-c) + energy (b-d) + energy (c-d)

private theorem four_pointwise (a b c d : ℂ) :
    4*(Complex.normSq a + Complex.normSq b + Complex.normSq c + Complex.normSq d) -
      Complex.normSq (a+b+c+d) =
    Complex.normSq (a-b) + Complex.normSq (a-c) + Complex.normSq (a-d) +
      Complex.normSq (b-c) + Complex.normSq (b-d) + Complex.normSq (c-d) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

theorem four_differences (a b c d : I → ℂ) :
    4*(energy a + energy b + energy c + energy d) -
      energy (a+b+c+d) = sixDifferences a b c d := by
  simp only [energy,sixDifferences,Pi.add_apply,Pi.sub_apply,← Finset.sum_add_distrib,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => four_pointwise (a i) (b i) (c i) (d i)

/-- The two completed pairings contribute one difference square. -/
theorem two_differences (a b : ℂ) :
    2*(Complex.normSq a + Complex.normSq b) - Complex.normSq (a+b) =
      Complex.normSq (a-b) := by
  rw [Complex.normSq_add,Complex.normSq_sub]
  ring

def edgeDiagonal (z : BalancedPacket.Boundary K → ℂ) : ℝ :=
  energy (L00 z) + energy (L01 z) + energy (L10 z) + energy (L11 z)

def matchingDiagonal (z : BalancedPacket.Boundary K → ℂ) : ℝ :=
  Complex.normSq (Ndirect z) + Complex.normSq (Ncross z)

/-- After extracting L/2 at every edge and L at every matching, retain both
the difference squares and the unused diagonal weights. -/
theorem completed_routes (L : ℝ) (z : BalancedPacket.Boundary K → ℂ) :
    L/2 * edgeDiagonal z + L * matchingDiagonal z -
        energy (BalancedPacket.oneSum z) - Complex.normSq (Ndirect z + Ncross z) =
      sixDifferences (L00 z) (L01 z) (L10 z) (L11 z) +
        Complex.normSq (Ndirect z - Ncross z) +
        (L/2 - 4) * edgeDiagonal z + (L - 2) * matchingDiagonal z := by
  have hedge : 4 * edgeDiagonal z - energy (BalancedPacket.oneSum z) =
      sixDifferences (L00 z) (L01 z) (L10 z) (L11 z) :=
    four_differences _ _ _ _
  have hmatch : 2 * matchingDiagonal z - Complex.normSq (Ndirect z + Ncross z) =
      Complex.normSq (Ndirect z - Ncross z) :=
    two_differences _ _
  rw [← hedge, ← hmatch]
  ring

private theorem energy_nonneg (u : I → ℂ) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem sixDifferences_nonneg (a b c d : I → ℂ) : 0 ≤ sixDifferences a b c d := by
  unfold sixDifferences
  linarith only [energy_nonneg (a-b), energy_nonneg (a-c), energy_nonneg (a-d),
    energy_nonneg (b-c), energy_nonneg (b-d), energy_nonneg (c-d)]

theorem unused_diagonals_nonneg {k : ℕ} (hk : 4 ≤ k) (z : BalancedPacket.Boundary K → ℂ) :
    0 ≤ (BalancedSupport.lastWeight k / 2 - 4) * edgeDiagonal z ∧
    0 ≤ (BalancedSupport.lastWeight k - 2) * matchingDiagonal z := by
  have h := BalancedSupport.eight_le hk
  constructor
  · apply mul_nonneg (by linarith)
    unfold edgeDiagonal
    solve_by_elim (maxDepth := 10) only [add_nonneg, energy_nonneg]
  · apply mul_nonneg (by linarith)
    unfold matchingDiagonal
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

end
end BlockPermanents.BalancedLastDifferences
