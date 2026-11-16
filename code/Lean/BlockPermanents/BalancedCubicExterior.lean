import BlockPermanents.CubicSquares
import BlockPermanents.TwoStep

/-! Exterior squares of the four crossing packet pairs in Theorem 6C.3. -/
namespace BlockPermanents.BalancedCubicExterior
open Bend Closures BalancedCoarse BalancedSigned CubicSquares
open scoped ComplexConjugate
noncomputable section

/-- In the determinant metric the two orders of a coordinate pair contribute
the same squared minor. The factor one half counts the pair once. -/
def wedgeEnergy {D : Type*} [Fintype D] (u v : D → ℂ) : ℝ :=
  (∑ i, ∑ j, Complex.normSq (u i * v j - u j * v i)) / 2

theorem gram_determinant {D : Type*} [Fintype D] (u v : D → ℂ) :
    energy u * energy v - Complex.normSq (bracket u v) = wedgeEnergy u v := by
  have h := TwoStep.path_square Finset.univ (fun i => conj (u i)) v
  simp only [← map_mul, ← map_sub, Complex.normSq_conj, ← Finset.mul_sum, ← Finset.sum_mul] at h
  simp only [Complex.normSq_mul, ← Finset.mul_sum, ← Finset.sum_mul] at h
  unfold energy bracket wedgeEnergy
  linarith only [h]

/-- The four wedges in the division with ordinary packets zero and one. -/
def crossingWedges {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) : ℝ :=
  wedgeEnergy (X 0) (X 2) + wedgeEnergy (X 0) (X 3) +
  wedgeEnergy (X 1) (X 2) + wedgeEnergy (X 1) (X 3)

theorem crossing_exterior {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ)
    (h : ∀ i, energy (X i) = 1) : 4 - crossing X = crossingWedges X := by
  have pair (i j) : 1 - BalancedCut.sq X i j = wedgeEnergy (X i) (X j) := by
    simpa only [h, one_mul, BalancedCut.sq] using gram_determinant (X i) (X j)
  unfold crossing crossingWedges
  linarith only [pair 0 2, pair 0 3, pair 1 2, pair 1 3]

/-- The signed cubic certificate with the four determinant squares inserted. -/
theorem signedSquares_exterior {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ)
    (h : ∀ i, energy (X i) = 1) :
    let U := leftSide X
    let V := rightSide X
    let α := caps U V
    signedSquares X =
      energy ((survivors U V * phases).mulVec α) +
      energy ((residual (1/2) (bracket (U 1) (U 0)) (star (bracket (V 1) (V 0)))).mulVec α) +
      Complex.normSq (α 0 * α 3 - α 1 * α 2) + 4 * internal X * crossingWedges X := by
  dsimp only
  unfold signedSquares
  rw [crossing_exterior X h]

end
end BlockPermanents.BalancedCubicExterior
