import BlockPermanents.FourNativeBoundary
import BlockPermanents.FourNativeTerminal

/-! The full-cap row of Lemma 5C.2 on the four packet clasps. -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourExchangeKernel FourThickCompression FourThickOpenings
open SchurNormalization
open scoped Matrix
noncomputable section

/-- Read the actual marked transfer on rectangular feet fixed by the packet
clasps. The first three operators contain only proper cuts. -/
theorem read_transfer {d k : ℕ} {I J : Type*} [Fintype I]
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (fixed : matrix d k (W d k) * ThreeGeneralOpen.legs M N = ThreeGeneralOpen.legs M N)
    (hk : 0 < k) (h₁ : HomogeneousSchur d k k)
    (h₂ : HomogeneousSchur d (2*k) k) (h₃ : HomogeneousSchur d (3*k) k) :
    read M N (Q d k) =
      (6 : ℚ) • read M N (U d k) + (3 * a k) • read M N (W₂ d k) +
      scale 3 k • read M N (V d k) + terminalSquares M N := by
  rw [← compressed_read M N fixed (Q d k),
    actual_open hk (by simpa only [one_mul] using h₁) h₂ h₃, compressed_read M N fixed]
  exact read_raw M N

/-- The packet-boundary instance has only the three Schur instances of the
manuscript. The boundary matrices are the four individual packet clasps. -/
theorem full_cap_row {d k : ℕ} (hk : 0 < k) (h₁ : HomogeneousSchur d k k)
    (h₂ : HomogeneousSchur d (2*k) k) (h₃ : HomogeneousSchur d (3*k) k) :
    let M := ZeroCap.inner d k 3
    let N := symClasp d k
    read M N (Q d k) =
      (6 : ℚ) • read M N (U d k) + (3 * a k) • read M N (W₂ d k) +
      scale 3 k • read M N (V d k) + terminalSquares M N :=
  read_transfer _ _ (clasps_fixed d k) hk h₁ h₂ h₃

/-- In manuscript notation c = ab, so the corrected square has weight ab². -/
theorem corrected_square_weight (k : ℕ) :
    scale 3 k * b k = ((2*k).choose k : ℚ) * ((3*k).choose k : ℚ)^2 := by
  rw [three_scale]
  simp only [a, b, two_mul, pow_two, mul_assoc]

/-- All four signed coefficients and the internal correction at k = 2. -/
theorem quadratic_weights :
    (scale 3 2 * b 2, 3 * (a 2)^2, (-12 : ℚ), -4 * a 2, (b 2)⁻¹) =
    (1350, 108, -12, -24, 1/15) := by
  decide +kernel

end
end BlockPermanents.FourNative
