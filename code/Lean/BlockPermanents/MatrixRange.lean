import BlockPermanents.ThreeQuadratic
import BlockPermanents.FiveMain
import BlockPermanents.MainResults

/-! # Matrix endpoints of the paper -/
namespace BlockPermanents
open SchurNormalization

/-- Three packets of arbitrary positive thickness. The exceptional quadratic
case uses a six-strand certificate and requires no external result. -/
theorem marcus_three_all {k : ℕ} (hk : 1 ≤ k) (schur : ∀ p q, HomogeneousSchur (3*k) p q) :
    MarcusAt 3 k := by
  by_cases h1 : k=1
  · subst k; exact thickness_one _
  by_cases h2 : k=2
  · subst k; exact marcus_three_quadratic
  exact marcus_three (by omega) (schur _ _) (schur _ _)

/-- All matrix ranges of Theorem 1A.1 except the four-quadratic case. -/
theorem matrix_range {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hr : m ≤ 4 ∨ (m=5 ∧ 3 ≤ k) ∨ (2 ≤ m ∧ m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1)))
    (h42 : (m,k) ≠ (4,2)) (schur : ∀ p q, HomogeneousSchur (m*k) p q) :
    MarcusAt m k := by
  rcases hr with h|⟨rfl,h⟩|⟨_,h⟩
  · by_cases h1 : m=1
    · subst m; exact one_packet _
    by_cases h2 : m=2
    · subst m
      apply marcus_two hk
      simpa [two_mul] using schur k k
    by_cases h3 : m=3
    · subst m; exact marcus_three_all hk schur
    obtain rfl : m=4 := by omega
    by_cases h1 : k=1
    · subst k; exact thickness_one _
    have h2 : k ≠ 2 := fun e => h42 (e ▸ rfl)
    exact MatchingThreshold.four_blocks (by omega) schur
  · exact FiveMain.marcus_five h schur
  · exact MatchingThreshold.marcus_threshold h schur

end BlockPermanents
