import BlockPermanents.BalancedLastPacket
import BlockPermanents.BalancedDivisionGram
import BlockPermanents.BalancedCubicMarcus
import BlockPermanents.VerifiedPaper

/-! The two balanced-cut proofs of Section 6 applied to the original matrix. -/
namespace BlockPermanents.BalancedLast
open Closures Bend BalancedDivision

/-- Average the three supported balanced bends of Lemma 6B.3, and
evaluate their original upright defect on a Gram factor of the given matrix. -/
theorem marcus_thick {k : ℕ} (hk : 4 ≤ k) : MarcusAt 4 k := by
  apply MatchingThreshold.marcusAt_of_gram
  intro x
  have h := defect_nonnegative hk (by omega : k ≤ 4*k) x
  rw [defect_gram, Complex.sub_re] at h
  exact sub_nonneg.mp h

/-- The signed cubic proof, the supported thick proof and the quadratic
and thin cases together cover every positive common block size. -/
theorem marcus_four {k : ℕ} (hk : 0 < k) : MarcusAt 4 k := by
  by_cases h : 4 ≤ k
  · exact marcus_thick h
  have small : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases small with rfl | rfl | rfl
  · exact thickness_one 4
  · exact VerifiedPaper.four_quadratic
  · exact BalancedCubicMarcus.marcus

end BlockPermanents.BalancedLast
