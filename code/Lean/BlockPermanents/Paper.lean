import BlockPermanents.MatrixRange
import BlockPermanents.FourMatrix

/-! # The full matrix theorem of the manuscript -/
namespace BlockPermanents
open SchurNormalization

/-- Theorem 1A.1 on the permanent of a complex positive semidefinite block matrix. -/
theorem manuscript_theorem (schur : ∀ d p q, HomogeneousSchur d p q) : ManuscriptTheorem := by
  intro m k hm hk hr
  by_cases h : (m,k) = (4,2)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    exact FourMatrix.marcus_four_quadratic (fun d => schur d 2 2) (fun d => schur d 4 2) (fun d => schur d 6 2)
  · exact matrix_range hm hk hr h (schur _)

end BlockPermanents
