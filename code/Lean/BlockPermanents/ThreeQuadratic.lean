import BlockPermanents.ThreeCertificate
import BlockPermanents.ThreeMarked

/-! # The permanent inequality for three quadratic packets -/

namespace BlockPermanents
open ThreeWire ThreeEndpoint Closures

/-- No external source is required for this finite wire calculation.
The Gram dimension is arbitrary and each of the three packets comes from its
two columns; in particular there is no unit-vector or rank assumption. -/
theorem three_quadratic_gram {d : ℕ} (x : Fin 3 → Fin 2 → Fin d → ℂ) :
    0 ≤ (evalTerms (evaluateWord (bdy (fun i => packet (x i)))) targetTerms).re := by
  let f := evaluateWord (bdy (fun i => packet (x i)))
  have hi : PacketInvariant f := boundary_invariant
    (Bridges.packet_symmetric _ _ (x 0)) (Bridges.packet_symmetric _ _ (x 1))
    (Bridges.packet_symmetric _ _ (x 2))
  change 0 ≤ (evalTerms f targetTerms).re
  rw [← corrected_three_quadratic hi]
  exact ThreeMarked.cyclic_nonneg x

/-- The matrix endpoint includes every Hermitian positive semidefinite 6×6
complex matrix split into 3×3 quadratic blocks. -/
theorem marcus_three_quadratic : MarcusAt 3 2 :=
  marcus_of_gram_positive three_quadratic_gram

end BlockPermanents
