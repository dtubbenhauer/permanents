import BlockPermanents.ThreeVerifyRaw
import BlockPermanents.ThreeVerifyFixed
import BlockPermanents.ThreeMarked

namespace BlockPermanents.ThreeWire
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The unaveraged raw square identity at thickness two, with the marked
packet fixed. The target includes both negative correction terms of Q₃. -/
theorem fixed_transfer_quadratic {f : Wire → ℂ} (hf : PacketInvariant f) :
    evalTerms f fixedMarkedTerms = evalTerms f correctionTerms := by
  rw [← table_sound hf, ← table_sound hf]
  apply congrArg (evalBins f)
  rw [table_at correctionTerms 48 27 (by decide +kernel),
    table_at fixedMarkedTerms 48 22 (by decide +kernel), stepsRaw rfl, stepsFixed rfl]
  decide

/-- Fixed-mark positivity on matrix packets, independently of the three
cyclic choices used by the global permanent inequality. -/
theorem fixed_transfer_positive {d : ℕ} (x y z : Fin 2 → Fin d → ℂ) :
    0 ≤ (evalTerms (evaluateWord (boundary (Closures.packet x) (Closures.packet y) (Closures.packet z)))
      fixedMarkedTerms).re := by
  have hi := boundary_invariant (Bridges.packet_symmetric _ _ x) (Bridges.packet_symmetric _ _ y)
    (Bridges.packet_symmetric _ _ z)
  rw [fixed_transfer_quadratic hi]
  exact ThreeMarked.correction_nonneg x y z

end BlockPermanents.ThreeWire
