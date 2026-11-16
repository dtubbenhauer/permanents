import BlockPermanents.ThreeVerifyRoutesA
import BlockPermanents.ThreeVerifyRoutesB
import BlockPermanents.ThreeVerifyRoutesC
import BlockPermanents.ThreeVerifyRoutesD
import BlockPermanents.ThreeVerifyTarget

namespace BlockPermanents.ThreeWire

/-- The two nonzero integer coefficient tables agree in all fifteen surviving
routing classes. Each multiplicity is checked at fixed six-wire indices. -/
theorem quadratic_tables : table cyclicTerms = table targetTerms := by
  have r := stepsRoutesD (stepsRoutesC (stepsRoutesB (stepsRoutesA rfl)))
  have t := stepsTarget rfl
  rw [table_at cyclicTerms 48 157 (by decide +kernel),
    table_at targetTerms 24 31 (by decide +kernel), r, t]
  decide

theorem corrected_three_quadratic {f : Wire → ℂ} (hf : PacketInvariant f) :
    evalTerms f cyclicTerms = evalTerms f targetTerms := by
  rw [← table_sound hf, ← table_sound hf, quadratic_tables]

end BlockPermanents.ThreeWire
