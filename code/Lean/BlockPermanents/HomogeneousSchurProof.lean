import BlockPermanents.SchurAverage
import BlockPermanents.SchurWireCriterion

namespace BlockPermanents.SchurNormalization

/-- The homogeneous exchange on symmetric word matrices, for every alphabet and
both packet sizes, including the cases where a packet is empty. -/
theorem homogeneousSchur (d p q : ℕ) : HomogeneousSchur d p q :=
  SchurWireCriterion.of_operator (SchurAverage.wire_identity d p q)

end BlockPermanents.SchurNormalization
