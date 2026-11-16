import BlockPermanents.ThreeMarkedMatrix
import BlockPermanents.ThreeGram

/-! Marcus’s inequality for three packets by the supported marked bend. -/
namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen SchurNormalization
open scoped BigOperators Matrix
noncomputable section

/-- The proof chooses adapted coordinates separately for the marked packet,
uses the positive supported bend, and recovers the fine and packet permanents
by their common Gram evaluation. -/
theorem marcus_three_supported {k : ℕ} (hk : 2≤k)
    (hs : ∀ d, HomogeneousSchur d k k) (hb : ∀ d, HomogeneousSchur d (k+k) k) :
    MarcusAt 3 k :=
  marcus_from_marked hk hs hb ThreeGram.gram_invariant (fun x => ThreeGram.target_gap x)

end
end BlockPermanents.ThreeMarkedAverage
