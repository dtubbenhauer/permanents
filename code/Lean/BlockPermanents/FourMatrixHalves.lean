import BlockPermanents.FourRestricted
import BlockPermanents.FourUpright
import BlockPermanents.FourFootAverage

/-! # The three oriented merges on a normalized matrix packet product -/
namespace BlockPermanents.FourMatrixHalves
open FourTarget FourUpright FourFootAverage FourWireCut FourCapOrbit FourRoutes FourWireAlgebra
open Closures TransferBlocks
open scoped BigOperators
noncomputable section

def unmarked {d : ℕ} (a : Fin 4 → Fin 2 → Fin d → ℂ) :=
  pureWord (fun i : Fin 3 => packet (a i.castSucc))

lemma flat {d : ℕ} (a : Fin 4 → Fin 2 → Fin d → ℂ) :
    flatPackets a = product (first (unmarked a)) (packet (a 3)) := by
  funext w
  rw [flatPackets,Fin.prod_univ_castSucc]
  rfl

lemma feet_action {d : ℕ} (a : Fin 4 → Fin 2 → Fin d → ℂ) :
    ordinary (packets d 2) (flatPackets a) = product (feet (unmarked a)) (packet (a 3)) := by
  rw [flat,ordinary_product]

/-- The three active-clasp rows and the complementary spectator clasp,
evaluated on precisely the vector used in the Gram-matrix comparison. -/
theorem halves {d : ℕ} (a : Fin 4 → Fin 2 → Fin d → ℂ)
    (absorbs : localClasp d 2 3 * ordinary (packets d 2) = localClasp d 2 3) :
    let z := flatPackets a
    let J := ordinary (packets d 2)
    let F := unmarked a
    let H := packet (a 3)
    J z = product (merged 0 F) H ∧
      suffix d 1 (J z) = product (merged 1 F) H ∧
      localClasp d 2 3 z = product (merged 2 F) H ∧
      localClasp d 2 2 (J z) = product (spectator (merged 0 F)) H := by
  dsimp only
  have hz := merged_zero (unmarked a) (packet_inner _)
  refine ⟨(feet_action a).trans (by rw [hz]),?_,?_,?_⟩
  · rw [feet_action,suffix_product]
  · have h := DFunLike.congr_fun absorbs (flatPackets a)
    change localClasp d 2 3 (ordinary (packets d 2) (flatPackets a)) = _ at h
    rw [←h,feet_action,entire,suffix_product]
  · rw [feet_action,hz,spectator_product]

/-- Reversal exchanges the first and third ordinary packets while preserving
the marked fourth packet. -/
lemma oriented_flat {d : ℕ} (a : Fin 4 → Fin 2 → Fin d → ℂ) :
    packets d 2 ori (flatPackets a) = flatPackets (a ∘ ori.symm) :=
  FourRestricted.relabel _ _

end
end BlockPermanents.FourMatrixHalves
