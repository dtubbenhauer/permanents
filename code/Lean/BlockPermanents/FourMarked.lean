import BlockPermanents.FourActualAlgebra
import BlockPermanents.FourOpenings
import BlockPermanents.FourRestricted

/-! # Marking and opening the four-quadratic matrix packet product -/
namespace BlockPermanents.FourMarked
open Closures FourTarget FourLocalCompression FourWireAlgebra TransferBlocks SchurNormalization
noncomputable section

/-- On the same packet product used in the PSD Gram reduction, the
ordinary marked operator has the seven quadratic opened terms. -/
theorem open_marked {d : ℕ} (x : Fin 4 → Fin 2 → Fin d → ℂ)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) :
    let z := flatPackets x
    (bracket z (Q d 2 z)).re =
      (bracket z (raw (ordinary (packets d 2)) (localClasp d 2 3) (localClasp d 2 2)
        (movedPair (packets d 2) (localClasp d 2 2)) (act d 2 eWire) (packets d 2 swap14) z)).re := by
  dsimp only
  have he := FourActualAlgebra.actual_open d (sand (W d)) (act d 2 eWire) (FourOpenings.openings_three d h₂ h₄ h₆)
  have hv := congrArg (fun a : Op d 2 => (bracket (flatPackets x) (a (flatPackets x))).re) he
  simpa only [sand,LinearMap.coe_mk,AddHom.coe_mk,compression_bracket] using hv

end
end BlockPermanents.FourMarked
