import BlockPermanents.FourCapValues
import BlockPermanents.FourLocalSlots

/-! The special slot at the bottom of a proper cut is strand two of
ordinary packet three. Its five companions retain the last-cap labelling. -/
namespace BlockPermanents.FourWireCut
open FourTarget FourCapOrbit FourCapValues FourRoutes Bend Equiv
noncomputable section

def product {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ)
    (w : Slot 2 → Fin d) : ℂ :=
  U (fun i => w (i.1.castSucc,i.2)) * H (fun j => w (3,j))

def merged {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (w : Pos → Fin d) : ℂ :=
  (((r.val+1)*2).factorial : ℂ)⁻¹ * ∑ p : Perm (A r),
    feet F (w ∘ (order r p).trans (order r 1).symm)

def spectator {d : ℕ} : LocalAction.EndW Pos (Fin d) :=
  LocalGroup.projector (Fin d) (fun j : Pos => j.1.val < 2)

def single : Wire 2 := swap ((2,1) : Slot 2) (3,1)
def double : Wire 2 := wires 2 TransferBlocks.swap34

end
end BlockPermanents.FourWireCut
