import BlockPermanents.FiveMean
import Mathlib.Data.Matrix.Notation

/-! Kernel-checked conjugacy classification and class sizes used in (8C.2). -/
namespace BlockPermanents.FiveCycles
namespace Conjugacy
def rep : Fin 7 → S := ![
  1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 3 4,
  Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4,
  Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4,
  Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2]

def kind (τ : S) : Fin 7 :=
  match (Finset.univ.filter (fun i => τ i = i)).card with
  | 5 => 0 | 3 => 1 | 2 => 3 | 1 => if τ*τ = 1 then 2 else 5
  | _ => if τ^5 = 1 then 6 else 4

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
theorem classifies : ∀ τ : S, ∃ π : S, ∀ i, π ((rep (kind τ)) i) = τ (π i) := by
  decide +kernel

def size : Fin 7 → ℕ := ![1,10,15,20,20,30,24]

set_option maxHeartbeats 2000000 in
theorem counts : ∀ k, (Finset.univ.filter (fun τ : S => kind τ = k)).card = size k := by
  decide +kernel

end Conjugacy
end BlockPermanents.FiveCycles
