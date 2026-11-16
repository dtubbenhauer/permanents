import BlockPermanents.FourRouteNorm
import BlockPermanents.FourFullValues

/-! # Positivity of the four-quadratic bend on supported packet products -/
namespace BlockPermanents.FourFullValues
open Bend Closures FourRoutes FourCapOrbit FourCapValues FourLastCaps
open scoped BigOperators Matrix
noncomputable section

/-- The four-packet quadratic form (5C.3). Every proper half is a
spectator slice of the literal contracted matrix; the three full halves
retain their four ordered positive outputs. -/
def cutForm {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) : ℝ :=
  24*properEnergy 0 F H + 144*properEnergy 1 F H + 1080*properEnergy 2 F H +
    1350*energy (fun t => full 2 F H t - clasp (full 0 F H) t/15) +
    108*energy (full 1 F H) - 12*energy (full 0 F H) - 24*energy (clasp (full 0 F H))

/-- Positivity on an actual supported marked packet, with no assumptions on
the port Gram or on any of the closures appearing in the diagram. -/
theorem cutForm_nonnegative {d : ℕ} (S : Finset (Fin d)) (hcard : S.card = 2)
    {F : Triple d 2 → ℂ} (hF : Inner F) (H : Word d 2 → ℂ) (hH : Bend.Symmetric H)
    (hS : Supported S H) : 0 ≤ cutForm F H := by
  have h := proper_and_full S hcard hF H hH (full 1 F H) (fun t => (full_values S hF H hH hS t).2.1)
  have hu : clasp (full 0 F H) = value S F H sameChart := funext fun t => (full_values S hF H hH hS t).1
  have hv : full 2 F H = fun t => (value S F H sameChart t+4*value S F H mixedChart t)/5 :=
    (last_symmetric F H hH).symm.trans (funext fun t => (full_values S hF H hH hS t).2.2)
  have ht : lastTrace S (some 3) (raw 0 F H) = full 0 F H := by
    funext w
    rw [← join_cut 0 F H hH]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro b _ hb
    exact outside_zero 0 S F H hH hS _ hb
  dsimp only at h
  rw [ht] at h
  simpa only [cutForm,hu,hv] using h

/-- Nonnegative marked cut value for an ordinary triple of matrix packets
and a marked packet whose two atoms lie in the indicated two-plane. -/
theorem packet_cutForm {d : ℕ} (S : Finset (Fin d)) (hc : S.card = 2)
    (x : Fin 3 → Fin 2 → Fin d → ℂ) (y : Fin 2 → Fin d → ℂ)
    (hs : ∀ i j, j ∉ S → y i j = 0) :
    0 ≤ cutForm (pureWord (fun i => packet (x i))) (packet y) :=
  cutForm_nonnegative S hc (packet_inner x) (packet y) (Bridges.packet_symmetric _ _ _) (packet_supported S y hs)

end
end BlockPermanents.FourFullValues
