import BlockPermanents.ThreeSupportedAssembly
import BlockPermanents.ThreeLastRouted
import BlockPermanents.ThreeCanonical

/-! The all-thickness supported three-packet decomposition on a common mixed
boundary. The mark may be an arbitrary map with image in the symmetric
words over the supported coordinate subspace. -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend SchurNormalization ThreeSupport FourRoutes
open scoped BigOperators Matrix ComplexOrder
noncomputable section
variable {I J : Type*}

theorem supported_decomposition {d k : ℕ} (hk : 2≤k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (hM : ∀ t i, Symmetric (fun w => M t w i))
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (S : Finset (Fin d)) (hs : 0<S.card)
    (hn : ∀ w j, (∃ t, w t∉S) → N w j=0) :
    let a : ℂ := (k+k).choose k
    let v := terminal (stackedFine P) N
    let u := terminal (stack M) N
    let perp := ThreeLastCap.perpendicular S (ThreeLastRouted.stackLast (show 1≤k by omega) M N)
    partialTranspose (corrected M P N) =
      (2:ℂ) • earlySquares M N + a • properSquares (by omega) (fun _ : Unit => P) N +
      (2*(k:ℂ)^2) • Support.reflected perp + Support.reflected (a • v - (1/2:ℂ) • u) +
      (2*(k:ℂ)^2/S.card - 9/4) • Support.reflected u :=
  resolve_raw hk hsmall hbig M P N hM hP hN _
    (ThreeLastRouted.routed_resolution S hs (by omega) M N hM hN hn)

theorem supported_psd {d k : ℕ} [Fintype I] [Fintype J] (hk : 2≤k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (hM : ∀ t i, Symmetric (fun w => M t w i))
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (S : Finset (Fin d)) (hs : 0<S.card) (hsk : S.card≤k)
    (hn : ∀ w j, (∃ t, w t∉S) → N w j=0) :
    (partialTranspose (corrected M P N)).PosSemidef :=
  resolved_psd hk hs hsk hsmall hbig M P N hM hP hN _
    (ThreeLastRouted.routed_resolution S hs (by omega) M N hM hN hn)

/-- The actual two packet orders, fine 2k-clasp, and supported marked k-clasp.
The conclusion tests arbitrary entangled mixed-boundary vectors. -/
theorem canonical_supported_psd {d k : ℕ} (hk : 2≤k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (S : Finset (Fin d)) (hs : 0<S.card) (hsk : S.card≤k) :
    (partialTranspose (corrected (M d k) (P d k) (ThreeLastRouted.markedColumns (k:=k) S))).PosSemidef :=
  supported_psd hk hsmall hbig _ _ _ (pair_symmetric d k)
    (fun i => column_symmetric _ _ _) (ThreeLastRouted.marked_symmetric S)
    S hs hsk (ThreeLastRouted.marked_support S)

end
end BlockPermanents.ThreeGeneralOpen
