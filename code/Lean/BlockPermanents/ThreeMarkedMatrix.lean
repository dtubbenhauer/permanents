import BlockPermanents.ThreeOrbitGap
import BlockPermanents.ThreeSupportedProduct
import BlockPermanents.SupportCoordinates

/-! Change coordinates separately for each choice of marked packet, then
average the nonnegative evaluations as in Section 3D. -/
namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen Closures SchurNormalization
open scoped BigOperators Matrix ComplexOrder
noncomputable section

theorem supported_mark {d k : ℕ} (hk : 2≤k) (hs : HomogeneousSchur d k k)
    (hb : HomogeneousSchur d (k+k) k) (x : Fin 3→Fin k→Fin d→ℂ)
    (S : Finset (Fin d)) (hS : S.card = k) (hx : ∀ i j, j∉S → x 2 i j=0) :
    0 ≤ (quadratic (original d k) (data x)).re := by
  rw [productData]
  exact original_product_nonnegative hk hs hb S (by omega) (by omega) _ _ _
    (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)
    (packet_supported S (x 2) hx)

theorem transport_mark {d k : ℕ} (hk : 2≤k)
    (hs : ∀ d, HomogeneousSchur d k k) (hb : ∀ d, HomogeneousSchur d (k+k) k)
    (x : Fin 3→Fin k→Fin d→ℂ)
    (invariant : ∀ {e : ℕ} (y : Fin 3→Fin k→Fin e→ℂ),
      crossGram (Function.uncurry x) (Function.uncurry x) =
        crossGram (Function.uncurry y) (Function.uncurry y) →
      quadratic (original d k) (data x)=quadratic (original e k) (data y)) :
    0 ≤ (quadratic (original d k) (data x)).re := by
  obtain ⟨e,S,U,hS,hU,hx⟩ := SupportCoordinates.adapt (x 2)
  let y (i : Fin 3) (j : Fin k) := U (x i j)
  have hgram : crossGram (Function.uncurry x) (Function.uncurry x) =
      crossGram (Function.uncurry y) (Function.uncurry y) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    exact (hU (x i a) (x j b)).symm
  rw [invariant y hgram]
  exact supported_mark hk (hs e) (hb e) y S hS hx

/-- Apply the matrix Gram reduction using the marked support independently
for each of the six reorderings of the packet product. -/
theorem marcus_from_marked {k : ℕ} (hk : 2≤k)
    (hs : ∀ d, HomogeneousSchur d k k) (hb : ∀ d, HomogeneousSchur d (k+k) k)
    (invariant : ∀ {d e : ℕ} (x : Fin 3→Fin k→Fin d→ℂ) (y : Fin 3→Fin k→Fin e→ℂ),
      crossGram (Function.uncurry x) (Function.uncurry x) =
        crossGram (Function.uncurry y) (Function.uncurry y) →
      quadratic (original d k) (data x) = quadratic (original e k) (data y))
    (hgap : ∀ x : Fin 3→Fin k→Fin (3*k)→ℂ,
      quadratic (target (3*k) k) (data x) = gap x) : MarcusAt 3 k := by
  apply MatchingThreshold.marcusAt_of_gram
  intro x
  have h := gap_of_marked x
    (fun p => transport_mark hk hs hb (x ∘ p) (fun y he => invariant _ y he)) hgap
  change 0 ≤ (_ - _ : ℂ).re at h
  exact sub_nonneg.mp (by simpa only [Complex.sub_re] using h)

end
end BlockPermanents.ThreeMarkedAverage
