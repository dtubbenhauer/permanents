import BlockPermanents.FourTradeSquares
import BlockPermanents.RefinedCoarse

/-! The signed four-label trade with a fixed spectator matching, averaged
over the labels and orientations of the actual unit packets. -/
namespace BlockPermanents.FaceTradeSquares
open Closures Matchings FaceSampling FaceMeans FacePeel FaceTrade CycleMatching
noncomputable section

def remainder {m d : ℕ} (x : Input m d) (r : ℕ) (u : ℝ) : ℝ :=
  mean x r 4 (fun y => FourTradeSquares.remainder y u)

theorem remainder_nonneg {m d r : ℕ} (x : Input m d) (fit : 2*r+4 ≤ m) {u : ℝ} (hu : 0 < u) :
    0 ≤ remainder x r u := by
  rw [remainder, mean, sample_eq (positions fit)]
  unfold average
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
      (FourTradeSquares.remainder_nonneg _ hu))

open private four_slack from BlockPermanents.RefinedCoarse in
theorem four_identity {m d r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    (fit : 2*r+4 ≤ m) (u : ℝ) (hu : 0 < u) :
    let z := Z (crossGram x x)
    FaceSlacks.S x 4 r = 4*(1-u)*z (r+1) + 4*(1-1/u)*z (r+2) + remainder x r u := by
  let e := positions fit
  let p := Function.Embedding.inl.trans e
  let j := Function.Embedding.inr.trans e
  have fresh (i : Fin 4) : j i ∉ Set.range p := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr (e.injective hk)
  let P (y : Input 4 d) := FourTrade.edges (crossGram y y)
  let D (y : Input 4 d) := FourTrade.matchings (crossGram y y)
  let a := 2*(1-u)/3
  let b := 4*(1-1/u)/3
  have h := FaceTrade.extensions (crossGram x x) p j fresh
  have hP : mean x r 4 P = 6*Z (crossGram x x) (r+1) := by
    rw [mean, FaceSampling.sample_eq e]
    simpa only [Fintype.card_fin] using h.1
  have hD : mean x r 4 D = 3*Z (crossGram x x) (r+2) := by
    rw [mean, FaceSampling.sample_eq e]
    simpa only [Fintype.card_fin] using h.2
  have localEq := FaceSlacks.mean_congr x fit (f := fun y => slack (crossGram y y))
    (g := fun y => a*P y+b*D y+FourTradeSquares.remainder y u) (by
      intro v
      let y := active x v
      have hi := FourTradeSquares.gram_identity y (fun _ => unit _) u hu
      dsimp only at hi
      change slack (crossGram y y) = _
      unfold slack P D a b
      change 1+7/3*FourTrade.edges (crossGram y y)+3*FourTrade.matchings (crossGram y y)-
        (crossGram y y).permanent.re = 2*(1-u)/3*FourTrade.edges (crossGram y y)+
        4*(1-1/u)/3*FourTrade.matchings (crossGram y y)+FourTradeSquares.remainder y u
      linear_combination -hi)
  rw [four_slack x fit]
  change mean x r 4 _ = _
  rw [localEq,mean_linear x fit,mean_linear x fit,mean_smul x fit,mean_smul x fit,hP,hD]
  dsimp only [a,b,remainder]
  ring

end
end BlockPermanents.FaceTradeSquares
