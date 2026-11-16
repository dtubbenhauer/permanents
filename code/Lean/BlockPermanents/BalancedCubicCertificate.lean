import BlockPermanents.BalancedCubicTau
import BlockPermanents.BalancedCubicExterior
import BlockPermanents.BalancedCubicFine

/-! The signed three-division certificate of Theorem 6C.3 on cubic matrix packets. -/
namespace BlockPermanents.BalancedCubic
open Closures Bend CubicSquares BalancedCoarse BalancedSigned MatchingFine
open BalancedCubicExterior
open scoped Matrix
noncomputable section

/-- The two proper cubic cuts have Schur weight nine. -/
def edgeSquares {d : ℕ} (U : Matrix (Fin d) (Fin 3) ℂ) (F H : Word d 3 → ℂ) : ℝ :=
  9 * energy (BalancedCubicTau.half U F H 1) + 9 * energy (BalancedCubicTau.half U F H 2)

/-- The contribution to T of a matching with two perpendicular energies a,b. -/
def matched {D : Type*} [Fintype D] (F : Fin 4 → D → ℂ) (a b : ℝ) : ℝ :=
  a * (1 + 11/2 * BalancedCut.sq F 2 3) + b * (1 + 11/2 * BalancedCut.sq F 0 1) + a*b

/-- The contribution to T for the matching (0,1)(2,3) on fixed three-planes. -/
def matchingSquares {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (U : Fin 4 → Matrix (Fin d) (Fin 3) ℂ) : ℝ :=
  let F := fun i => packet (x i)
  matched F (edgeSquares (U 0) (F 0) (F 1)) (edgeSquares (U 2) (F 2) (F 3))

/-- Reversing a cubic opposed edge may change the supporting plane. The
sum of its two reflected halves is unchanged. -/
theorem reverse_edge {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (i j : Fin 4)
    (U V : Matrix (Fin d) (Fin 3) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (hi : packet (x i) ∈ BalancedSupport.space 3 U) (hj : packet (x j) ∈ BalancedSupport.space 3 V) :
    edgeSquares U (packet (x i)) (packet (x j)) = edgeSquares V (packet (x j)) (packet (x i)) := by
  exact (BalancedCubicTau.tau_squares x h i j U hU hi).symm.trans
    ((BalancedCubicTau.tau_swap x i j).trans (BalancedCubicTau.tau_squares x h j i V hV hj))

theorem proper_squares {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (U : Fin 4 → Matrix (Fin d) (Fin 3) ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) (hs : ∀ i, packet (x i) ∈ BalancedSupport.space 3 (U i)) :
    properSquares x = matchingSquares x U := by
  unfold properSquares matchingSquares matched edgeSquares
  rw [BalancedCubicTau.tau_squares x h 0 1 (U 0) (hU 0) (hs 0),
    BalancedCubicTau.tau_squares x h 2 3 (U 2) (hU 2) (hs 2)]

/-- The signed survivor square, the t=1/2 square, the det of the two
full caps, and the four exterior products for a single division. -/
def signedTerms {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) : ℝ :=
  let U := leftSide X
  let V := rightSide X
  let α := caps U V
  energy ((survivors U V * phases).mulVec α) +
    energy ((residual (1/2) (bracket (U 1) (U 0)) (star (bracket (V 1) (V 0)))).mulVec α) +
    Complex.normSq (α 0 * α 3 - α 1 * α 2) + 4 * internal X * crossingWedges X

/-- The complete 37/4 identity, replacing every scalar slack by its actual
proper cuts, trace-cup complements or exterior minors. -/
theorem cubic_certificate {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (U : Fin 4 → Matrix (Fin d) (Fin 3) ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) (hs : ∀ i, packet (x i) ∈ BalancedSupport.space 3 (U i)) :
    let X := fun i => packet (x i)
    let g := crossGram X X
    3 * (fine (Function.uncurry x) - g.permanent.re) =
      (∑ p : Fin 3, BalancedCubicFine.squares (x ∘ division p)) +
      (∑ p : Fin 3, matchingSquares (x ∘ division p) (U ∘ division p)) +
      37/4 * FourTrade.matchings g + ∑ p : Fin 3, signedTerms (X ∘ division p) := by
  have hp (p : Fin 3) := proper_squares (x ∘ division p) (fun i => h _) (U ∘ division p)
    (fun i => hU _) (fun i => hs _)
  have he (p : Fin 3) : signedSquares ((fun i => packet (x i)) ∘ division p) =
      signedTerms ((fun i => packet (x i)) ∘ division p) :=
    signedSquares_exterior _ (fun i => h _)
  simpa only [BalancedCubicFine.fine_remainder, hp, he] using cubic_identity x h

/-- Read a cubic edge on the smaller span of its actual surviving products.
In low Gram dimension the excess coefficient multiplies the full-cap square. -/
def spanEdge {d : ℕ} (a b : Fin 3 → Fin d → ℂ) : ℝ :=
  let H := packet b
  9 * energy (PairResidual.residual 1 a H 1) + 9 * energy (PairResidual.residual 1 a H 2) +
    (BalancedCubicTau.rankCorrection a 1 + BalancedCubicTau.rankCorrection a 2) *
      Complex.normSq (bracket (packet a) H)

def spanMatching {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) : ℝ :=
  matched (fun i => packet (x i)) (spanEdge (x 0) (x 1)) (spanEdge (x 2) (x 3))

/-- The complete identity in every original Gram dimension, using only
the spans of the actual packets. No ambient extension or frame is required. -/
theorem cubic_certificate_all_dimensions {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) :
    let X := fun i => packet (x i)
    let g := crossGram X X
    3 * (fine (Function.uncurry x) - g.permanent.re) =
      (∑ p : Fin 3, BalancedCubicFine.squares (x ∘ division p)) +
      (∑ p : Fin 3, spanMatching (x ∘ division p)) +
      37/4 * FourTrade.matchings g + ∑ p : Fin 3, signedTerms (X ∘ division p) := by
  have hp (p : Fin 3) : properSquares (x ∘ division p) = spanMatching (x ∘ division p) := by
    unfold properSquares spanMatching matched spanEdge
    rw [BalancedCubicTau.tau_packet_spans (x ∘ division p) (fun i => h _) 0 1,
      BalancedCubicTau.tau_packet_spans (x ∘ division p) (fun i => h _) 2 3]
  have he (p : Fin 3) : signedSquares ((fun i => packet (x i)) ∘ division p) =
      signedTerms ((fun i => packet (x i)) ∘ division p) :=
    signedSquares_exterior _ (fun i => h _)
  simpa only [BalancedCubicFine.fine_remainder, hp, he] using cubic_identity x h

end
end BlockPermanents.BalancedCubic
