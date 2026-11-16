import BlockPermanents.FourQuadratic
import BlockPermanents.Coarse
import Mathlib.Tactic.Linarith

/-! # Estimating proper four-packet cuts by their rows of last-cap values -/
namespace BlockPermanents.FourQuadratic
open Matrix Bend
open scoped BigOperators ComplexOrder Matrix
noncomputable section

private theorem quadratic_dot {I : Type*} [Fintype I] (M : Matrix I I ℂ) (v : I → ℂ) :
    quadratic M v = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The norm accounted for by a whole row of possibly overlapping last caps
is its inverse-Gram quadratic form. The unaccounted orthogonal component
has nonnegative squared norm. -/
theorem inverseGram_le {I U : Type*} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
    (C : Matrix I U ℂ) (h : (C * Cᴴ).PosDef) (z : U → ℂ) :
    (quadratic (C*Cᴴ)⁻¹ (C.mulVec z)).re ≤ energy z := by
  let P := Routings.gramProjection C
  obtain ⟨hs,hp,_⟩ := Routings.gramProjection_spec C h
  have hstar : Pᴴ = P := hs
  have hcomp : (1-P)ᴴ*(1-P) = 1-P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, hp, sub_self, sub_zero]
  have hpos : (1-P).PosSemidef := by rw [← hcomp]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hn := (Complex.nonneg_iff.mp (hpos.2 z)).1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at hn
  have hz : (star z ⬝ᵥ z) = (energy z : ℂ) := by
    exact Coarse.bracket_self z
  rw [hz, Complex.ofReal_re] at hn
  rw [quadratic_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  exact sub_nonneg.mp hn

/-- Reinsert the three proper halves before the orthogonal projections. The
hypotheses are precisely their pairwise last-cap gluings and the values of
the two full-cap routes on the chosen input. The discarded complementary
squares stay on their original Hilbert spaces. -/
theorem three_halves_nonnegative {U W V : Type*} [Fintype U] [Fintype W] [Fintype V]
    [DecidableEq U] [DecidableEq W] [DecidableEq V] {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1)
    (C : Matrix (Fin 2) U ℂ) (D : Matrix (Fin 2) W ℂ) (E : Matrix (Fin 1) V ℂ)
    (hC : C*Cᴴ = Routings.capGram d41 2 ρ) (hD : D*Dᴴ = Routings.capGram d23 2 ρ)
    (hE : E*Eᴴ = Routings.capGram d5 2 ρ) (u : U → ℂ) (w : W → ℂ) (v : V → ℂ) (x y : ℂ)
    (hu : C.mulVec u = ![y,x]) (hw : D.mulVec w = ![y,fullCapMean 2 x y])
    (hv : E.mulVec v = fun _ => fullCapMean 3 x y) :
    0 ≤ 24*energy u + 144*energy w + 1080*energy v +
      1350*Complex.normSq (fullCapMean 3 x y-x/15) + 108*Complex.normSq (fullCapMean 2 x y) -
      36*Complex.normSq x := by
  have hs : ρ < 2 := by linarith
  have h₁ := inverseGram_le C (hC ▸ Routings.capGram_posDef d41 2 ρ h₀ hs) u
  have h₂ := inverseGram_le D (hD ▸ Routings.capGram_posDef d23 2 ρ h₀ hs) w
  have h₃ := inverseGram_le E (hE ▸ Routings.capGram_posDef d5 2 ρ h₀ hs) v
  rw [hC,hu] at h₁
  rw [hD,hw] at h₂
  rw [hE,hv] at h₃
  have hx : 0 ≤ gramSector ρ x y := by
    rw [gramSector_split h₀ ‹ρ ≤ 1›]
    exact add_nonneg (sector_nonnegative h₀ ‹ρ ≤ 1› _ _) (sector_nonnegative h₀ ‹ρ ≤ 1› _ _)
  dsimp only [gramSector] at hx
  linarith only [hx,h₁,h₂,h₃]


end
end BlockPermanents.FourQuadratic
