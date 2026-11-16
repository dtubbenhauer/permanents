import BlockPermanents.ConsecutiveCycleSquares
import BlockPermanents.CycleParameters

/-! Reflected energies for both signs of a single piece of a disjoint-cycle plan. -/
namespace BlockPermanents.PieceProductSquares
open CyclePlans CycleCuts CycleParameters CycleMatching CycleComposition ReflectedCycles Closures Matchings
noncomputable section

variable {D : Type*} [Fintype D]

/-- On a component of fixed points the unit closure has signed energies 2 and 0. -/
def fixedEnergy (plus : Bool) : ℝ := if plus then 2 else 0

def piecePerm : (a : Piece) → S a.size
  | .fixed _ => 1
  | .even r => localPerm (2*r+2) 0
  | .odd r s => localPerm (2*r+3) s

theorem piece_type (a : Piece) : (piecePerm a).cycleType = (a.parts : Multiset ℕ) := by
  cases a with
  | fixed n => simp [piecePerm, Piece.parts]
  | even r => simpa [piecePerm, Piece.parts] using localPerm_type (2*r+2) 0 (by omega)
  | odd r s => simpa [piecePerm, Piece.parts] using localPerm_type (2*r+3) s (by omega)

/-- Each component uses its consecutive-cycle reflected square, with its own parameter. -/
def pieceEnergy : (a : Piece) → (Fin a.size → D → ℂ) → Bool → ℝ → ℝ
  | .fixed _, _, plus, _ => fixedEnergy plus
  | .even r, x, plus, _ => evenRemainder r 0 (crossGram x x) plus
  | .odd r s, x, plus, u => oddRemainder r s x plus u

theorem fixedEnergy_nonneg (plus : Bool) : 0 ≤ fixedEnergy plus := by
  cases plus <;> norm_num [fixedEnergy]

theorem pieceEnergy_nonneg (a : Piece) (x : Fin a.size → D → ℂ) (plus : Bool) {u : ℝ}
    (hu : 0 < u) : 0 ≤ pieceEnergy a x plus u := by
  cases a with
  | fixed n => exact fixedEnergy_nonneg plus
  | even r => exact div_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)) (by norm_num)
  | odd r s => exact oddRemainder_nonneg _ _ _ _ _ hu

private theorem fixed_mean {m : ℕ} (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) :
    (mean (crossGram x x) 1).re = 1 := by
  have hx (σ : S m) : circuit (crossGram x x) 1 σ = 1 := by
    simp [circuit, crossGram, Coarse.bracket_self, unit]
  simp [mean, re_complexAverage, hx, average_const]

theorem fixed_identity {m : ℕ} (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) :
    Z (crossGram x x) 0 + sign plus * (mean (crossGram x x) 1).re = fixedEnergy plus := by
  have hz : Z (crossGram x x) 0 = 1 := by simp [Z, moment_zero]
  rw [hz, fixed_mean x unit]
  cases plus <;> norm_num [sign, fixedEnergy]

open private packets_unitGram from BlockPermanents.OddCycleSquares in
theorem piece_identity (a : Piece) (x : Fin a.size → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) (u : ℕ → ℝ) (hu : 0 < u 0) :
    let g := crossGram x x
    score [a] u (Z g) 0 + sign plus * (mean g (piecePerm a)).re = pieceEnergy a x plus (u 0) := by
  cases a with
  | fixed n => exact fixed_identity x unit plus
  | even r => simpa only [score, Nat.zero_add, piecePerm, pieceEnergy] using
      even_consecutive_squares r 0 (crossGram x x) (packets_unitGram x unit) plus
  | odd r s => simpa only [score, Nat.zero_add, piecePerm, pieceEnergy] using
      odd_consecutive_squares r s x unit plus _ hu

end
end BlockPermanents.PieceProductSquares
