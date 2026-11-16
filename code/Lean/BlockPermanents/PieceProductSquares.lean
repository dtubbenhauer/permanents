import BlockPermanents.PieceEnergies
import BlockPermanents.PieceScoreProduct

/-! Reflected-square products on disjoint labels in Lemma AC.1. -/
namespace BlockPermanents.PieceProductSquares
open CyclePlans CycleMatching CycleComposition CycleCuts ReflectedCycles CycleParameters Closures Matchings
noncomputable section

variable {D : Type*} [Fintype D]

/-- Concatenate the consecutive permutations on pairwise disjoint label sets. -/
def planPerm : (p : List Piece) → S (planSize p)
  | [] => 1
  | a :: p => splitPerm finSumFinEquiv (piecePerm a) (planPerm p)

theorem plan_type (p : List Piece) : (planPerm p).cycleType = (planParts p : Multiset ℕ) := by
  induction p with
  | nil => simp [planPerm, planParts]
  | cons a p ih => simp [planPerm, planParts, split_type, piece_type, ih]

private def leftPackets {a b : ℕ} (x : Fin (a+b) → D → ℂ) (σ : S (a+b)) :
    Fin a → D → ℂ := fun i => x (σ (finSumFinEquiv (.inl i)))

private def rightPackets {a b : ℕ} (x : Fin (a+b) → D → ℂ) (σ : S (a+b)) :
    Fin b → D → ℂ := fun i => x (σ (finSumFinEquiv (.inr i)))

/-- Two equal-sign or opposite-sign products of reflected energies, according to the
sign of the new closure. -/
def halfSum (L R : Bool → ℝ) (plus : Bool) : ℝ :=
  (L true * R plus + L false * R (!plus)) / 2

/-- Average the products over disjoint assignments of actual labels at each split. -/
def energy : (p : List Piece) → (ℕ → ℝ) → (Fin (planSize p) → D → ℂ) → Bool → ℝ
  | [], _, _, plus => fixedEnergy plus
  | a :: p, u, x, plus =>
    average _ fun σ => halfSum
      (fun s => pieceEnergy a (leftPackets (b := planSize p) x σ) s (u 0))
      (energy p (fun i => u (i+1)) (rightPackets (a := a.size) x σ)) plus

theorem energy_nonneg (p : List Piece) (u : ℕ → ℝ) (hu : ∀ i, 0 < u i)
    (x : Fin (planSize p) → D → ℂ) (plus : Bool) : 0 ≤ energy p u x plus := by
  induction p generalizing u plus with
  | nil => exact fixedEnergy_nonneg _
  | cons a p ih =>
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro σ _
    apply div_nonneg _ (by norm_num)
    apply add_nonneg <;> apply mul_nonneg (pieceEnergy_nonneg _ _ _ (hu 0))
    · exact ih _ (fun i => hu (i+1)) _ _
    · exact ih _ (fun i => hu (i+1)) _ _

private theorem halfSum_identity (A B C E : ℝ) (plus : Bool) :
    halfSum (fun s => A + sign s * C) (fun s => B + sign s * E) plus =
      A * B + sign plus * (C * E) := by
  cases plus <;> simp [halfSum, sign] <;> ring

open private packets_unitGram from BlockPermanents.OddCycleSquares in
private theorem split_mean_re (a : Piece) (p : List Piece) (x : Fin (planSize (a::p)) → D → ℂ)
    (unit : ∀ i, Bend.energy (x i) = 1) :
    (mean (crossGram x x) (planPerm (a::p))).re =
    average _ (fun σ =>
      (mean (leftGram (crossGram x x) finSumFinEquiv σ) (piecePerm a)).re *
      (mean (rightGram (crossGram x x) finSumFinEquiv σ) (planPerm p)).re) := by
  let g := crossGram x x
  have hg := packets_unitGram x unit
  rw [planPerm, split_mean, re_complexAverage]
  apply congrArg (average _)
  funext σ
  let L := leftGram (a := a.size) (b := planSize p) g finSumFinEquiv σ
  let R := rightGram (a := a.size) (b := planSize p) g finSumFinEquiv σ
  change (mean L _ * mean R _).re = (mean L _).re * (mean R _).re
  have hL (i j) : star (L i j) = L j i := hg.herm .. 
  have hR (i j) : star (R i j) = R j i := hg.herm ..
  conv_lhs => rw [mean_real L hL (piecePerm a), mean_real R hR (planPerm p), ← Complex.ofReal_mul]
  rfl

/-- The normalized signed identity for the concrete concatenation of the cycles. -/
theorem plan_squares (p : List Piece) (u : ℕ → ℝ)
    (hu : ∀ i, 0 < u i) (x : Fin (planSize p) → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) : score p u (Z (crossGram x x)) 0 + sign plus * (mean (crossGram x x) (planPerm p)).re =
      energy p u x plus := by
  induction p generalizing u plus with
  | nil => exact fixed_identity x unit plus
  | cons a p ih =>
    let v := fun i => u (i+1)
    let l (σ : S (planSize (a::p))) := leftPackets (a := a.size) (b := planSize p) x σ
    let r (σ : S (planSize (a::p))) := rightPackets (a := a.size) (b := planSize p) x σ
    let A σ := score [a] u (Z (crossGram (l σ) (l σ))) 0
    let B σ := score p v (Z (crossGram (r σ) (r σ))) 0
    let C σ := (mean (crossGram (l σ) (l σ)) (piecePerm a)).re
    let E σ := (mean (crossGram (r σ) (r σ)) (planPerm p)).re
    have hL σ s : pieceEnergy a (l σ) s (u 0) = A σ + sign s * C σ :=
      (piece_identity a (l σ) (fun i => unit _) s u (hu 0)).symm
    have hR σ s : energy p v (r σ) s = B σ + sign s * E σ :=
      (ih v (fun i => hu (i+1)) (r σ) (fun i => unit _) s).symm
    have hf : average _ (fun σ => A σ * B σ) = score (a::p) u (Z (crossGram x x)) 0 :=
      PieceScoreProduct.score_split a p u (crossGram x x)
    have hm : (mean (crossGram x x) (planPerm (a::p))).re = average _ (fun σ => C σ * E σ) :=
      split_mean_re a p x unit
    rw [← hf, hm, ← average_smul, ← average_add]
    change average _ _ = average _ (fun σ => halfSum (fun s => pieceEnergy a (l σ) s (u 0))
      (energy p v (r σ)) plus)
    apply congrArg (average _)
    funext σ
    rw [show energy p v (r σ) = _ from funext (hR σ)]
    simp only [hL, halfSum_identity]

/-- Both signs of the class mean are realized by the same explicit products of local
reflected energies, for every representative of the prescribed cycle type. -/
theorem class_squares (p : List Piece) (u : ℕ → ℝ) (hu : ∀ i, 0 < u i)
    (τ : S (planSize p)) (hτ : τ.cycleType = (planParts p : Multiset ℕ))
    (x : Fin (planSize p) → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) (plus : Bool) :
    score p u (Z (crossGram x x)) 0 + sign plus * (mean (crossGram x x) τ).re = energy p u x plus := by
  rw [mean_conjugate _ (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hτ.trans (plan_type p).symm))]
  exact plan_squares p u hu x unit plus

end
end BlockPermanents.PieceProductSquares
