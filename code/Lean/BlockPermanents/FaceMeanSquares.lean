import BlockPermanents.FaceStraightSquares
import BlockPermanents.FaceSlacks

/-! # Exact three- and four-face bounds with a spectator matching

The mean includes the squared brackets of all marked pairs. Each remainder is
the same weighted mean of the positive-order cuts on the discarded labels.
-/
namespace BlockPermanents.FaceMeanSquares
open FaceMeans FaceExit FaceStraightSquares
noncomputable section

variable {m d : ℕ}

private def threeCut {n : ℕ} (y : Input (n+3) d) : ℝ :=
  let D := survivor (y 0) (y (0 : Fin (n+2)).succ) (y (0 : Fin (n+1)).succ.succ)
  keepRemainder (fun _ : Fin 1 => D) (fun i : Fin n => y i.succ.succ.succ)

private def fourCut {n : ℕ} (y : Input (n+4) d) : ℝ :=
  let D := survivor (y 0) (y (0 : Fin (n+3)).succ) (y (0 : Fin (n+2)).succ.succ)
  keepRemainder ![D, y (0 : Fin (n+1)).succ.succ.succ]
    (fun i : Fin n => y i.succ.succ.succ.succ)

/-- Average of all cuts discarded when keeping the three-label survivor. -/
def tripleRemainder (x : Input m d) (r n : ℕ) : ℝ := mean x r (n+3) threeCut

/-- Average of all cuts discarded when the fourth active label is also kept. -/
def quadRemainder (x : Input m d) (r n : ℕ) : ℝ := mean x r (n+4) fourCut

private theorem mean_nonneg (x : Input m d) {r q : ℕ} (fit : 2*r+q ≤ m)
    {F : Input q d → ℝ} (h : ∀ y, 0 ≤ F y) : 0 ≤ mean x r q F := by
  rw [mean, FaceSampling.sample_eq (positions fit), Matchings.average]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _) (h _))

theorem tripleRemainder_nonneg (x : Input m d) {r n : ℕ} (fit : 2*r+(n+3) ≤ m) :
    0 ≤ tripleRemainder x r n :=
  mean_nonneg x fit (fun _ => keepRemainder_nonneg _ _)

theorem quadRemainder_nonneg (x : Input m d) {r n : ℕ} (fit : 2*r+(n+4) ≤ m) :
    0 ≤ quadRemainder x r n :=
  mean_nonneg x fit (fun _ => keepRemainder_nonneg _ _)

/-- Exact normalized three-face formula in (AA.2). -/
theorem triple_identity (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    {r n : ℕ} (fit : 2*r+(n+3) ≤ m) :
    mean x r (n+3) fullExit = mean x r 3 triple + tripleRemainder x r n := by
  let e := Fin.castLEEmb (by omega : 3 ≤ n+3)
  rw [← mean_restrict x fit e triple, tripleRemainder, ← FacePeel.mean_linear x fit]
  apply FaceSlacks.mean_congr x fit
  intro v
  exact keep_three_squares _ _ _ _ (fun _ => unit _)

/-- Exact normalized four-face formula in (AA.2). -/
theorem quad_identity (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    {r n : ℕ} (fit : 2*r+(n+4) ≤ m) :
    mean x r (n+4) fullExit = mean x r 4 quadruple + quadRemainder x r n := by
  let e := Fin.castLEEmb (by omega : 4 ≤ n+4)
  rw [← mean_restrict x fit e quadruple, quadRemainder, ← FacePeel.mean_linear x fit]
  apply FaceSlacks.mean_congr x fit
  intro v
  let y := active x v
  have h := keep_four_squares (y 0) (y (0 : Fin (n+3)).succ) (y (0 : Fin (n+2)).succ.succ)
    (y (0 : Fin (n+1)).succ.succ.succ) (fun i : Fin n => y i.succ.succ.succ.succ) (fun _ => unit _)
  have he : (Fin.cons (y (0 : Fin (n+1)).succ.succ.succ) (fun i : Fin n => y i.succ.succ.succ.succ) :
      Fin (n+1) → Fin d → ℂ) = fun i => y i.succ.succ.succ := by
    funext i
    exact Fin.cases (by rw [Fin.cons_zero]) (fun j => by rw [Fin.cons_succ]) i
  rw [he] at h
  exact h

end
end BlockPermanents.FaceMeanSquares
