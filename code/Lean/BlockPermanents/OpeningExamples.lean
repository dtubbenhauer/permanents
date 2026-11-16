import BlockPermanents.ThreeCoarse
import BlockPermanents.Bridges
import BlockPermanents.MarkedEdges

/-! # The whole-pair count and the 2+1 fork in Examples 1A.2 and 2A.3 -/
namespace BlockPermanents.OpeningExamples
open Closures Bend Quadratic
open scoped BigOperators Matrix
noncomputable section

/-- The whole and broken thin matchings of the all-ones example. -/
theorem whole_split_counts :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 2 × Fin 2) => (MarkedEdges.whole σ).card = 2)).card = 8 ∧
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 2 × Fin 2) => (MarkedEdges.whole σ).card = 0)).card = 16 := by
  decide

/-- Four identical unit columns, in a one-dimensional Gram space. -/
def atoms : Fin 4 → Fin 1 → ℂ := fun _ _ => 1

theorem gram_one (i j : Fin 4) : gram4 atoms i j = 1 := by simp [gram4, pair, atoms]

theorem all_ones_example :
    (gram4 atoms).permanent = 24 ∧ (blockMatrix (gram4 atoms)).permanent = 8 ∧
    (∑ i, ∑ j, Complex.normSq (singleCap atoms i j)) = 4 ∧
    (gram4 atoms).permanent - (blockMatrix (gram4 atoms)).permanent = 16 := by
  have hb (i j : Fin 2) : blockMatrix (gram4 atoms) i j = 2 := by
    norm_num [blockMatrix, Matrix.permanent, Matrix.submatrix_apply, gram_one, Fintype.card_perm, Nat.factorial]
  have fine : (gram4 atoms).permanent = 24 := by
    norm_num [Matrix.permanent, gram_one, Fintype.card_perm, Nat.factorial]
  have coarse : (blockMatrix (gram4 atoms)).permanent = 8 := by
    norm_num [Matrix.permanent, hb, Finset.prod_const, Fintype.card_perm, Nat.factorial]
  have cap (i j : Fin 1) : singleCap atoms i j = 2 := by norm_num [singleCap, atoms]; exact map_ofNat _ _
  norm_num [fine, coarse, cap, Complex.normSq_ofNat]

/-- The coarse permanent counts the whole permutations, and its difference
from the fine permanent counts precisely the split permutations in this example. -/
theorem whole_permanent_and_gap :
    (blockMatrix (gram4 atoms)).permanent =
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 2 × Fin 2) => (MarkedEdges.whole σ).card = 2)).card : ℂ) ∧
    (gram4 atoms).permanent - (blockMatrix (gram4 atoms)).permanent =
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 2 × Fin 2) => (MarkedEdges.whole σ).card = 0)).card : ℂ) := by
  rw [whole_split_counts.1, whole_split_counts.2]
  exact ⟨all_ones_example.2.1, all_ones_example.2.2.2⟩

open private permanent_three from BlockPermanents.ThreeCoarse in
private theorem clasp_xxy {d : ℕ} (x y : Fin d → ℂ) (w : Word d 3) :
    clasp (pureWord ![x,x,y]) w = (1/3:ℂ) *
      (x (w 0)*x (w 1)*y (w 2) + x (w 0)*y (w 1)*x (w 2) + y (w 0)*x (w 1)*x (w 2)) := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j => (![x,x,y] : Fin 3 → Fin d → ℂ) i (w j)
  have h : orderSum ![x,x,y] w = A.permanent := rfl
  rw [clasp, sumSlots_pure, h, permanent_three]
  have h₀ (j) : A 0 j = x (w j) := rfl
  have h₁ (j) : A 1 j = x (w j) := rfl
  have h₂ (j) : A 2 j = y (w j) := rfl
  norm_num [h₀, h₁, h₂, Nat.factorial]
  ring

/-- The actual 2+1 fork on the three-clasped tensor. The average of the
two left placements is the indicated x ⊙ y. Coordinates may be arbitrary. -/
theorem fork_two_one {d : ℕ} (x y : Fin d → ℂ) (u : Word d 2) (v : Word d 1) :
    (wordFork d 3 1 (by decide)).mulVec (pureWord ![x,x,y]) (u,v) =
      (1/3:ℂ) * (x (u 0)*x (u 1)) * y (v 0) +
      (2/3:ℂ) * ((x (u 0)*y (u 1)+y (u 0)*x (u 1))/2) * x (v 0) := by
  let w : Word d 3 := Fin.append u v
  change (symClasp d 3).mulVec (pureWord ![x,x,y]) w = _
  rw [Bridges.symClasp_action, clasp_xxy]
  have w₀ : w 0 = u 0 := Fin.append_left u v 0
  have w₁ : w 1 = u 1 := Fin.append_left u v 1
  have w₂ : w 2 = v 0 := Fin.append_right u v 0
  rw [w₀,w₁,w₂]
  ring

end
end BlockPermanents.OpeningExamples
