import BlockPermanents.ForcedQuadratics
import BlockPermanents.ForcedWitness

/-! # The forced-edge certificate in tensor and coefficient coordinates

Each summand in the evaluator is obtained by opening precisely the chosen
whole edges, with the unused labels retained on their original boundaries.
-/
namespace BlockPermanents.ForcedCertificate
open Negative Occupation ForcedWitness ForcedRoutes ForcedQuadratics
noncomputable section

/-- The normalized sum of all routings which preserve the selected pairs,
labeling the forced blocks by their positions in the assignment. -/
def constrained {α β : Type} (x : α → Quad) (y : β → Quad) (t : Assignment α β) : ℚ := by
  classical
  let n := 2*(t.left.map x).length
  let I := Fin t.edges.length
  let R := Fin n
  let a (i : I) := amplitude (x (t.edges.get i).1)
  let b (i : I) := amplitude (y (t.edges.get i).2)
  exact (∑ p : {p : Equiv.Perm (Slots I R) // preserves p},
    contraction (tensor a (residual n (t.left.map x)))
      (tensor b (residual n (t.right.map y))) p.1) / 2^(t.edges.length+t.left.length)

theorem forcedWeight_eq_constrained {α β : Type} (x : α → Quad) (y : β → Quad)
    (xs : List α) (ys : List β) (len : xs.length = ys.length)
    (t : Assignment α β) (ht : t ∈ assignments xs ys) :
    forcedWeight x y t = constrained x y t := by
  have part := partition xs ys t ht
  have hl := part.1.length_eq
  have hr := part.2.length_eq
  simp only [List.length_append,List.length_map] at hl hr
  have he : (t.left.map x).length = (t.right.map y).length := by simp; omega
  have h := forced_weight (fun i : Fin t.edges.length => x (t.edges.get i).1)
    (fun i => y (t.edges.get i).2) (t.left.map x) (t.right.map y) he
  simp only [List.length_map,Fintype.card_fin] at h
  have hp : (∏ i : Fin t.edges.length, gram (x (t.edges.get i).1) (y (t.edges.get i).2)) =
      (t.edges.map fun e => gram (x e.1) (y e.2)).prod := by
    rw [← Fin.prod_ofFn]
    exact congrArg List.prod (List.ofFn_getElem_eq_map t.edges (fun e => gram (x e.1) (y e.2)))
  rw [hp] at h
  exact h.symm

/-- On the witness the rational signed transfer is coefficient extraction
on the polynomial whose contributions are the constrained tensor sums. -/
theorem marked_polynomial (t : Fin 5) :
    witnessRead t = ((List.range 5).map fun h =>
      (5 : ℚ)/(2*(5-h : ℕ)) *
      (polynomial MarkedWitness.five MarkedWitness.five t t labels labels).coeff h).sum :=
  (run_correct 5 MarkedWitness.five MarkedWitness.five t t labels labels).trans
    (evaluate_eq 5 MarkedWitness.five MarkedWitness.five t t labels labels)

end
end BlockPermanents.ForcedCertificate
