import BlockPermanents.RoutedGluing

/-! # The last-cap monomials before averaging the internal cable slots -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

theorem one_port {N d : ℕ} (S : Finset (Fin d)) (p q : Perm (Cable (Fin (N+1)) 1))
    {f : Bend.Word d (N+1) → ℂ} (hf : Bend.Symmetric f) (w : Bend.Word d (N+1)) :
    Closures.clasp (routedCap S 1 p (reflectedCap S 1 q f)) w =
      (if p (q.symm none) = none then (S.card : ℂ) else (occupied S w).card / (N+1 : ℂ)) * f w := by
  let u : Perm (Option (Fin (N+1))) := q.symm.trans p
  rw [glued]
  change Closures.clasp (trace S (wire S u ∅) f) w = _
  rw [trace_wire]
  let v := u none
  have sc (a : ℂ) (z : Bend.Word d (N+1) → ℂ) :
      Closures.clasp (fun t => a*z t) w=a*Closures.clasp z w := by
    simp only [Closures.clasp,Closures.sumSlots,←Finset.mul_sum]; ring
  rw [sc,clasp_wire _ _ _ hf w]
  change _ = (if u none=none then _ else _) * f w
  cases h : u none with
  | none =>
    have hm : nextMarks u ∅ = ∅ := by simp [nextMarks,h]
    rw [hm]
    simp
  | some i =>
    have hm : nextMarks u ∅ = {i} := by simp [nextMarks,h]
    rw [hm]
    simp

end
end BlockPermanents.RoutedTrace
