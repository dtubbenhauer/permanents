import BlockPermanents.FourNativeTerminal

/-! The survivor clasp on the two outputs of the terminal half-map in Definition 5C.1. -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourExchangeKernel FourWireAlgebra FourNativeCap ThreeTransfer
open scoped Matrix
noncomputable section

/-- The fine clasp on packets 2 and 3 is absorbed by the clasp on packets 1, 2 and 3. -/
private theorem moved_triple (d k : ℕ) :
    movedPair (packets d k) (localClasp d k 2) * localClasp d k 3 = localClasp d k 3 := by
  have h : wires k (Equiv.swap 0 2) ∈ group k 3 := by
    rintro ⟨i,t⟩ hi
    change 3 ≤ i.val at hi
    change (Equiv.swap 0 2 i,t) = (i,t)
    rw [Equiv.swap_apply_of_ne_of_ne (by intro e; subst i; norm_num at hi)
      (by intro e; subst i; norm_num at hi)]
  have hs := (local_absorption d k 3 _ h).1
  simp only [movedPair, mul_assoc, hs, (FourActualAlgebra.fine_clasps d k).pe]

open private Emat part_spec upright_mul from BlockPermanents.FourNativeTerminal in
/-- On arbitrary rectangular feet, the terminal half v has symmetric output
across the two surviving packets. No positivity or Schur input is required. -/
theorem terminalV_fixed {d k : ℕ} {I J : Type*}
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :
    totalClasp d k k * terminalV M N = terminalV M N := by
  let p := totalClasp d k k
  have h := congrArg (matrix d k) (moved_triple d k)
  have e : matrix d k (localClasp d k 3) = upright (Emat d k) := part_spec _ _
  rw [map_mul, FourNativeSurvivor.matrix_moved, e, upright_mul] at h
  have fixes : survivor p * Emat d k = Emat d k := by
    ext x y
    simpa only [upright, if_true] using congrFun (congrFun h (x,x 0)) (y,x 0)
  ext t ij
  -- Restrict to one column to slide the clasp along the two surviving outputs.
  let m : Matrix (Triple d k) Unit ℂ := fun x _ => M x ij.1
  have slide := (half_survivor p (Emat d k * m) N).symm
  rw [← Matrix.mul_assoc, fixes] at slide
  exact congrFun (congrFun slide t) ((),ij.2)

end
end BlockPermanents.FourNative
