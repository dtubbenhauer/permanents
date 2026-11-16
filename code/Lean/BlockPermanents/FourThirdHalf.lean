import BlockPermanents.FourMergedHalf
import BlockPermanents.FourMergedClasp
import BlockPermanents.FourThirdBoundary

/-! # The spectator-free half-map for the third proper-cut family -/
namespace BlockPermanents.FourNative
open Bend FourTarget FourRoutes FourExchangeKernel ThreeGeneralOpen Support
open scoped Matrix BigOperators
noncomputable section

/-- Concatenate the three ordinary packets in the order 1, 2, 3. -/
def joinThree (d k : ℕ) : Matrix (Word d (3*k)) (Triple d k) ℂ :=
  fun w x => if w = (fun i => x i.divNat i.modNat) then 1 else 0

private theorem join_slice {d k : ℕ} (s : Word d ((3-3)*k)) :
    slice 3 (by decide) s = joinThree d k := by
  have empty : IsEmpty (Fin ((3-3)*k)) := by simpa using (inferInstance : IsEmpty (Fin 0))
  letI := empty
  ext w x
  simp only [slice, joinThree, Subsingleton.elim (idle 3 x) s, true_and, active]
  rfl

/-- Vᵣ first averages the ordinary packets, merges all three through P₃ₖ,
and caps r strands against the fourth packet. Only the two through words
remain at the output. -/
def thirdProperHalf {d k : ℕ} (r : CutIndex (3*k) k) :
    Matrix (Word d (3*k-r) × Word d (k-r)) (Triple d k × Word d k) ℂ :=
  routed (fun _ : Unit => symClasp d (3*k) *
    (joinThree d k * (ordinaryFoot d k * ZeroCap.inner d k 3))) (symClasp d k) r ()

private theorem half_entry {d k : ℕ} (r : CutIndex (3*k) k) (s : Word d ((3-3)*k))
    (w : Word d (3*k-r) × Word d (k-r)) (i : Triple d k × Word d k) :
    mergedProperHalf 3 (by decide) (ordinaryFoot d k * ZeroCap.inner d k 3) (symClasp d k) r (s,w) i =
      thirdProperHalf r w i := by
  unfold thirdProperHalf
  rw [routed_merge_clasp (fun _ : Unit => joinThree d k * (ordinaryFoot d k * ZeroCap.inner d k 3))]
  simp only [mergedProperHalf, routed, join_slice]

private theorem merged_third_square {d k : ℕ} (r : CutIndex (3*k) k) :
    reflected (mergedProperHalf 3 (by decide) (ordinaryFoot d k * ZeroCap.inner d k 3) (symClasp d k) r) =
      reflected (thirdProperHalf (d:=d) r) := by
  have empty : IsEmpty (Fin ((3-3)*k)) := by simpa using (inferInstance : IsEmpty (Fin 0))
  letI := empty
  letI : Unique (Word d ((3-3)*k)) := ⟨⟨isEmptyElim⟩, fun _ => Subsingleton.elim _ _⟩
  ext i j
  simp only [reflected, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_unique, half_entry]

/-- On the four packet clasps each native third exchange bends to the square
of the displayed three-packet merge. -/
theorem read_third_cut {d k : ℕ} (r : CutIndex (3*k) k) :
    read (ZeroCap.inner d k 3) (symClasp d k)
      (localClasp d k 3 * act d k (FourThickSlots.exchange k 3 (by decide) r) * localClasp d k 3) =
    reflected (thirdProperHalf (d:=d) r) := by
  rw [third_boundary _ _ (clasps_fixed d k), read_merged_cut, merged_third_square]

end
end BlockPermanents.FourNative
