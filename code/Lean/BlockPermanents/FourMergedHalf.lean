import BlockPermanents.FourExchangeRoutes
import BlockPermanents.FourNativeFull

/-! Proper cuts on a merged ordinary cable. The open rows keep the idle
packets in order, followed by the ordinary and marked through words. -/
namespace BlockPermanents.FourNative
open FourTarget FourRoutes FourExchangeKernel Bend ThreeGeneralOpen
open scoped BigOperators Matrix
noncomputable section
variable {d k : ℕ} {I J : Type*}

/-- Keep the ordinary spectators and join the two active cables by the
word cap of size r. The marked input has the dual action after bending. -/
def mergedProperHalf (n : ℕ) (hn : n ≤ 3) (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (n*k) k) :
    Matrix (Word d ((3-n)*k) × (Word d (n*k-r) × Word d (k-r))) (I×J) ℂ :=
  fun row col => routed (fun s => slice n hn s * M) N r row.1 row.2 col

private theorem merged_half_foot (n : ℕ) (hn : n ≤ 3) (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (n*k) k) (s : Word d ((3-n)*k)) :
    FourExchangeKernel.half n hn r s * legs M (dual N) =
      routed (fun z => slice n hn z * M) N r s := by
  rw [half_as_route,Matrix.mul_assoc,upright_legs]
  rfl

open private bend_legs from BlockPermanents.ThreeGeneralOpen in
/-- The native exchange on the two clasped active cables bends to the Gram
matrix of the single half, summing over all of its output rows. -/
theorem read_merged_cut (n : ℕ) (hn : n ≤ 3) (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (n*k) k) :
    read M N (FourThickSlots.block d k n *
      act d k (FourThickSlots.exchange k n hn r) * FourThickSlots.block d k n) =
        Support.reflected (mergedProperHalf n hn M N r) := by
  let A := FourThickSlots.block d k n *
    act d k (FourThickSlots.exchange k n hn r) * FourThickSlots.block d k n
  change partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N) = _
  have h : partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N) =
      (legs M (dual N))ᴴ * partialTranspose (matrix d k A) * legs M (dual N) :=
    bend_legs M N _
  rw [h, bent_exchange hn r, Matrix.mul_sum,Matrix.sum_mul]
  have congruence (s : Word d ((3-n)*k)) :
      (legs M (dual N))ᴴ * Support.reflected (FourExchangeKernel.half n hn r s) *
        legs M (dual N) =
      Support.reflected (routed (fun z => slice n hn z * M) N r s) := by
    rw [← merged_half_foot n hn]
    simp only [Support.reflected,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simp_rw [congruence]
  ext i j
  simp only [Support.reflected, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, mergedProperHalf]

end
end BlockPermanents.FourNative
