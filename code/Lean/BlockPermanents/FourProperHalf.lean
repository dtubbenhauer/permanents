import BlockPermanents.FourExchangeRoutes
import BlockPermanents.FourNativeFull

/-! The first proper cut bends packet 4 against packet 1. The open rows keep
packets 2 and 3 in order, followed by the two remaining through words. -/
namespace BlockPermanents.FourNative
open FourTarget FourRoutes FourExchangeKernel Bend ThreeGeneralOpen
open scoped BigOperators Matrix
noncomputable section
variable {d k : ℕ} {I J : Type*}

/-- Slice the two ordinary spectators, and join the two active cables by the
word cap of size r. The marked input has the dual action after bending. -/
def properHalf (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (1*k) k) :
    Matrix (Word d ((3-1)*k) × (Word d (1*k-r) × Word d (k-r))) (I×J) ℂ :=
  fun row col => routed (fun s => slice 1 (by decide) s * M) N r row.1 row.2 col

private theorem half_foot (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (1*k) k) (s : Word d ((3-1)*k)) :
    FourExchangeKernel.half 1 (by decide) r s * legs M (dual N) =
      routed (fun z => slice 1 (by decide) z * M) N r s := by
  rw [half_as_route,Matrix.mul_assoc,upright_legs]
  rfl

open private bend_legs from BlockPermanents.ThreeGeneralOpen in
/-- The native exchange on the two clasped active cables bends to the Gram
matrix of the single half, summing over all of its output rows. -/
theorem read_block_cut (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex (1*k) k) :
    read M N (FourThickSlots.block d k 1 *
      act d k (FourThickSlots.exchange k 1 (by decide) r) * FourThickSlots.block d k 1) =
        Support.reflected (properHalf M N r) := by
  let A := FourThickSlots.block d k 1 *
    act d k (FourThickSlots.exchange k 1 (by decide) r) * FourThickSlots.block d k 1
  change partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N) = _
  have h : partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N) =
      (legs M (dual N))ᴴ * partialTranspose (matrix d k A) * legs M (dual N) :=
    bend_legs M N _
  rw [h, bent_exchange (by decide : 1≤3) r, Matrix.mul_sum,Matrix.sum_mul]
  have congruence (s : Word d ((3-1)*k)) :
      (legs M (dual N))ᴴ * Support.reflected (FourExchangeKernel.half 1 (by decide) r s) *
        legs M (dual N) =
      Support.reflected (routed (fun z => slice 1 (by decide) z * M) N r s) := by
    rw [← half_foot]
    simp only [Support.reflected,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  simp_rw [congruence]
  ext i j
  simp only [Support.reflected, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, properHalf]

end
end BlockPermanents.FourNative
