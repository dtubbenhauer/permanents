import BlockPermanents.FourNativeBoundary
import BlockPermanents.FourThickJoint

/-! # The ordinary packet average at the two feet of a proper cut -/
namespace BlockPermanents.FourNative
open Bend FourTarget FourRoutes FourExchangeKernel FourWireAlgebra FourAdjoints
open ThreeTransfer ThreeGeneralOpen FourThickCompression FourThickJoint
open scoped Matrix
noncomputable section

/-- The ordinary three-packet average in word coordinates. The marked packet
is left idle, as expressed by `ordinaryFoot_spec`. -/
def ordinaryFoot (d k : ℕ) : Matrix (Triple d k) (Triple d k) ℂ :=
  Classical.choose (getUpright (average_ordinary d k))

theorem ordinaryFoot_spec (d k : ℕ) :
    matrix d k (ordinary (packets d k)) = upright (ordinaryFoot d k) :=
  Classical.choose_spec (getUpright (average_ordinary d k))

private theorem read_ordinary {d k : ℕ} {I J : Type*}
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) (A : Op d k) :
    read M N (sand (ordinary (packets d k)) A) =
      read (ordinaryFoot d k * M) N A := by
  let F := ordinary (packets d k)
  have hF : (matrix d k F)ᴴ = matrix d k F := reflected_matrix (ordinary_self _ _)
  have hleg : matrix d k F * legs M N = legs (ordinaryFoot d k * M) N := by
    rw [ordinaryFoot_spec, upright_legs]
  change partialTranspose ((legs M N)ᴴ * matrix d k (F * A * F) * legs M N) =
    partialTranspose ((legs (ordinaryFoot d k * M) N)ᴴ * matrix d k A *
      legs (ordinaryFoot d k * M) N)
  rw [← hleg, Matrix.conjTranspose_mul, hF, map_mul, map_mul]
  simp only [Matrix.mul_assoc]

/-- On a packet-symmetric boundary one may put the marked clasp at both
ends of the exchange. The ordinary packet average acts on the ordinary foot. -/
theorem proper_boundary {d k : ℕ} {I J : Type*}
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (fixed : matrix d k (W d k) * legs M N = legs M N)
    (n : ℕ) (hn : n ≤ 3) (A : Op d k) :
    read M N (sand (ordinary (packets d k)) (localClasp d k n * A * localClasp d k n)) =
      read (ordinaryFoot d k * M) N (FourThickSlots.block d k n * A * FourThickSlots.block d k n) := by
  have h := surround (F := ordinary (packets d k))
    (compressed_block d k n hn A) (W_comm_triple d k)
  rw [← compressed_read M N fixed, ← h, compressed_read M N fixed, read_ordinary]

end
end BlockPermanents.FourNative
