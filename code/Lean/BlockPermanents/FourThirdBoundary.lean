import BlockPermanents.FourProperBoundary
import BlockPermanents.FourActualAlgebra

/-! # The ordinary packet average at the full three-packet merge -/
namespace BlockPermanents.FourNative
open Bend FourTarget FourRoutes FourExchangeKernel FourWireAlgebra TransferBlocks
open ThreeGeneralOpen FourThickCompression
open scoped Matrix
noncomputable section

/-- The full 3k-clasp absorbs the packet average on either side. -/
theorem triple_absorbs_ordinary (d k : ℕ) :
    ordinary (packets d k) * localClasp d k 3 = localClasp d k 3 ∧
    localClasp d k 3 * ordinary (packets d k) = localClasp d k 3 := by
  have c := FourActualAlgebra.fine_clasps d k
  constructor
  · simp only [ordinary,triple,smul_mul_assoc,add_mul,mul_assoc,one_mul,c.uE,c.vE]
    module
  · simp only [ordinary,triple,mul_smul_comm,mul_add,← mul_assoc,mul_one,c.Eu,c.Ev]
    module

/-- On the clasped boundary, insert the packet average at the foot of the
third family and the marked clasp at both ends of the exchange. -/
theorem third_boundary {d k : ℕ} {I J : Type*}
    (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (fixed : matrix d k (W d k) * legs M N = legs M N) (A : Op d k) :
    read M N (localClasp d k 3 * A * localClasp d k 3) =
      read (ordinaryFoot d k * M) N (FourThickSlots.block d k 3 * A * FourThickSlots.block d k 3) := by
  let E := localClasp d k 3
  let F := ordinary (packets d k)
  obtain ⟨fe,ef⟩ := triple_absorbs_ordinary d k
  have h : sand F (E * A * E) = E * A * E := by
    change F * (E * A * E) * F = _
    calc
      _ = (F * E) * A * (E * F) := by simp only [mul_assoc]
      _ = _ := by rw [show F*E=E from fe,show E*F=E from ef]
  exact (congrArg (read M N) h).symm.trans (proper_boundary M N fixed 3 (by decide) A)

end
end BlockPermanents.FourNative
