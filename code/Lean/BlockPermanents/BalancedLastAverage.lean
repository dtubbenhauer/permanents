import BlockPermanents.BalancedDivisionDefect
import BlockPermanents.BalancedDivisionParallel
import BlockPermanents.BalancedDivisionPair

/-! Averaging the three balanced moves on internally symmetric upright inputs.
Changing divisions permutes the actual word coordinates of all four packets. -/
namespace BlockPermanents.BalancedDivision
open BalancedPacket BalancedAssembly Bend Matrix
open scoped Matrix
noncomputable section

private def cyclic {K : Type*} : Boundary K ≃ Boundary K where
  toFun := rotate
  invFun x := rotate (rotate x)
  left_inv _ := rfl
  right_inv _ := rfl

private def parallelInternal (d k : ℕ) :=
  (a k^2) • pairFine d k -
  (4:ℂ) • BendCoordinates.tensor (BalancedCorners.packetPair d k) (BalancedCorners.packetPair d k)

private def moved (d k : ℕ) :=
  defect d k - parallelInternal d k +
  (1/2:ℂ) • (BalancedCorners.correction false d k + BalancedCorners.correction true d k)

/-- Relabel the parallel division and the two actual crossing corrections.
Swapping the order of the last edge preserves both of its pair clasps. -/
private theorem cycle {d k : ℕ} (x y : B d k) :
    parallelInternal d k (rotate x) (rotate y) = BalancedCorners.correction false d k x y ∧
    BalancedCorners.correction false d k (rotate x) (rotate y) =
      BalancedCorners.correction true d k x y ∧
    BalancedCorners.correction true d k (rotate x) (rotate y) = parallelInternal d k x y := by
  rcases x with ⟨⟨xa,xb⟩,xc,xe⟩
  rcases y with ⟨⟨ya,yb⟩,yc,ye⟩
  simp only [parallelInternal, BalancedCorners.correction, pairFine, a,
    BalancedOpen.productFine, BalancedOpen.productOperator, BalancedOpen.arrange,
    rotate, Bool.false_eq_true, if_false, if_true, BendCoordinates.tensor,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [fine_pair_swap xb xe yb ye, packet_pair_swap xb xe yb ye,
    fine_pair_swap xb xc yb yc, packet_pair_swap xb xc yb yc]
  simp

private theorem moved_sum {d k : ℕ} (x y : B d k) :
    moved d k x y + moved d k (rotate x) (rotate y) +
      moved d k (rotate (rotate x)) (rotate (rotate y)) = 3 * defect d k x y := by
  obtain ⟨hp,hb,hd⟩ := cycle x y
  obtain ⟨hp',hb',hd'⟩ := cycle (rotate x) (rotate y)
  simp only [moved, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hp', hb', hd', hp, hb, hd, defect_rotate, defect_rotate, defect_rotate]
  ring

/-- Internally symmetric packets at the four upright feet, before choosing a division. -/
def packetProduct {K : Type*} (F G H J : K → ℂ) (y : Boundary K) : ℂ :=
  (F y.1.1 * G y.1.2) * (H y.2.1 * J y.2.2)

private theorem marked_action {d k : ℕ} (F G H J : Word d k → ℂ)
    (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H) (hJ : Symmetric J) :
    (marked d k).mulVec (packetProduct F G H J) =
      (moved d k).mulVec (packetProduct F G H J) := by
  simp only [marked, moved, parallelCorrection, parallelInternal, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec_assoc]
  rw [show (straight (K d k)).mulVec (packetProduct F G H J) =
    (BendCoordinates.tensor (BalancedCorners.packetPair d k) (BalancedCorners.packetPair d k)).mulVec
       (packetProduct F G H J) from straight_internal F G H J hF hG hH hJ]

private theorem moved_action {d k : ℕ} (F G H J : Word d k → ℂ) (x : B d k) :
    (moved d k).mulVec (packetProduct F H J G) (rotate x) =
      ∑ y, moved d k (rotate x) (rotate y) * packetProduct F G H J y := by
  change (∑ y, moved d k (rotate x) y * packetProduct F H J G y) = _
  rw [← cyclic.sum_comp (fun y => moved d k (rotate x) y * packetProduct F H J G y)]
  apply Finset.sum_congr rfl
  intro y _
  change _ * packetProduct F H J G (rotate y) = _ * packetProduct F G H J y
  congr 1
  unfold packetProduct rotate
  ring

private theorem moved_action_twice {d k : ℕ} (F G H J : Word d k → ℂ) (x : B d k) :
    (moved d k).mulVec (packetProduct F J G H) (rotate (rotate x)) =
      ∑ y, moved d k (rotate (rotate x)) (rotate (rotate y)) * packetProduct F G H J y := by
  rw [moved_action F H J G]
  rw [← cyclic.sum_comp (fun y => moved d k (rotate (rotate x)) (rotate y) * packetProduct F H J G y)]
  apply Finset.sum_congr rfl
  intro y _
  change _ * packetProduct F H J G (rotate y) = _ * packetProduct F G H J y
  congr 1
  unfold packetProduct rotate
  ring

/-- Equation cubic-move as an equality of the actual upright output vectors.
The three divisions occur in cyclic order around the first fixed packet. -/
theorem three_division_average {d k : ℕ} (F G H J : Word d k → ℂ)
    (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H) (hJ : Symmetric J)
    (x : B d k) :
    (marked d k).mulVec (packetProduct F G H J) x +
      (marked d k).mulVec (packetProduct F H J G) (rotate x) +
      (marked d k).mulVec (packetProduct F J G H) (rotate (rotate x)) =
      3 * (defect d k).mulVec (packetProduct F G H J) x := by
  rw [marked_action F G H J hF hG hH hJ, marked_action F H J G hF hH hJ hG,
    marked_action F J G H hF hJ hG hH, moved_action, moved_action_twice]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← add_mul, ← add_mul, moved_sum]
  ring

end
end BlockPermanents.BalancedDivision
