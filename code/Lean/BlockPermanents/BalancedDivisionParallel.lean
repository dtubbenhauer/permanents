import BlockPermanents.BalancedAssembly
import BlockPermanents.BalancedRoutes
import BlockPermanents.BendCoordinates

/-! The parallel packet correction on singly clasped inputs. -/
namespace BlockPermanents.BalancedDivision
open Bend BalancedPacket BendCoordinates
noncomputable section

open private clasp_two from BlockPermanents.BalancedRoutes in
private theorem bare_pair {K : Type*} [Fintype K] (x : K × K) (f : K × K → ℂ) :
    Matrix.mulVec (packetPair K) f x = (f x + f x.swap)/2 := by
  let e := letters K
  have hs : e.symm (e x ∘ Equiv.swap 0 1) = x.swap := by
    ext <;> simp (config := {decide := true}) [e, letters, finTwoArrowEquiv, Equiv.swap_apply_def]
  change (∑ y, packetPair K x y * f y) = _
  rw [← e.symm.sum_comp (fun y => packetPair K x y * f y)]
  change (∑ w, symClasp _ 2 (e x) (e (e.symm w)) * f (e.symm w)) = _
  simp only [Equiv.apply_symm_apply]
  rw [clasp_two (e x) (fun w => f (e.symm w)), Equiv.symm_apply_apply, hs]

private theorem internal_pair {d k : ℕ} (F G : Word d k → ℂ)
    (hF : Symmetric F) (hG : Symmetric G) (x : Word d k × Word d k) :
    (BalancedCorners.packetPair d k).mulVec (product F G) x =
      (F x.1 * G x.2 + F x.2 * G x.1)/2 := by
  have sep (a b : Word d k) :
      (∑ y : Word d k × Word d k, (symClasp d k a y.1 * symClasp d k b y.2) *
        (F y.1 * G y.2)) = F a * G b := by
    exact congrFun (tensor_product (symClasp d k) (symClasp d k) F G
      |>.trans (congrArg₂ product hF hG)) (a,b)
  change (∑ y : Word d k × Word d k, ((symClasp d k x.1 y.1 * symClasp d k x.2 y.2 + symClasp d k x.1 y.2 * symClasp d k x.2 y.1)/2) * (F y.1 * G y.2)) = _
  simp_rw [div_mul_eq_mul_div, add_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sep]
  have hr (y : Word d k × Word d k) :
      symClasp d k x.1 y.2 * symClasp d k x.2 y.1 = symClasp d k x.2 y.1 * symClasp d k x.1 y.2 :=
    mul_comm _ _
  simp_rw [hr]
  rw [sep]

/-- On symmetric packets the parallel coarse correction absorbs all four
internal clasps, so all three divisions can use the same correction kernel. -/
theorem straight_internal {d k : ℕ} (F G H J : Word d k → ℂ)
    (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H) (hJ : Symmetric J) :
    (straight (Word d k)).mulVec (fun y => (F y.1.1 * G y.1.2) * (H y.2.1 * J y.2.2)) =
    (tensor (BalancedCorners.packetPair d k) (BalancedCorners.packetPair d k)).mulVec
      (fun y => (F y.1.1 * G y.1.2) * (H y.2.1 * J y.2.2)) := by
  let f := product F G
  let g := product H J
  change (tensor (packetPair _) (packetPair _)).mulVec (product f g) = _
  rw [tensor_product, show (fun y : Boundary (Word d k) => (F y.1.1*G y.1.2)*(H y.2.1*J y.2.2))
    = product f g from rfl, tensor_product]
  funext x
  change Matrix.mulVec (packetPair _) f x.1 * Matrix.mulVec (packetPair _) g x.2 = _
  rw [bare_pair, bare_pair]
  change _ = (BalancedCorners.packetPair d k).mulVec (product F G) x.1 *
    (BalancedCorners.packetPair d k).mulVec (product H J) x.2
  rw [internal_pair F G hF hG, internal_pair H J hH hJ]
  rfl

end
end BlockPermanents.BalancedDivision
