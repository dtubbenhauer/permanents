import BlockPermanents.BalancedPacketEnergy
import BlockPermanents.BalancedAssembly

/-! Scalar form of the balanced four-packet opening on an arbitrary mixed
tensor, including the interference between the four single-packet exits
and the two fully paired exits. -/
namespace BlockPermanents.BalancedEvaluation
open Bend Support SchurNormalization BalancedOpen BalancedCorners BalancedAssembly
open scoped BigOperators Matrix
noncomputable section

private def evaluate {I : Type*} [Fintype I] (z : I → ℂ) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun A := quadratic A z
  map_add' A B := by simp [quadratic,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [quadratic,Matrix.smul_apply,smul_eq_mul,mul_left_comm _ c,mul_assoc,Finset.mul_sum]
    rfl

private lemma glue {I T : Type*} [Fintype I] [Fintype T] (z : I → ℂ) (M : Matrix T I ℂ) :
    evaluate z (reflected M) = (energy (M.mulVec z) : ℂ) := by
  change quadratic (Mᴴ*M) z=_
  rw [quadratic_reflected]
  exact (map_sum Complex.ofRealHom _ _).symm

def fineEnergy {d k : ℕ} (z : B d k → ℂ) : ℝ :=
  ∑ r ∈ Finset.univ.erase (zeroCut (k+k)), (weight (k+k) (k+k) r : ℝ) * energy ((totalCap d k r).mulVec z)

def edgeEnergy {d k : ℕ} (flip : Bool) (z : B d k → ℂ) : ℝ :=
  ∑ u ∈ (corners k)ᶜ, ((weight k k u.1 : ℝ)*(weight k k u.2 : ℝ)) * energy ((productCap flip d k u.1 u.2).mulVec z)

private theorem fine_eval {d k : ℕ} (z : B d k → ℂ) :
    evaluate z (fineProper d k) = (fineEnergy z : ℂ) := by
  simp [fineProper,fineEnergy,glue]

private theorem edge_eval {d k : ℕ} (f : Bool) (z : B d k → ℂ) :
    evaluate z (edgeProper f d k) = (edgeEnergy f z : ℂ) := by
  simp [edgeProper,weighted,edgeEnergy,glue]

theorem opening {d k : ℕ} (hk : 0<k) (hs : HomogeneousSchur d k k)
    (hb : HomogeneousSchur d (k+k) (k+k))
    (hp : HomogeneousSchur (Fintype.card (K d k)) 2 2) (z : B d k → ℂ) :
    (quadratic (partialTranspose (marked d k)) z).re =
      ((k+k).choose k : ℝ)^2 * fineEnergy z + (edgeEnergy false z + edgeEnergy true z)/2 -
      energy (BalancedPacket.oneSum z) - Complex.normSq (BalancedRoutes.Ndirect z + BalancedRoutes.Ncross z) := by
  have h := congrArg (evaluate z) (BalancedAssembly.opening hk hs hb hp)
  simp only [map_add,map_sub,map_smul,smul_eq_mul,fine_eval,edge_eval,glue] at h
  change (evaluate z (partialTranspose (marked d k))).re=_
  rw [h]
  rw [← BalancedPacket.one_energy z,← BalancedPacket.two_energy z]
  simp [a,←Complex.ofReal_pow,←Complex.ofReal_natCast]
  ring

end
end BlockPermanents.BalancedEvaluation
