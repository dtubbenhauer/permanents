import BlockPermanents.FourGram
import BlockPermanents.TensorCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Naturality of the four-packet transfer under rectangular coordinate maps -/
namespace BlockPermanents.FourCovariance
open FourTarget FourGram
noncomputable section

/-- The tensor power of a coordinate map intertwines the representations of
every rational linear combination of thin-slot permutations. -/
theorem representation_natural {d e k : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    (u : U k) (x : (Slot k → Fin d) → ℂ) :
    rep e k u ((TensorCoordinates.power (Slot k) A).mulVec x) =
      (TensorCoordinates.power (Slot k) A).mulVec (rep d k u x) := by
  classical
  let T := (TensorCoordinates.power (Slot k) A).mulVecLin
  change rep e k u (T x) = T (rep d k u x)
  have wire (p : Wire k) : act e k p (T x) = T (act d k p x) :=
    TensorCoordinates.naturality (Slot k) A p x
  simp only [rep, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_rat_smul, wire]

/-- Applying the same complex coordinate map to every thin slot intertwines the
four-packet transfers. Both coordinate dimensions and the packet size are arbitrary. -/
theorem transfer_natural {d e k : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    (x : (Slot k → Fin d) → ℂ) :
    Q e k ((TensorCoordinates.power (Slot k) A).mulVec x) =
      (TensorCoordinates.power (Slot k) A).mulVec (Q d k x) := by
  simpa only [realize] using representation_natural A (formalQ k) x

end
end BlockPermanents.FourCovariance
