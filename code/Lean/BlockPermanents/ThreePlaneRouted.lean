import BlockPermanents.ThreePlaneWords
import BlockPermanents.ThreePlaneCap

/-! Resolving the last proper three-packet cut on an arbitrary isometric marked cable. -/
namespace BlockPermanents.ThreePlane
open Bend ThreeGeneralOpen ThreeLastRouted
open scoped BigOperators Matrix
noncomputable section

variable {I J : Type*}

open private allSlots from BlockPermanents.ThreeLastRouted in
private theorem stackLast_slice {d s k : ℕ} (E : Matrix (Fin d) (Fin s) ℂ)
    (hk : 1 ≤ k) (M : Word d k → Matrix (Word d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ t i, Symmetric (fun w => M t w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (hSlice : ∀ v j, ∃ c, E.mulVec c = fun b => N (allSlots hk (b,v)) j)
    (t : Word d k) (a : Fin d) (ij : I × J) :
    ∃ c, E.mulVec c = fun b : Fin d =>
      star (stackLast hk M N (t, (fun _ => a, fun _ => b)) ij) := by
  classical
  obtain ⟨i,j⟩ := ij
  choose c hc using fun v => hSlice v j
  let m (v : Word d (k-1)) := star (M t (allSlots hk (a,v)) i)
  refine ⟨∑ v, m v • c v, ?_⟩
  have he : E.mulVec (∑ v, m v • c v) = ∑ v, m v • E.mulVec (c v) := by
    change E.mulVecLin _ = ∑ v, m v • E.mulVecLin (c v)
    simp only [map_sum, map_smul]
  rw [he]
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, stackLast,
    routed_entry M N hM hN, star_sum, star_mul', star_star]
  rfl

open private stack_square trace_same from BlockPermanents.ThreeLastRouted in
/-- The last U halfweb on the actual mixed boundary splits into its trace
complement and the terminal cap, with reciprocal marked dimension. -/
theorem routed_resolution {d s k : ℕ} (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1)
    (hs : 0 < s) (hk : 1 ≤ k)
    (M : Word d k → Matrix (Word d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (D : Matrix (Word s k) J ℂ) (hfac : N = TensorCoordinates.power (Fin k) E * D)
    (hM : ∀ t i, Symmetric (fun w => M t w i)) (hN : ∀ j, Symmetric (fun w => N w j)) :
    ∑ t, Support.reflected (routed M N (ThreeSupport.lastProper k) t) =
      Support.reflected (perpendicular E (stackLast hk M N)) +
      (s : ℂ)⁻¹ • Support.reflected (terminal (stack M) N) := by
  rw [stack_square, ← trace_same hk M N hM hN]
  apply ThreePlane.resolve E hE hs _ (stackLast_slice E hk M N hM hN ?_)
  intro v j
  rw [hfac]
  exact power_slice hk E D v j

private theorem fixes_columns {d s n : ℕ} (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1)
    (F : Matrix (Fin d) (Fin n) ℂ) (hF : LinearMap.range F.mulVecLin ≤ LinearMap.range E.mulVecLin) :
    (E * Eᴴ) * F = F := by
  classical
  ext i j
  have hcol : (fun a => F a j) ∈ LinearMap.range F.mulVecLin :=
    ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl⟩
  obtain ⟨v,hv⟩ := hF hcol
  have fix : (E * Eᴴ).mulVec (E.mulVec v) = E.mulVec v := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hE]
  change E.mulVec v = _ at hv
  rw [hv] at fix
  exact congrFun fix i

/-- Two isometric frames with the same column space define the same orthogonal projector. -/
theorem frame_projector_eq {d s n : ℕ} (E : Matrix (Fin d) (Fin s) ℂ) (F : Matrix (Fin d) (Fin n) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) (h : LinearMap.range E.mulVecLin = LinearMap.range F.mulVecLin) :
    E * Eᴴ = F * Fᴴ := by
  have left : E * Eᴴ * F = F := fixes_columns E hE F h.ge
  have right : F * Fᴴ * E = E := fixes_columns F hF E h.le
  have h' : Eᴴ * (F * Fᴴ) = Eᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose right
  calc
    E * Eᴴ = E * (Eᴴ * (F * Fᴴ)) := by rw [h']
    _ = E * Eᴴ * F * Fᴴ := by simp only [Matrix.mul_assoc]
    _ = F * Fᴴ := by rw [left]

/-- The residual of the actual last cut depends only on the marked subspace:
two orthonormal frames of that space give the same output matrix. -/
theorem perpendicular_eq_of_range {d s : ℕ} {T I : Type*} [Fintype T] [DecidableEq T]
    (E F : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1)
    (h : LinearMap.range E.mulVecLin = LinearMap.range F.mulVecLin)
    (U : Matrix (T × ThreeLastCap.Pair d) I ℂ) :
    perpendicular E U = perpendicular F U := by
  have hc : planeCap (T := T) E = planeCap (T := T) F := by
    unfold planeCap
    rw [frame_projector_eq E F hE hF h]
  simp only [perpendicular, hc]

end
end BlockPermanents.ThreePlane
