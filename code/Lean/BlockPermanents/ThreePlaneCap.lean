import BlockPermanents.ThreeLastCap

/-! # The supported cap for an arbitrary marked subspace -/
namespace BlockPermanents.ThreePlane
open ThreeLastCap
open scoped BigOperators Matrix
noncomputable section

variable {T I : Type*} [Fintype T] [DecidableEq T] {d s : ℕ}

/-- On one ordinary and one dual survivor, insert the orthogonal projector
onto the marked subspace and take the trace, keeping the spectator through. -/
def planeCap (E : Matrix (Fin d) (Fin s) ℂ) : Matrix T (T × Pair d) ℂ :=
  fun t u => if t = u.1 then (E * Eᴴ) (u.2.2 0) (u.2.1 0) else 0

omit [Fintype T] in
/-- Changing the orthonormal basis within the marked subspace leaves the cap fixed. -/
theorem cap_frame_change (E : Matrix (Fin d) (Fin s) ℂ)
    (V : Matrix (Fin s) (Fin s) ℂ) (hV : V * Vᴴ = 1) :
    planeCap (T:=T) (E * V) = planeCap E := by
  ext t u
  simp only [planeCap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]

private theorem cap_apply (E : Matrix (Fin d) (Fin s) ℂ) (U : Matrix (T × Pair d) I ℂ)
    (t : T) (j : I) :
    (planeCap (T:=T) E * U : Matrix T I ℂ) t j =
      ∑ a : Fin d, ∑ b : Fin d, (E * Eᴴ) b a * U (t, (fun _ => a, fun _ => b)) j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single t]
  · simp only [planeCap, if_true]
    let e := (Equiv.funUnique (Fin 1) (Fin d)).symm
    have h := (e.prodCongr e).sum_comp
      (fun p : Pair d => (E * Eᴴ) (p.2 0) (p.1 0) * U (t,p) j)
    rw [← h, Fintype.sum_prod_type]
    rfl
  · intro u _ hu
    simp [planeCap, Ne.symm hu]
  · simp

/-- The bubble equals the rank of the subspace, also in a rotated frame. -/
theorem cap_bubble (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1) :
    planeCap (T := T) E * (planeCap E)ᴴ = (s : ℂ) • (1 : Matrix T T ℂ) := by
  let P := E * Eᴴ
  have hstar : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
  have hp : Pᴴ * P = P := by
    rw [hstar]
    change E * Eᴴ * (E * Eᴴ) = E * Eᴴ
    rw [Matrix.mul_assoc E, ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul]
  have hsum : (∑ a, ∑ b, P b a * star (P b a)) = (s : ℂ) := by
    calc
      _ = (Pᴴ * P).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
        simp only [mul_comm]
      _ = (s : ℂ) := by rw [hp]; simp [P, Matrix.trace_mul_comm E, hE]
  ext t u
  rw [cap_apply]
  by_cases h : t = u
  · subst u
    simpa [Matrix.conjTranspose_apply, planeCap, Matrix.smul_apply, P] using hsum
  · simp [Matrix.conjTranspose_apply, planeCap, Ne.symm h, h, Matrix.smul_apply, Matrix.one_apply]

/-- If each conjugated marked slice is in the span of E, the projected cap
closes the same tensor as the ordinary full trace. -/
theorem cap_eq_trace (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1)
    (U : Matrix (T × Pair d) I ℂ)
    (hu : ∀ t a j, ∃ c : Fin s → ℂ, E.mulVec c =
      fun b : Fin d => star (U (t, (fun _ => a, fun _ => b)) j)) :
    planeCap (T:=T) E * U = fullTrace U := by
  let P := E * Eᴴ
  have hstar : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
  ext t j
  rw [cap_apply]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨c,hc⟩ := hu t a j
  have hfix : P.mulVec (E.mulVec c) = E.mulVec c := by
    rw [Matrix.mulVec_mulVec, show P * E = E by simp [P, Matrix.mul_assoc, hE]]
  rw [hc] at hfix
  have e := congrArg (starRingEnd ℂ) (congrFun hfix a)
  have hp (b : Fin d) : star (P a b) = P b a := congrFun (congrFun hstar b) a
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, Complex.star_def,
    Complex.conj_conj, ← Complex.star_def, star_star, hp, ThreeLastCap.diagonal] using e

/-- The residual thin half after removing the component along the trace cup. -/
def perpendicular (E : Matrix (Fin d) (Fin s) ℂ) (U : Matrix (T × Pair d) I ℂ) :=
  ((1 : Matrix (T × Pair d) (T × Pair d) ℂ) - (s : ℂ)⁻¹ • ((planeCap (T:=T) E)ᴴ * planeCap E)) * U

theorem resolve (E : Matrix (Fin d) (Fin s) ℂ) (hE : Eᴴ * E = 1) (hs : 0 < s)
    (U : Matrix (T × Pair d) I ℂ)
    (hu : ∀ t a j, ∃ c : Fin s → ℂ, E.mulVec c =
      fun b : Fin d => star (U (t, (fun _ => a, fun _ => b)) j)) :
    Support.reflected U = Support.reflected (perpendicular E U) +
      (s : ℂ)⁻¹ • Support.reflected (ThreeLastCap.fullTrace U) := by
  simpa only [perpendicular, cap_eq_trace E hE U hu] using
    Support.resolve_last_cap (planeCap E) U s hs (cap_bubble E hE)

end
end BlockPermanents.ThreePlane
