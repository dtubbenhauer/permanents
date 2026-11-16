import BlockPermanents.Routings
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! # The projector for a possibly singular column of reflected caps (Section 4B) -/
namespace BlockPermanents.GramInverse
open Matrix
open scoped Matrix ComplexOrder
noncomputable section
variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν]

/-- Invert each nonzero eigenvalue. Inversion in ℝ sends zero to zero. -/
def inverse {G : Matrix ι ι ℂ} (h : G.IsHermitian) : Matrix ι ι ℂ :=
  h.eigenvectorUnitary.1 * diagonal (fun i => (((h.eigenvalues i)⁻¹ : ℝ) : ℂ)) *
    star (h.eigenvectorUnitary : Matrix ι ι ℂ)

theorem hermitian {G : Matrix ι ι ℂ} (h : G.IsHermitian) : (inverse h).IsHermitian := by
  apply isHermitian_mul_mul_conjTranspose
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)

private theorem triple {U : Matrix ι ι ℂ} (hu : star U * U = 1) (A B : Matrix ι ι ℂ) :
    (U*A*star U)*(U*B*star U)*(U*A*star U) = U*(A*B*A)*star U := by
  calc
    _ = U*(A*(star U*U)*B*(star U*U)*A)*star U := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [hu]

theorem sandwich {G : Matrix ι ι ℂ} (h : G.IsHermitian) :
    G * inverse h * G = G := by
  let U : Matrix ι ι ℂ := h.eigenvectorUnitary
  let A : Matrix ι ι ℂ := diagonal (fun i => (h.eigenvalues i : ℂ))
  let B : Matrix ι ι ℂ := diagonal (fun i => (((h.eigenvalues i)⁻¹ : ℝ) : ℂ))
  have e : G = U*A*star U := h.spectral_theorem
  have ab : A*B*A = A := by
    simp only [A,B,diagonal_mul_diagonal,Complex.ofReal_inv,mul_inv_cancel_right₀]
    funext i; simp
  change G*(U*B*star U)*G=G
  rw [e,triple (unitary.coe_star_mul_self _) A B,ab]

/-- This projector works simultaneously in the regular and singular sectors. -/
def projection (C : Matrix ι ν ℂ) : Matrix ν ν ℂ :=
  Cᴴ * inverse (isHermitian_mul_conjTranspose_self C) * C

/-- A Hermitian generalized inverse on the output suffices. This form
also applies when separate sectors choose their own eigenbases. -/
theorem sandwich_projection (C : Matrix ι ν ℂ) (D : Matrix ι ι ℂ) (hd : D.IsHermitian)
    (eqn : (C*Cᴴ)*D*(C*Cᴴ)=C*Cᴴ) :
    let P := Cᴴ*D*C
    P.IsHermitian ∧ P * P = P ∧ Set.range P.mulVec = Set.range Cᴴ.mulVec := by
  classical
  let G := C*Cᴴ
  let P := Cᴴ*D*C
  change P.IsHermitian ∧ P*P=P ∧ _ 
  change G*D*G=G at eqn
  have annih : (C*Cᴴ)*(D*G-1) = 0 := by
    change G*(D*G-1)=0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,eqn,sub_self]
  have st := (Matrix.self_mul_conjTranspose_mul_eq_zero C _).mp annih
  rw [Matrix.mul_sub,Matrix.mul_one,sub_eq_zero] at st
  have fix : P * Cᴴ = Cᴴ := by
    change Cᴴ * D * C * Cᴴ = _
    simpa only [G,Matrix.mul_assoc] using st
  refine ⟨isHermitian_conjTranspose_mul_mul C hd,?_,?_⟩
  · change P * (Cᴴ*D*C) = _
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,fix]
  · apply Set.Subset.antisymm
    · rintro _ ⟨v,rfl⟩
      exact ⟨(D*C).mulVec v,by simp [P,Matrix.mulVec_mulVec,Matrix.mul_assoc]⟩
    · rintro _ ⟨v,rfl⟩
      exact ⟨Cᴴ.mulVec v,by rw [Matrix.mulVec_mulVec,fix]⟩

theorem projection_spec (C : Matrix ι ν ℂ) :
    (projection C).IsHermitian ∧ projection C * projection C = projection C ∧
    Set.range (projection C).mulVec = Set.range Cᴴ.mulVec :=
  sandwich_projection C _ (hermitian _) (sandwich _)

end
end BlockPermanents.GramInverse
