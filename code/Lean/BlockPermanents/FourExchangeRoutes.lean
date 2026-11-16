import BlockPermanents.FourExchangeKernel

/-! Composing an ordinary merge on either foot of a native four-packet
exchange. Spectators and seam outputs retain the prefix ordering. -/
namespace BlockPermanents.FourExchangeKernel
open FourTarget FourRoutes Bend Equiv ThreeTransfer
open scoped Matrix BigOperators
noncomputable section

def slice {d k : ℕ} (n : ℕ) (hn : n≤3) (s : Word d ((3-n)*k)) :
    Matrix (Word d (n*k)) (Triple d k) ℂ :=
  fun w x => if idle n x = s ∧ w=active n hn x then 1 else 0

theorem half_as_route {d k : ℕ} (n : ℕ) (hn : n≤3) (r : CutIndex (n*k) k) (s : Word d ((3-n)*k)) :
    half n hn r s = wordCap d (n*k) k r * upright (slice n hn s) := by
  ext z ⟨x,h⟩
  by_cases e : idle n x=s <;> simp [Matrix.mul_apply,FourExchangeKernel.half,slice,upright,
    Fintype.sum_prod_type,e,mul_ite]

theorem upright_adjoint {I J K : Type*} [DecidableEq K] (P : Matrix I J ℂ) :
    (upright (K:=K) P)ᴴ = upright Pᴴ := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases h : a=b <;> simp [upright,Matrix.conjTranspose_apply,h,Ne.symm]

/-- The proper exchange with different upright matrices at its two feet.
For equal feet each summand is a reflected square. -/
theorem mixed_routes {d k n : ℕ} {A : Type*} (hn : n≤3) (r : CutIndex (n*k) k)
    (P Q : Matrix (Triple d k) A ℂ) :
    partialTranspose ((upright (K:=Word d k) P)ᴴ * matrix d k
      (FourThickSlots.block d k n * act d k (FourThickSlots.exchange k n hn r) *
        FourThickSlots.block d k n) * upright Q) =
      ∑ s, (half n hn r s * upright P)ᴴ * (half n hn r s * upright Q) := by
  rw [upright_adjoint,bend_sandwich]
  change upright Pᴴ * partialTranspose (matrix d k _) * upright Q = _
  rw [bent_exchange,Matrix.mul_sum,Matrix.sum_mul]
  simp only [Support.reflected,Matrix.conjTranspose_mul,upright_adjoint,Matrix.mul_assoc]

end
end BlockPermanents.FourExchangeKernel
