import BlockPermanents.FourNativeUpright
import BlockPermanents.FourThickTransfer
/-! # Reading native four-packet operators after bending the fourth packet -/
namespace BlockPermanents.FourNative
open FourTarget FourRoutes FourExchangeKernel FourWireAlgebra FourAdjoints Bend ThreeTransfer
open ThreeGeneralOpen FourThickCompression FourNativeCap
open scoped Matrix BigOperators
noncomputable section
variable {I J : Type*} {d k : ℕ}

def read (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :
    Op d k →ₗ[ℚ] Matrix (I×J) (I×J) ℂ where
  toFun A := partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N)
  map_add' A B := by simp only [map_add,Matrix.mul_add,Matrix.add_mul]; rfl
  map_smul' a A := by simp only [map_smul,Matrix.smul_mul,Matrix.mul_smul]; rfl

theorem compressed_read (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    (fixed : matrix d k (W d k) * legs M N = legs M N) (A : Op d k) :
    read M N (sand (W d k) A) = read M N A := by
  have self : (matrix d k (W d k))ᴴ=matrix d k (W d k) :=
    reflected_matrix (average_self (D:=Fin d) (withinHom k))
  have left := congrArg Matrix.conjTranspose fixed
  rw [Matrix.conjTranspose_mul,self] at left
  change partialTranspose ((legs M N)ᴴ * matrix d k (W d k * A * W d k) * legs M N) = _
  simp only [map_mul,← Matrix.mul_assoc,left]
  simp only [Matrix.mul_assoc,fixed]
  change partialTranspose ((legs M N)ᴴ * (matrix d k A * legs M N)) = partialTranspose ((legs M N)ᴴ * matrix d k A * legs M N)
  rw [Matrix.mul_assoc]

theorem upright_legs {A B D K J : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (P : Matrix A B ℂ) (M : Matrix B D ℂ) (N : Matrix K J ℂ) :
    upright P * legs M N = legs (P*M) N := by
  ext ⟨a,b⟩ ⟨i,j⟩
  simp [upright,legs,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,Finset.sum_mul,mul_assoc]

theorem read_full (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ)
    {A B : Op d k} (ab : Reflected B A)
    {Z : Matrix (Triple d k) (Triple d k) ℂ} (hz : matrix d k B = upright Z) :
    read M N (A * packets d k TransferBlocks.swap14 * B) =
      (half (Z*M) N)ᴴ * half (Z*M) N := by
  have refl := reflected_matrix ab
  change partialTranspose ((legs M N)ᴴ * matrix d k (A * _ * B) * legs M N)=_
  rw [map_mul,map_mul,← refl,hz,packet_cross,← bend_full]
  apply congrArg _
  rw [← upright_legs Z M N,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end
end BlockPermanents.FourNative
