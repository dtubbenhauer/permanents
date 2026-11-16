import BlockPermanents.TwoFullCaps
import BlockPermanents.ThreeGeneralOpen

/-! # The general two full caps on a projected marked boundary -/
namespace BlockPermanents.TwoFullCaps
open Bend ThreeTransfer ThreeGeneralOpen Matrix
open scoped Matrix BigOperators
noncomputable section

variable {I J T K : Type*} [Fintype T] [Fintype K] [DecidableEq T] [DecidableEq K]

/-- Retain the residual packets T and cap the last packet K into the
marked boundary via the marked input map N. -/
def full (P : Matrix (T×K) I ℂ) (N : Matrix K J ℂ) : Matrix T (I×J) ℂ :=
  fun t x => ∑ b,P (t,b) x.1 * star (N b x.2)

def crossing (P Q : Matrix (T×K) I ℂ) (N : Matrix K J ℂ) : Matrix (I×J) (I×J) ℂ :=
  (legs P N)ᴴ * ThreeTransfer.cross * legs Q N

theorem bend_crossing (P Q : Matrix (T×K) I ℂ) (N : Matrix K J ℂ) :
    partialTranspose (crossing P Q N) = (full P N)ᴴ*full Q N := by
  ext ⟨i,j⟩ ⟨i',j'⟩
  simp only [crossing,partialTranspose,legs,ThreeTransfer.cross,full,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,star_mul',star_sum,star_star,Finset.sum_mul,Finset.mul_sum]
  simp [mul_ite,Prod.ext_iff,ite_and]
  apply Finset.sum_congr rfl;intro s _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _;ring

private theorem full_old (n k : ℕ) (P F : Matrix (T×K) I ℂ) (N : Matrix K J ℂ) :
    full (fineFactor n k • P - (n.factorial:ℚ) • F) N =
      fineFactor n k • full P N - (n.factorial:ℚ) • full F N := by
  ext t ⟨i,j⟩
  simp only [full,Matrix.smul_apply,Matrix.sub_apply,sub_mul,smul_mul_assoc,Finset.sum_sub_distrib,
    ← Finset.smul_sum]

/-- The new defect X, stationary old defect B and moved old term C have a
common outer boundary. P and F send the old packets to the chosen residual
packets and the final packet, where the marked swap is made. -/
def boundaryCorrection (n k : ℕ) (X B C : Matrix (I×J) (I×J) ℂ)
    (P F : Matrix (T×K) I ℂ) (N : Matrix K J ℂ) :=
  let D := fineFactor n k • P - (n.factorial:ℚ) • F
  X - B + (n:ℚ) • C - (((n:ℚ)-1)/2) • (crossing D F N + crossing F D N)

theorem boundary_full_caps {n k : ℕ} (hn : 0<n) (X B C proper : Matrix (I×J) (I×J) ℂ)
    (P F : Matrix (T×K) I ℂ) (N : Matrix K J ℂ)
    (hz : partialTranspose X = partialTranspose B + proper +
      (fineFactor n k * ((n*k).choose k : ℚ)) • ((full P N)ᴴ * full P N) -
      ((n:ℚ)*n.factorial) • ((full F N)ᴴ * full F N)) :
    let a := fineFactor n k
    let v := full P N
    let u := full F N
    partialTranspose (boundaryCorrection n k X B C P F N) =
      (n:ℚ) • partialTranspose C + proper + (a^2/fineFactor (n-1) k) • (vᴴ*v) -
      (n.factorial:ℚ) • (uᴴ*u) - (((n:ℚ)-1)*a/2) • (vᴴ*u+uᴴ*v) := by
  dsimp only
  let D := fineFactor n k • P - (n.factorial:ℚ) • F
  change partialTranspose X - partialTranspose B + (n:ℚ) • partialTranspose C -
    (((n:ℚ)-1)/2) • (partialTranspose (crossing D F N) + partialTranspose (crossing F D N)) = _
  rw [bend_crossing,bend_crossing,hz,full_coefficient hn]
  dsimp only [D]
  simp only [full_old,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_trivial,Matrix.sub_mul,
    Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul]
  module

end
end BlockPermanents.TwoFullCaps
