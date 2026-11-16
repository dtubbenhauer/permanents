import BlockPermanents.ThreeGeneralRaw
import BlockPermanents.PairBound
import BlockPermanents.TransferBlocks

/-! # The actual pair, merged and marked columns in the three-packet bend -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend ThreeTransfer TransferBlocks SchurNormalization
open scoped Matrix BigOperators
noncomputable section

abbrev ThreeWords (d k : ℕ) := (K d k × K d k) × K d k

/-- A spectator and a live word passed through the two-order packet average. -/
def M (d k : ℕ) (s : K d k) : Matrix (K d k) (K d k × K d k) ℂ :=
  fun w i => (symClasp d k s i.1 * symClasp d k w i.2 + symClasp d k s i.2 * symClasp d k w i.1)/2

/-- The first two ordinary packets merged under the fine clasp. -/
def P (d k : ℕ) : Matrix (K d (k+k)) (K d k × K d k) ℂ := fun w i =>
  symClasp d (k+k) w (Fin.append i.1 i.2)

theorem column_symmetric (d k : ℕ) (i : K d k) : Symmetric (fun w => symClasp d k w i) := by
  let e : K d k → ℂ := Pi.single i (1:ℂ)
  have h : (symClasp d k).mulVec e = fun w => symClasp d k w i := by
    funext w; simp [Matrix.mulVec,dotProduct,e,Pi.single_apply, mul_ite]
  rw [← h]; exact PairBound.projected_symmetric _ _ _

theorem pair_symmetric (d k : ℕ) (s : K d k) (i : K d k × K d k) :
    Symmetric (fun w => M d k s w i) := by
  let v (j : K d k) : K d k → ℂ := fun w => symClasp d k w j
  have h (j : K d k) : (symClasp d k).mulVec (v j) = v j := column_symmetric _ _ _
  have he : (fun w => M d k s w i) =
      (2:ℂ)⁻¹ • (symClasp d k s i.1 • v i.2 + symClasp d k s i.2 • v i.1) := by
    funext w; simp [M,v,div_eq_mul_inv,mul_comm]
  unfold Bend.Symmetric; rw [he]; simp only [Matrix.mulVec_smul,Matrix.mulVec_add,h]

theorem canonical_raw (d k : ℕ) (hk : 0<k) (hsmall : HomogeneousSchur d k k)
    (hbig : HomogeneousSchur d (k+k) k) :
    let a : ℂ := (k+k).choose k
    let u := terminal (stack (M d k)) (symClasp d k)
    let v := terminal (stackedFine (P d k)) (symClasp d k)
    partialTranspose (corrected (M d k) (P d k) (symClasp d k)) =
      (2:ℂ) • properSquares le_rfl (M d k) (symClasp d k) +
      a • properSquares (by omega) (fun _ : Unit => P d k) (symClasp d k) +
      Support.reflected (a • v - (1/2:ℂ) • u) - (9/4:ℂ) • Support.reflected u :=
  general_raw hk hsmall hbig _ _ _ (pair_symmetric d k)
    (fun i => column_symmetric d (k+k) (Fin.append i.1 i.2)) (column_symmetric d k)

/-- The three packet projectors as a single boundary map. -/
def internal (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ :=
  legs (legs (symClasp d k) (symClasp d k)) (symClasp d k)

def swapFront (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ :=
  fun u v => if ((u.1.swap,u.2) : ThreeWords d k) = v then 1 else 0

theorem front_mul {I : Type*} {d k : ℕ} (A : Matrix (ThreeWords d k) I ℂ) (x : ThreeWords d k) (j : I) :
    (swapFront d k * A) x j = A (x.1.swap,x.2) j := by
  simp [Matrix.mul_apply,swapFront,ite_mul]

theorem front_sq (d k : ℕ) : swapFront d k * swapFront d k = 1 := by
  ext x y; simp [front_mul,swapFront,Matrix.one_apply]

theorem front_star (d k : ℕ) : (swapFront d k)ᴴ = swapFront d k := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨x,y⟩,z⟩
  simp [Matrix.conjTranspose_apply,swapFront,Prod.ext_iff,eq_comm, and_comm, and_left_comm]

theorem pair_star (d k : ℕ) : (pair (swapFront d k))ᴴ = pair (swapFront d k) := by
  simp [pair,front_star]

theorem legs_pair (d k : ℕ) :
    legs (stack (M d k)) (symClasp d k) = pair (swapFront d k)*internal d k := by
  rw [pair,smul_mul_assoc,add_mul,one_mul]
  ext ⟨⟨s,w⟩,b⟩ ⟨⟨i,j⟩,a⟩
  simp [M,legs,stack,internal,Matrix.smul_apply,Rat.smul_def,front_mul]
  ring

theorem straight_stack {d k : ℕ} {I J : Type*} (C : K d k → Matrix (K d k) I ℂ) (N : Matrix (K d k) J ℂ) :
    straight C N = (legs (stack C) N)ᴴ * legs (stack C) N := by
  ext i j
  simp only [straight,Support.reflected,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    legs,stack,Fintype.sum_prod_type]

/-- The six concrete whole-packet orderings on the compressed boundary.
The two straight terms and four reflected crossings are exactly the
unnormalized three-packet clasp. -/
theorem coarse_six (d k : ℕ) :
    coarse (M d k) (symClasp d k) =
      (internal d k)ᴴ * ((6:ℚ) • triple (swapFront d k) ThreeTransfer.cross) * internal d k := by
  let u := swapFront d k
  let f := pair u
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  let D := internal d k
  have eqn : (2:ℚ) • f + (4:ℚ) • (f*t*f) = (6:ℚ) • triple u t := by
    rw [show f*t*f=triple u t-(1/2:ℚ) • (f-triple u t) from sandwiched_crossing u t]
    module
  have two (X : Matrix (ThreeWords d k) (ThreeWords d k) ℂ) : (2:ℂ) • X = (2:ℚ) • X := by
    ext a b; simp [Matrix.smul_apply,Rat.smul_def]
  have four (X : Matrix (ThreeWords d k) (ThreeWords d k) ℂ) : (4:ℂ) • X = (4:ℚ) • X := by
    ext a b; simp [Matrix.smul_apply,Rat.smul_def]
  rw [coarse,straight_stack,mixed,legs_pair,Matrix.conjTranspose_mul,pair_star,two,four,← eqn]
  change (2:ℚ) • (Dᴴ*f*(f*D)) + (4:ℚ) • (Dᴴ*f*t*(f*D)) =
    Dᴴ*((2:ℚ) • f+(4:ℚ) • (f*t*f))*D
  have ff : f*f=f := pair_idem _ (front_sq d k)
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc f f D,ff]

end
end BlockPermanents.ThreeGeneralOpen
