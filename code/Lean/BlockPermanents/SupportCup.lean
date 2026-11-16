import BlockPermanents.PairBound
import BlockPermanents.Support

/-! The trace cup on a subspace of the positive output of a square cut. An
orthonormal basis of that subspace gives word coordinates for the dashed seam. -/
namespace BlockPermanents.SupportCup
open Bend Support
open scoped BigOperators Matrix
noncomputable section

variable {I : Type*} [Fintype I]
def euclid := (WithLp.linearEquiv 2 ℂ (I→ℂ)).symm
def plane (W : Submodule ℂ (I→ℂ)) := W.map euclid.toLinearMap
abbrev Rank (W : Submodule ℂ (I→ℂ)) := Module.finrank ℂ (plane W)
abbrev Seam (W : Submodule ℂ (I→ℂ)) := Fin (Rank W) × I
theorem rank_eq (W : Submodule ℂ (I→ℂ)) : Rank W=Module.finrank ℂ W :=
  euclid.finrank_map_eq W

def basisColumn (W : Submodule ℂ (I→ℂ)) (t : Fin (Rank W)) (i : I) : ℂ :=
  ((stdOrthonormalBasis ℂ (plane W) t).val) i
def cap (W : Submodule ℂ (I→ℂ)) : Matrix Unit (Seam W) ℂ :=
  fun _ z => basisColumn W z.1 z.2
/-- Coordinates of a matrix on the positive supported cable and the full dual. -/
def coords (W : Submodule ℂ (I→ℂ)) (A : Matrix I I ℂ) : Seam W → ℂ :=
  fun z => ∑ i, star (basisColumn W z.1 i) * A i z.2

def J [DecidableEq I] (W : Submodule ℂ (I→ℂ)) : Matrix (Seam W) (Seam W) ℂ :=
  1 - (Rank W:ℂ)⁻¹ • ((cap W)ᴴ * cap W)

private theorem norm_basis (W : Submodule ℂ (I→ℂ)) (t : Fin (Rank W)) :
    ∑ i, Complex.normSq (basisColumn W t i) = 1 := by
  let b := stdOrthonormalBasis ℂ (plane W)
  simp only [Complex.normSq_eq_norm_sq,basisColumn]
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : I => ℂ) (b t).val]
  change ‖b t‖ ^ 2=1
  rw [b.orthonormal.norm_eq_one t,one_pow]

theorem bubble (W : Submodule ℂ (I→ℂ)) : cap W * (cap W)ᴴ = (Rank W : ℂ) • 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,cap,Fintype.sum_prod_type]
  have hb (t : Fin (Rank W)) : (∑ i, basisColumn W t i * star (basisColumn W t i))=(1:ℂ) := by
    simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.ofReal_one, mul_comm]
      using congrArg Complex.ofReal (norm_basis W t)
  rw [Finset.sum_congr rfl (fun t _ => hb t)]
  simp [Subsingleton.elim a b]

private def col (W : Submodule ℂ (I→ℂ)) (A : Matrix I I ℂ) (j : I)
    (h : (fun i => A i j)∈W) : plane W := ⟨euclid (fun i=>A i j),⟨_,h,rfl⟩⟩

private theorem coord_repr (W : Submodule ℂ (I→ℂ)) (A : Matrix I I ℂ) (j : I)
    (h : (fun i => A i j)∈W) (t : Fin (Rank W)) :
    coords W A (t,j)=(stdOrthonormalBasis ℂ (plane W)).repr (col W A j h) t := by
  rw [OrthonormalBasis.repr_apply_apply,Submodule.coe_inner]
  simp only [coords,PiLp.inner_apply,RCLike.inner_apply',basisColumn,col,euclid]
  rfl

theorem close (W : Submodule ℂ (I→ℂ)) (A : Matrix I I ℂ) (hc : ∀ j, (fun i => A i j) ∈ W) :
    (cap W).mulVec (coords W A) () = A.trace := by
  let b := stdOrthonormalBasis ℂ (plane W)
  have hex (i j : I) : ∑ t, coords W A (t,j)*basisColumn W t i=A i j := by
    let ev := (EuclideanSpace.projₗ i).comp (plane W).subtype
    have he := congrArg ev (b.sum_repr (col W A j (hc j)))
    simpa only [coord_repr W A j (hc j),map_sum,map_smul,smul_eq_mul] using he
  simp only [Matrix.mulVec,dotProduct,cap,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simpa only [mul_comm] using hex j j

theorem coord_energy (W : Submodule ℂ (I→ℂ)) (A : Matrix I I ℂ) (hc : ∀ j, (fun i=>A i j)∈W) :
    energy (coords W A) = ∑ i,∑ j,Complex.normSq (A i j) := by
  let b := stdOrthonormalBasis ℂ (plane W)
  have hn (j) : ∑ t, Complex.normSq (coords W A (t,j)) = ∑ i,Complex.normSq (A i j) := by
    simp only [coord_repr W A j (hc j),Complex.normSq_eq_norm_sq]
    rw [← PiLp.norm_sq_eq_of_L2 (fun _=>ℂ) (b.repr (col W A j (hc j))),
      b.repr.norm_map, Submodule.coe_norm, PiLp.norm_sq_eq_of_L2]
    rfl
  simp only [energy,Fintype.sum_prod_type]
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun i j=>Complex.normSq (A i j))]
  exact Finset.sum_congr rfl fun j _ => hn j

private theorem singleton_gram {Z : Type*} [Fintype Z] (u : Z→ℂ) :
    reflected (Matrix.of (fun z (_ : Unit) => u z)) () () = (energy u:ℂ) := by
  simp [reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,energy,Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self]

/-- Subtracting the component along the trace cup is the actual residual
projection. Reclosing the other branch recovers the ordinary matrix trace. -/
theorem resolution [DecidableEq I] (W : Submodule ℂ (I→ℂ)) (hW : 0<Rank W) (A : Matrix I I ℂ)
    (hc : ∀ j, (fun i=>A i j)∈W) :
    (∑ i,∑ j,Complex.normSq (A i j)) =
      energy ((J W).mulVec (coords W A)) + Complex.normSq A.trace / Rank W := by
  let Y : Matrix (Seam W) Unit ℂ := Matrix.of (fun z _ => coords W A z)
  have h := congrArg (fun M : Matrix Unit Unit ℂ => M () ())
    (resolve_last_cap (cap W) Y (Rank W) hW (bubble W))
  change reflected Y () ()= reflected (J W * Y) () () + (Rank W:ℂ)⁻¹ * reflected (cap W*Y) () () at h
  have jgram := singleton_gram ((J W).mulVec (coords W A))
  have cgram := singleton_gram ((cap W).mulVec (coords W A))
  change reflected (J W * Y) () () = _ at jgram
  change reflected (cap W * Y) () () = _ at cgram
  rw [jgram,cgram] at h
  change (reflected (Matrix.of (fun z (_:Unit)=>coords W A z))) () () = _ at h
  rw [singleton_gram,coord_energy W A hc] at h
  have he : energy ((cap W).mulVec (coords W A)) = Complex.normSq A.trace := by
    simp [energy,close W A hc]
  rw [he] at h
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_re, div_eq_mul_inv, mul_comm] using congrArg Complex.re h

end
end BlockPermanents.SupportCup
