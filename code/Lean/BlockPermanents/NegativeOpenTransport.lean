import BlockPermanents.NegativeOpenBend
import BlockPermanents.TensorCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Remark 3A.5 for any two orthogonal complex unit vectors -/
namespace BlockPermanents.NegativeOpenTransport
open NegativeOpenBend Closures TensorCoordinates
open scoped Matrix
noncomputable section

/-- In the two slots of the family x, the ordinary boundary vector is the
product of the two k-fold tensor powers. -/
def purePowers {k d : ℕ} (x : Fin 2 → Fin d → ℂ) : State d k :=
  pureWord (fun t : Slots k => x t.1)

def direction {k d : ℕ} (x : Fin 2 → Fin d → ℂ) : State d k :=
  packetClasp (purePowers x) - clasp (purePowers x)

private def matrix {k d : ℕ} (x : Fin 2 → Fin d → ℂ) :=
  power (Slots k) (Matrix.of fun j i => x i j)

private theorem isometry {k d : ℕ} (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    (matrix (k:=k) x)ᴴ * matrix (k:=k) x = 1 := by
  have h : (Matrix.of (fun j i => x i j))ᴴ * Matrix.of (fun j i => x i j) = 1 := hx
  rw [matrix,← power_star,← power_mul,h,power_one]

private theorem pure_image {k d : ℕ} (x : Fin 2 → Fin d → ℂ) :
    (matrix (k:=k) x).mulVec (input (Function.Embedding.refl _)) = purePowers x := by
  funext u
  simp [Matrix.mulVec,dotProduct,input,mul_ite,matrix,power,purePowers,pureWord]

private theorem fine_sum {k d : ℕ} (v : State d k) :
    clasp v = ((Fintype.card (Slots k)).factorial:ℂ)⁻¹ •
          ∑ p : Equiv.Perm (Slots k), Transfer.tensorAction (Slots k) (Fin d) p.symm v := by
  funext w
  simp [clasp,sumSlots,Transfer.tensorAction,Finset.sum_apply]

private theorem packet_sum {k d : ℕ} (v : State d k) :
    packetClasp v = (2:ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin 2),
          Transfer.tensorAction (Slots k) (Fin d) (p.symm.prodCongr (Equiv.refl (Fin k))) v := by
  funext w
  simp only [packetClasp,clasp,sumSlots,Fintype.card_fin,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  congr 1

private theorem fine_natural {k d : ℕ} (x : Fin 2 → Fin d → ℂ) (v : State 2 k) :
    clasp ((matrix x).mulVec v) = (matrix x).mulVec (clasp v) := by
  rw [fine_sum,fine_sum]
  simp only [← Matrix.mulVecLin_apply,map_smul,map_sum]
  simp only [matrix,Matrix.mulVecLin_apply,naturality]

private theorem packet_natural {k d : ℕ} (x : Fin 2 → Fin d → ℂ) (v : State 2 k) :
    packetClasp ((matrix x).mulVec v) = (matrix x).mulVec (packetClasp v) := by
  rw [packet_sum,packet_sum]
  simp only [← Matrix.mulVecLin_apply,map_smul,map_sum]
  simp only [matrix,Matrix.mulVecLin_apply,naturality]

private theorem direction_image {k d : ℕ} (x : Fin 2 → Fin d → ℂ) :
    direction (k:=k) x = (matrix x).mulVec (witness (Function.Embedding.refl _)) := by
  rw [direction, ← pure_image, packet_natural, fine_natural, witness, Matrix.mulVec_sub]

/-- The two-packet defect takes eigenvalue −2 on this vector. -/
theorem eigenvector {k d : ℕ} (x : Fin 2 → Fin d → ℂ) :
    defect (direction (k:=k) x) = (-2:ℂ) • direction x := by
  let w := witness (k:=k) (Function.Embedding.refl (Fin 2))
  have hf : clasp w = 0 := NegativeOpenBend.fine_zero _
  have hr : packetClasp w = w := by
    funext u
    have he := congrFun (NegativeOpenBend.eigenvector (k:=k) (Function.Embedding.refl _)) u
    change fineWeight _ _ * clasp w u - _ * packetClasp w u = (-2:ℂ)*w u at he
    rw [hf] at he
    norm_num at he
    exact he
  rw [direction_image]
  change defect ((matrix x).mulVec w) = _
  funext u
  simp only [defect, fine_natural,packet_natural,hf,hr,Matrix.mulVec_zero,Pi.zero_apply,
    mul_zero,Fintype.card_fin,Pi.smul_apply,smul_eq_mul]
  norm_num [w]

/-- Independent permutations within either ordinary packet fix the vector. -/
theorem internal_symmetric {k d : ℕ} (x : Fin 2 → Fin d → ℂ) (p : Fin 2 → Equiv.Perm (Fin k))
    (u : Slots k → Fin d) : direction x (u ∘ withinPackets p) = direction x u := by
  let w := witness (k:=k) (Function.Embedding.refl (Fin 2))
  have hv : Transfer.tensorAction (Slots k) _ (withinPackets p) w = w :=
    funext (NegativeOpenBend.internal_symmetric _ p)
  rw [direction_image]
  exact congrFun ((naturality _ _ _ w).trans (congrArg (matrix x).mulVec hv)) u

/-- The squared norm is unchanged by embedding the pair in any finite dimension. -/
theorem norm_sq {k d : ℕ} (hk : 0 < k) (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    bracket (direction (k:=k) x) (direction x) = 1/2 - 1/((2*k).choose k:ℂ) := by
  rw [direction_image]
  let w := witness (k:=k) (Function.Embedding.refl (Fin 2))
  change dotProduct (star ((matrix x).mulVec w)) ((matrix x).mulVec w) = _
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,isometry x hx,Matrix.one_mulVec]
  exact NegativeOpenBend.norm_sq hk _

theorem nonzero {k d : ℕ} (hk : 2 ≤ k) (x : Fin 2 → Fin d → ℂ) (hx : crossGram x x = 1) :
    direction (k:=k) x ≠ 0 := by
  rw [direction_image]
  intro h
  have hh := congrArg (matrix (k:=k) x)ᴴ.mulVec h
  rw [Matrix.mulVec_mulVec,isometry x hx,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
  exact NegativeOpenBend.nonzero hk _ hh

/-- Every fine cut of the next marked opening vanishes, for arbitrary marked packet l. -/
theorem fine_cuts {k d : ℕ} (x : Fin 2 → Fin d → ℂ) (l : Bend.Word d k → ℂ)
    (r : Bend.CutIndex (2*k) k) :
    (Bend.wordCap d (2*k) k r).mulVec
      (Bend.product (clasp (fun u : Bend.Word d (2*k) => direction x (u ∘ finProdFinEquiv))) l) = 0 := by
  have hf : clasp (fun u : Bend.Word d (2*k) => direction x (u ∘ finProdFinEquiv)) = 0 := by
    funext w
    rw [Bridges.clasp_transport,direction_image,fine_natural,NegativeOpenBend.fine_zero,Matrix.mulVec_zero]
    rfl
  rw [hf]
  have hp : Bend.product (0 : Bend.Word d (2*k) → ℂ) l = 0 := by funext w; simp [Bend.product]
  rw [hp,Matrix.mulVec_zero]

/-- The explicit eigenvector and its nonzero squared norm for the two unit
vectors named in the remark. -/
theorem orthogonal_unit_pair {d k : ℕ} (hk : 2 ≤ k) (u v : Fin d → ℂ)
    (hu : Bend.energy u = 1) (hv : Bend.energy v = 1) (huv : bracket u v = 0) :
    let w := direction (k:=k) ![u,v]
    w ≠ 0 ∧ defect w = (-2:ℂ) • w ∧ bracket w w = 1/2 - 1/((2*k).choose k:ℂ) := by
  have hvu : bracket v u = 0 := by
    have h := congrArg star huv
    simpa [bracket,star_sum,star_mul',mul_comm] using h
  have hg : crossGram ![u,v] ![u,v] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [crossGram,Coarse.bracket_self,hu,hv,huv,hvu,Matrix.one_apply]
  exact ⟨nonzero hk _ hg, eigenvector _, norm_sq (by omega) _ hg⟩

end
end BlockPermanents.NegativeOpenTransport
