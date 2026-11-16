import BlockPermanents.ThreeTransfer
import Mathlib.Tactic.FieldSimp

/-! # The two full caps of the corrected bend at arbitrary packet count -/
namespace BlockPermanents.TwoFullCaps
open Bend ThreeTransfer Matrix
open scoped Matrix BigOperators
noncomputable section

variable {T K : Type*} [Fintype T] [Fintype K] [DecidableEq T] [DecidableEq K]

/-- The permanent normalization of the fine clasp on n packets. -/
def fineFactor (n k : ℕ) : ℚ := (n*k).factorial / (k.factorial:ℚ)^n

private theorem fineFactor_ne_zero (n k : ℕ) : fineFactor n k ≠ 0 := by
  unfold fineFactor;positivity

theorem fineFactor_step (m k : ℕ) :
    fineFactor (m+1) k = fineFactor m k * (((m+1)*k).choose k : ℚ) := by
  have hk : k ≤ (m+1)*k := by rw [Nat.add_mul,one_mul]; omega
  have h := Nat.choose_mul_factorial_mul_factorial hk
  rw [show (m+1)*k-k=m*k by rw [Nat.add_mul,one_mul];omega] at h
  have hc : ((((m+1)*k).choose k : ℚ) * k.factorial) * (m*k).factorial = ((m+1)*k).factorial := by exact_mod_cast h
  unfold fineFactor;rw [← hc,pow_succ]
  field_simp [Nat.factorial_ne_zero];ring

theorem full_coefficient {n k : ℕ} (hn : 0<n) :
    fineFactor n k * ((n*k).choose k : ℚ) = (fineFactor n k)^2 / fineFactor (n-1) k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Nat.succ_sub_one,eq_div_iff (fineFactor_ne_zero m k),fineFactor_step]; ring

abbrev A (T K : Type*) := T×K
abbrev Z (T K : Type*) := (T×K)×K

def old (n k : ℕ) (E f : Matrix (A T K) (A T K) ℂ) :=
  fineFactor n k • E - (n.factorial:ℚ) • f

/-- X is the new defect, and s is the packet interchange used to move the
old defect. The interface allows a spectator consisting of arbitrarily many packets. -/
def corrected (n k : ℕ) (X s : Matrix (Z T K) (Z T K) ℂ) (E f : Matrix (A T K) (A T K) ℂ) :=
  let F : Matrix (Z T K) (Z T K) ℂ := upright f
  let B : Matrix (Z T K) (Z T K) ℂ := upright (old n k E f)
  X - B + (n:ℚ) • (F*(s*B*s)*F) - (((n:ℚ)-1)/2) • (B*cross*F+F*cross*B)

private theorem bend_upright (M : Matrix (A T K) (A T K) ℂ) :
    partialTranspose (upright (K:=K) M) = upright M := by
  ext ⟨a,b⟩ ⟨i,j⟩; simp [partialTranspose,upright,eq_comm]

private theorem after_old (E f : Matrix (A T K) (A T K) ℂ) (n k : ℕ) :
    afterCap (old n k E f) = fineFactor n k • afterCap E - (n.factorial:ℚ) • afterCap f := rfl

/-- Bending the four signed summands of the actual corrected operator.
Both mixed gluings occur with their actual matrix adjoints. -/
theorem bend_corrected (n k : ℕ) (X s : Matrix (Z T K) (Z T K) ℂ)
    (E f : Matrix (A T K) (A T K) ℂ) (hE : Eᴴ=E) (hf : fᴴ=f) :
    let a := fineFactor n k
    let B := upright (K:=K) (old n k E f)
    let F := upright (K:=K) f
    let v := afterCap E
    let u := afterCap f
    partialTranspose (corrected n k X s E f) =
      partialTranspose X - B + (n:ℚ) • (F*partialTranspose (s*B*s)*F) -
        (((n:ℚ)-1)*a/2) • (vᴴ*u+uᴴ*v) +
        (((n:ℚ)-1)*n.factorial) • (uᴴ*u) := by
  dsimp only
  have ho : (old n k E f)ᴴ=old n k E f := by
    simp [old, Matrix.conjTranspose_smul,hE,hf]
  have raw : partialTranspose (corrected n k X s E f) =
      partialTranspose X - partialTranspose (upright (K:=K) (old n k E f)) +
      (n:ℚ) • partialTranspose (upright f*(s*upright (old n k E f)*s)*upright f) -
      (((n:ℚ)-1)/2) • (partialTranspose (upright (old n k E f)*cross*upright f)+
        partialTranspose (upright f*cross*upright (old n k E f))) := rfl
  rw [raw,bend_upright,bend_sandwich,bend_cross,bend_cross,ho,hf,after_old]
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,star_trivial,Matrix.sub_mul,
    Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul]
  change partialTranspose X - upright (old n k E f) + (n:ℚ) • (upright f*partialTranspose (s*upright (old n k E f)*s)*upright f) - _ = _
  module

/-- On inserting the zero-cap remainder, the two reflected packet terms
simplify to −n! and the full fine term has weight aₙ²/aₙ₋₁. -/
theorem two_full_caps {n k : ℕ} (hn : 0<n) (X s proper : Matrix (Z T K) (Z T K) ℂ)
    (E f : Matrix (A T K) (A T K) ℂ) (hE : Eᴴ=E) (hf : fᴴ=f)
    (hzero : partialTranspose X = upright (old n k E f) + proper +
      (fineFactor n k * ((n*k).choose k : ℚ)) • ((afterCap E)ᴴ*afterCap E) -
      ((n:ℚ)*n.factorial) • ((afterCap f)ᴴ*afterCap f)) :
    let a := fineFactor n k
    let B := upright (K:=K) (old n k E f)
    let F := upright (K:=K) f
    let v := afterCap E
    let u := afterCap f
    partialTranspose (corrected n k X s E f) = (n:ℚ) • (F * partialTranspose (s*B*s) * F) +
      proper + (a^2/fineFactor (n-1) k) • (vᴴ*v) - (n.factorial:ℚ) • (uᴴ*u) -
      (((n:ℚ)-1)*a/2) • (vᴴ*u+uᴴ*v) := by
  dsimp only
  rw [bend_corrected _ _ _ _ _ _ hE hf,hzero,full_coefficient hn]
  module

end
end BlockPermanents.TwoFullCaps
