import BlockPermanents.TransferBlocks
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-! # Full-cap contributions in the four-packet bend (Lemma 5C.2)

Rectangular complex matrices act from the common marked input to the
surviving two-packet output. `mixed` records both orders of a reflected gluing.
-/
namespace BlockPermanents.FourBend
open scoped Matrix
noncomputable section

variable {A Z : Type*} [Fintype Z]

/-- Sum of the two mixed gluings. -/
def cross (x y : Matrix Z A ℂ) := xᴴ*y + yᴴ*x

def square (x : Matrix Z A ℂ) := xᴴ*x

private lemma cross_sub (x y z : Matrix Z A ℂ) : cross (x-y) z = cross x z - cross y z := by
  simp only [cross, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
private lemma cross_add (x y z : Matrix Z A ℂ) : cross (x+y) z = cross x z + cross y z := by
  simp only [cross, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
private lemma cross_scale (a : ℚ) (x y : Matrix Z A ℂ) : cross (a • x) y = a • cross x y := by
  simp [cross, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_add]
private lemma cross_self (x : Matrix Z A ℂ) : cross x x = (2:ℚ) • square x := by
  simp only [cross, square, two_smul]
private lemma cross_switch (x y : Matrix Z A ℂ) : cross x y = cross y x := add_comm _ _

private lemma square_sub_scale (x y : Matrix Z A ℂ) (a : ℚ) :
    square (x-a • y) = square x - a • cross x y + (a*a) • square y := by
  simp only [square, cross, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  module

/-- The last term from the `J` block has three placements: two choices
of an ordinary packet and the fine clasp on the output. -/
def residual (P S : Matrix Z Z ℂ) (u w : Matrix Z A ℂ) :=
  w - (1/3:ℚ) • (w + S*w + P*u)

private lemma cross_adjoint (S : Matrix Z Z ℂ) (hS : Sᴴ = S) (w u : Matrix Z A ℂ) :
    cross (S*w) u = cross w (S*u) := by
  simp [cross, Matrix.conjTranspose_mul, hS, Matrix.mul_assoc]

private lemma cross_residual (P S : Matrix Z Z ℂ) (u w : Matrix Z A ℂ)
    (hP : Pᴴ=P) (hPP : P*P=P) (hS : Sᴴ=S) (hSu : S*u=u) :
    cross (residual P S u w) u = (1/3:ℚ) • cross w u - (2/3:ℚ) • square (P*u) := by
  have he : cross (P*u) u = (2:ℚ) • square (P*u) := by
    rw [← cross_self, cross_adjoint P hP u (P*u), ← Matrix.mul_assoc, hPP, cross_switch]
  unfold residual
  rw [cross_sub, cross_scale, cross_add, cross_add, cross_adjoint S hS, hSu, he]
  module

/-- Assemble the full-cap terms before square completion: the respective
sources are `X₄`, three transferred copies of `B`, and the marked correction. -/
def rawFull (P S : Matrix Z Z ℂ) (u w v : Matrix Z A ℂ) (a b : ℚ) :=
  ((a*b)*b) • square v - (18:ℚ) • square u +
    (3:ℚ) • (a^2 • square w - (2:ℚ) • square u - (a/2) • cross w u) -
    cross ((a*b) • v - (6:ℚ) • u - ((9*a)/2) • residual P S u w) u

/-- The full-cap identity as an equality of operators on the marked input,
using only projector/flip laws on the output and support of the two halves. -/
theorem full_cap_square (P S : Matrix Z Z ℂ) (u w v : Matrix Z A ℂ)
    (a b : ℚ) (hb : b ≠ 0) (hP : Pᴴ=P) (hPP : P*P=P) (hS : Sᴴ=S)
    (hSu : S*u=u) (hPv : P*v=v) :
    rawFull P S u w v a b =
      ((a*b)*b) • square (v-b⁻¹ • (P*u)) + (3*a^2) • square w -
      (12:ℚ) • square u - (4*a) • square (P*u) := by
  have hc : cross v (P*u) = cross v u := by rw [← cross_adjoint P hP, hPv]
  unfold rawFull
  rw [square_sub_scale, hc, cross_sub, cross_sub, cross_scale, cross_scale, cross_self,
    cross_scale, cross_residual P S u w hP hPP hS hSu]
  match_scalars <;> field_simp [hb] <;> ring

end
end BlockPermanents.FourBend
