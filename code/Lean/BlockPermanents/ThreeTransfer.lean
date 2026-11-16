import BlockPermanents.Bend
import BlockPermanents.Support
import BlockPermanents.TransferBlocks
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.Module

/-! # Crossing and bending three packets
The marked packet is on the right. All entries are in complex orthonormal coordinates.
-/
namespace BlockPermanents.ThreeTransfer
noncomputable section
open scoped BigOperators Matrix
open Bend

variable {A B D K T : Type*}

/-- An upright operator with the marked wire untouched. -/
def upright [DecidableEq K] (F : Matrix A B ℂ) : Matrix (A × K) (B × K) ℂ :=
  fun i j => if i.2=j.2 then F i.1 j.1 else 0

/-- Interchange the last two packet cables, including on entangled inputs. -/
def cross [DecidableEq T] [DecidableEq K] : Matrix ((T × K) × K) ((T × K) × K) ℂ :=
  fun i j => if i=( (j.1.1,j.2),j.1.2) then 1 else 0

/-- Apply F to the upright packets, then contract its rightmost output with
the marked dual. The spectator T is the only output. -/
def afterCap (F : Matrix (T × K) A ℂ) : Matrix T (A × K) ℂ :=
  fun t x => F (t,x.2) x.1

/-- Moving upright factors across the bend, on either side. -/
theorem bend_sandwich [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
    (P : Matrix D A ℂ) (Y : Matrix (A × K) (B × K) ℂ) (Q : Matrix B D ℂ) :
    partialTranspose (upright P * Y * upright Q) =
      upright P * (show Matrix (A×K) (B×K) ℂ from fun x y => Y (x.1,y.2) (y.1,x.2)) * upright Q := by
  classical
  ext ⟨d,k⟩ ⟨e,l⟩
  simp [partialTranspose, Matrix.mul_apply, upright, Fintype.sum_prod_type, ite_mul, mul_ite]

/-- The mixed diagrams in (tr-general). Splitting a marked interchange
yields the two cap maps glued in the specified order, for arbitrary branching
and spectator dimensions. -/
theorem bend_cross [Fintype T] [Fintype K] [DecidableEq T] [DecidableEq K]
    (P : Matrix A (T × K) ℂ) (Q : Matrix (T × K) A ℂ) :
    partialTranspose (upright P * cross * upright Q) =
      (afterCap Pᴴ)ᴴ * afterCap Q := by
  classical
  ext ⟨i,k⟩ ⟨j,l⟩
  simp [partialTranspose, upright, cross, afterCap, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite, Prod.ext_iff, ite_and]

/-- Nesting an upright map under a cap composes the lower halves. -/
theorem afterCap_mul [Fintype B] [Fintype K] [DecidableEq K]
    (F : Matrix (T×K) B ℂ) (Q : Matrix B A ℂ) :
    afterCap (F * Q) = afterCap F * upright Q := by
  ext t x
  simp [afterCap, upright, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite]

/-- Subtracting the two mixed full-cap gluings gives exactly the corrected
square with the leftover coefficient −9/4. -/
theorem complete_full_square [Fintype T] (v u : Matrix T A ℂ) (a : ℚ) :
    (a^2 : ℚ) • (vᴴ*v) - (2:ℚ) • (uᴴ*u) -
      (a/2 : ℚ) • (vᴴ*u+uᴴ*v) =
      ((a • v - (1/2 : ℚ) • u)ᴴ * (a • v - (1/2 : ℚ) • u)) -
      (9/4 : ℚ) • (uᴴ*u) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
  module

end
end BlockPermanents.ThreeTransfer
