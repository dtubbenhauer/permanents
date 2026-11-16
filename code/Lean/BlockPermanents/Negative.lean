import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The negative marked closure for five quadratic packets

We compute the transfers from the recurrence for `A_j` and the four terms
defining `Y_m` in “Iterating the transfer”. The mixed contractions have
different bra and ket packets. The calculation is independent of the
whole-edge inclusion–exclusion certificate in the appendix.

All packet coordinates and all mixed contractions in the computation are exact rationals.
Packet coordinates are in the basis (e₀², e₀ ⊙ e₁, e₁²).
-/
namespace BlockPermanents.Negative

structure Quad where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

/-- The inner product, since the middle occupation has squared norm 1/2. -/
def gram (p q : Quad) : ℚ :=
  p.a * q.a + p.b * q.b / 2 + p.c * q.c

def addCoeffs : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: addCoeffs p q

/-- Multiply by a + bz + cz². Trailing zeros need not be removed. -/
def timesQuad (q : Quad) (p : List ℚ) : List ℚ :=
  if q.b = 0 ∧ q.c = 0 then p.map (q.a * ·)
  else addCoeffs (p.map (q.a * ·)) (0 :: addCoeffs (p.map (q.b * ·)) (0 :: p.map (q.c * ·)))

def productCoeffs (xs : List Quad) : List ℚ := xs.foldr timesQuad [1]

/-- The mixed fine closure on two lists of n quadratic packets. The j-th
occupation has squared norm 1/binom(2n,j), and the fine prefactor is (2n)!/2ⁿ. -/
def fine (xs ys : List Quad) : ℚ :=
  let degree := 2 * xs.length
  let x := productCoeffs xs
  let y := productCoeffs ys
  ((List.range (degree+1)).map fun j =>
    x[j]?.getD 0 * y[j]?.getD 0 * (Nat.factorial j : ℚ)
      * (Nat.factorial (degree-j) : ℚ)).sum / 2^xs.length

/-- Pick each position once and keep the other entries in their original order.
Equal-valued packets in different positions contribute with multiplicity. -/
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: xs => (a, xs) :: ((picks xs).map fun ⟨b, rest⟩ => (b, a :: rest))

/-- The permanent of the packet Gram matrix, i.e. the
mixed coarse closure when both inputs have length n. -/
def coarse : List Quad → List Quad → ℚ
  | [], ys => if ys.isEmpty then 1 else 0
  | p :: xs, ys => ((picks ys).map fun ⟨q, rest⟩ => gram p q * coarse xs rest).sum

def defect (xs ys : List Quad) : ℚ := fine xs ys - coarse xs ys

/-- Choose the spectator on the bra and ket boundaries independently. -/
private def bothExits (K : List Quad → List Quad → ℚ) (xs ys : List Quad) : ℚ :=
  ((picks xs).map fun ⟨p, left⟩ =>
    ((picks ys).map fun ⟨q, right⟩ => gram p q * K left right).sum).sum

/-- The mixed closure of A_j on two lists of length j. Each spectator
pair in the two packet averages of L_j has weight 1/j². -/
def transfer : Nat → List Quad → List Quad → ℚ
  | 0, _, _ => 0
  | 1, _, _ => 0
  | j+2, xs, ys => defect xs ys + bothExits (transfer (j+1)) xs ys / (j + 1 : ℚ)

/-- The transfer Y₅ on the four ordinary packets `xs` and a marked packet
`t`. In fA'f both ordinary exits are chosen independently. In each crossed
term exactly one exit is ordinary. We retain both crossed terms. -/
def markedValue (xs : List Quad) (t : Quad) : ℚ :=
  let K := transfer 4
  let stationary := gram t t * K xs xs
  let moved := ((picks xs).map fun ⟨p, left⟩ =>
    ((picks xs).map fun ⟨q, right⟩ => gram p q * K (t :: left) (t :: right)).sum).sum
  let crossedBra := ((picks xs).map fun ⟨p, left⟩ =>
    gram p t * K (t :: left) xs).sum
  let crossedKet := ((picks xs).map fun ⟨q, right⟩ =>
    gram t q * K xs (t :: right)).sum
  defect (t :: xs) (t :: xs) - stationary +
    4 * (moved / 16) - (3 / 2) * (crossedBra / 4 + crossedKet / 4)

def unitPacket : Quad := ⟨1, 0, 0⟩
def fourthPacket : Quad := ⟨1, 1/5, 7/400⟩
def fifthPacket : Quad := ⟨1, -60, 1200⟩

def witness : List Quad := [unitPacket, unitPacket, unitPacket, fourthPacket, fifthPacket]
def markAtUnit : ℚ := markedValue [unitPacket, unitPacket, fourthPacket, fifthPacket] unitPacket
def markAtFour : ℚ := markedValue [unitPacket, unitPacket, unitPacket, fifthPacket] fourthPacket
def markAtFive : ℚ := markedValue [unitPacket, unitPacket, unitPacket, fourthPacket] fifthPacket

/-- Coefficients of (1+uz)(1+vz) in the symmetric occupation basis. -/
def linearProduct (u v : ℂ) : ℂ × ℂ × ℂ := (1, u+v, u*v)
noncomputable def coords (p : Quad) : ℂ × ℂ × ℂ :=
  ((p.a : ℂ), (p.b : ℂ), (p.c : ℂ))

private theorem conjugateFactors (a b : ℝ) :
    linearProduct ⟨a, b⟩ ⟨a, -b⟩ = (1, ((2*a : ℝ) : ℂ), ((a^2 + b^2 : ℝ) : ℂ)) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> apply Complex.ext <;>
    simp [linearProduct, sq, Complex.mul_re, Complex.mul_im] <;> ring

theorem unit_factors : coords unitPacket = linearProduct 0 0 := by
  norm_num [coords, unitPacket, linearProduct]

theorem fourth_factors :
    coords fourthPacket =
    linearProduct ⟨2/20, Real.sqrt 3 / 20⟩ ⟨2/20, -(Real.sqrt 3 / 20)⟩ := by
  rw [conjugateFactors]
  simp only [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [coords, fourthPacket]

theorem fifth_factors :
    coords fifthPacket =
    linearProduct ⟨-30, 10 * Real.sqrt 3⟩ ⟨-30, -(10 * Real.sqrt 3)⟩ := by
  rw [conjugateFactors, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [coords, fifthPacket]

/-- Each of the five rational quadratics is a product of two complex linear forms. -/
theorem witness_factors (p : Quad) (hp : p ∈ witness) :
    ∃ u v : ℂ, coords p = linearProduct u v := by
  simp [witness] at hp
  rcases hp with h | h | h
  · exact h ▸ ⟨_, _, unit_factors⟩
  · exact h ▸ ⟨_, _, fourth_factors⟩
  · exact h ▸ ⟨_, _, fifth_factors⟩

section Certificate
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem fifth_value : markAtFive = -565839/2000 := by decide +kernel
theorem fourth_value : markAtFour = 18083516817/4 := by decide +kernel
theorem first_value : markAtUnit = 9041984725911/2000 := by decide +kernel

theorem all_marked_values :
    (picks witness).map (fun ⟨p, xs⟩ => markedValue xs p) =
      [9041984725911/2000, 9041984725911/2000, 9041984725911/2000,
       18083516817/4, -565839/2000] := by
  change [markAtUnit, markAtUnit, markAtUnit, markAtFour, markAtFive] = _
  rw [first_value, fourth_value, fifth_value]

theorem negative_marked_closure : markAtFive < 0 := by rw [fifth_value]; norm_num

theorem fine_value : fine witness witness = 14606209031337/4000 := by decide +kernel
theorem coarse_value : coarse witness witness = 695621115897/20000 := by decide +kernel

theorem mean_is_defect :
    ((picks witness).map (fun ⟨p, xs⟩ => markedValue xs p)).sum / 5 =
    defect witness witness := by
  rw [all_marked_values, defect, fine_value, coarse_value]
  norm_num

theorem mean_value : defect witness witness = 18083856010197/5000 := by
  rw [defect, fine_value, coarse_value]
  norm_num

end Certificate
end BlockPermanents.Negative
