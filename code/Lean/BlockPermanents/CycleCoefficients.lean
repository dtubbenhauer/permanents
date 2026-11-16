import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum

/-! # Cycle-type coefficient calculation

This directly evaluates the partition sum from Appendix A. Parts include the
fixed points. The fixed points are distributed evenly among the nontrivial odd
cycles, with remainders assigned one at a time. -/
namespace BlockPermanents.CycleCoefficients

private def raiseHead : List ℕ → Option (List ℕ)
  | [] => none
  | a :: t => some ((a+1) :: t)

/-- Generating compositions by either prepending one or increasing the first
part. Each operation has a unique inverse on its image. -/
def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n+1 => ((compositions n).map (1 :: ·)) ++ ((compositions n).filterMap raiseHead)

theorem mem_compositions {n : ℕ} {l : List ℕ} (hpos : ∀ a ∈ l, 0 < a) (hsum : l.sum = n) :
    l ∈ compositions n := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => simp [compositions]
    | cons a t =>
      have h := hpos a (by simp)
      simp only [List.sum_cons] at hsum
      omega
  | succ n ih =>
    cases l with
    | nil => simp at hsum
    | cons a t =>
      have ha := hpos a (by simp)
      have ht : ∀ b ∈ t, 0 < b := fun b hb => hpos b (by simp [hb])
      simp only [List.sum_cons] at hsum
      rcases a with _ | (_ | a)
      · omega
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨t,ih ht (by omega),rfl⟩
      · apply List.mem_append_right
        apply List.mem_filterMap.mpr
        refine ⟨(a+1)::t,ih ?_ ?_,rfl⟩
        · simpa [ht] using (show 0 < a+1 ∧ (∀ x ∈ t, 0 < x) from ⟨by omega,ht⟩)
        · simp; omega

/-- Nondecreasing partitions of m. -/
def partitions (m : ℕ) := (compositions m).filter (fun l => decide (l.Pairwise (· ≤ ·)))

theorem mem_partitions {n : ℕ} {l : List ℕ} (hpos : ∀ a ∈ l, 0 < a)
    (hsum : l.sum = n) (hsort : l.Pairwise (· ≤ ·)) : l ∈ partitions n := by
  simpa [partitions, hsort] using mem_compositions hpos hsum

/-- Standard cardinality m! / ∏_d d^{m_d} m_d! of the conjugacy class. -/
def classSize (m : ℕ) (l : List ℕ) : ℕ :=
  m.factorial / (l.eraseDups.map (fun d => d^(l.count d) * (l.count d).factorial)).prod

/-- Closest half-integer to √(s+1), using the integer square root. -/
def halfParameter (s : ℕ) : ℚ := ((Nat.sqrt (16*(s+1)) + 1)/2 : ℕ) / (2 : ℚ)

private def cycleCoeff (c : ℕ → ℚ) (s j : ℕ) : ℚ :=
  let u := halfParameter s
  (u / (s+1) + u⁻¹)/2 * c j + (if j=0 then 0 else s/(2*u) * c (j-1))

/-- Contribution of a single partition, including the class multiplicity. -/
def contribution (m : ℕ) (l : List ℕ) (j : ℕ) : ℚ :=
  let a := (l.filter (fun d => decide (1 < d) && d%2 == 1)).length
  let f := l.count 1
  let r := (l.map (·/2)).sum
  let initial := fun (i : ℕ) => if i=r then (classSize m l : ℚ) else 0
  (List.range a).foldl (fun c i => cycleCoeff c (f/a + if i < f%a then 1 else 0)) initial j

def coefficient (m j : ℕ) : ℚ :=
  ((partitions m).map (fun l => contribution m l j)).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 7000000 in
theorem ten_coefficients : (List.range 6).map (coefficient 10) =
    [1,130,143339/15,555911/2,2126771,1349585] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 7000000 in
theorem six_coefficients : (List.range 4).map (coefficient 6) = [1,35,392,313] := by decide +kernel

end BlockPermanents.CycleCoefficients
