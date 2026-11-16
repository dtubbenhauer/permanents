import BlockPermanents.Closures
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Fin

/-! # Six labeled thin wires for three quadratic packets

Products of wire maps use ordinary function composition. A closed wire map
is evaluated on word coordinates before any quotient by packet symmetry.
-/
namespace BlockPermanents.ThreeWire
open scoped BigOperators
open Closures
abbrev Wire := Fin 6 → Fin 6
abbrev Words (D : Type*) := Fin 6 → D

def identity : Wire := id
def packetSwap : Wire := ![2,3,0,1,4,5]
def thinSwap : Wire := ![0,1,2,5,4,3]
def fullSwap : Wire := ![0,1,4,5,2,3]

/-- The packet-average on the two upright packets uses these two wirings. -/
def pairList : List Wire := [identity,packetSwap]

def boundary {D : Type*} (F G H : (Fin 2 → D) → ℂ) : Words D → ℂ :=
  fun w => F ![w 0,w 1] * G ![w 2,w 3] * H ![w 4,w 5]

def evaluateWord {D : Type*} [Fintype D] (z : Words D → ℂ) (p : Wire) : ℂ :=
  bracket z (fun w => z (w ∘ p))

/-- Bilinearly glue the two lists of upright operators across a fixed
interchange. The two lists in the applications are inverse-invariant. -/
def glue (f : Wire → ℂ) (l : List Wire) (t : Wire) (r : List Wire) : ℂ :=
  (l.map fun a => (r.map fun b => f (a ∘ t ∘ b)).sum).sum

/-- Enumerate all permutations by the image of the first slot, then the
orders of the remaining slots. -/
def permutations : (n : ℕ) → List (Equiv.Perm (Fin n))
  | 0 => [1]
  | n+1 => (List.finRange (n+1)).flatMap fun i =>
      (permutations n).map fun p => Equiv.Perm.decomposeFin.symm (i,p)

private theorem sum_flatMap {I J M : Type*} [AddCommMonoid M]
    (l : List I) (g : I → List J) (f : J → M) :
    ((l.flatMap g).map f).sum = (l.map fun i => ((g i).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_permutations {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Equiv.Perm (Fin n) → M) : ((permutations n).map f).sum = ∑ p, f p := by
  induction n with
  | zero => simp [permutations]
  | succ n ih =>
    simp only [permutations, sum_flatMap, List.map_map, Function.comp_def]
    simp_rw [ih]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp f, Fintype.sum_prod_type]

/-- Wire maps may be applied repeatedly. Storing the six images once keeps
the small finite certificate independent of how a permutation was produced. -/
def tabulate (p : Wire) : Wire := ![p 0,p 1,p 2,p 3,p 4,p 5]

theorem tabulate_eq (p : Wire) : tabulate p = p := by
  funext i
  fin_cases i <;> rfl

def allWires : List Wire := (permutations 6).map fun p => tabulate p

/-- An arbitrary permutation of the four upright thin slots. -/
def uprightFour (p : Equiv.Perm (Fin 4)) : Wire :=
  ![(p 0).castLE (by decide), (p 1).castLE (by decide),
    (p 2).castLE (by decide), (p 3).castLE (by decide), 4,5]

def fourList : List Wire := (permutations 4).map uprightFour

/-- Lift a relabeling of the packets to their six thin slots. -/
def packetOrder (p : Equiv.Perm (Fin 3)) (i : Fin 6) : Fin 6 :=
  ⟨2*(p ⟨i.val/2, by omega⟩).val+i.val%2, by have := (p ⟨i.val/2, by omega⟩).isLt; omega⟩

def packetOrders : List (Wire × Wire) := (permutations 3).map fun p =>
  (tabulate (packetOrder p), tabulate (packetOrder p.symm))

/-- Independent exchanges of the two slots within each packet. -/
def innerList : List Wire := ([false,true] : List Bool).flatMap fun a =>
  ([false,true] : List Bool).flatMap fun b => ([false,true] : List Bool).map fun c =>
    ![if a then 1 else 0, if a then 0 else 1,
      if b then 3 else 2, if b then 2 else 3, if c then 5 else 4, if c then 4 else 5]

end BlockPermanents.ThreeWire
