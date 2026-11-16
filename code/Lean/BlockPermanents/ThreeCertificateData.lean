import BlockPermanents.ThreeWire
import Mathlib.Tactic.Ring

namespace BlockPermanents.ThreeWire
open scoped BigOperators
open Closures

/-- Flip the slots independently in three packets. -/
def inner (a b c : Bool) : Wire :=
  ![if a then 1 else 0, if a then 0 else 1, if b then 3 else 2, if b then 2 else 3,
    if c then 5 else 4, if c then 4 else 5]

/-- Sorting the three pairs at the input and then orienting each output pair
by first occurrence chooses a wire representing the same compressed operator. -/
def normal (p : Wire) : Wire :=
  let r := inner (decide (p 1 < p 0)) (decide (p 3 < p 2)) (decide (p 5 < p 4))
  let q := p ∘ r
  let first (a : Fin 6) := ([q 0,q 1,q 2,q 3,q 4,q 5] : List (Fin 6)).idxOf a
  let l := inner (decide (first 1 < first 0)) (decide (first 3 < first 2))
    (decide (first 5 < first 4))
  l ∘ q

/-- Base-six code of the six output indices. -/
def code (p : Wire) : ℕ :=
  p 0 + 6*((p 1 : ℕ) + 6*((p 2 : ℕ) + 6*((p 3 : ℕ) + 6*((p 4 : ℕ) + 6*(p 5 : ℕ)))))

def digit (n : ℕ) : Fin 6 := ⟨n%6, Nat.mod_lt _ (by decide)⟩
def decode (n : ℕ) : Wire :=
  ![digit n, digit (n/6), digit (n/6/6), digit (n/6/6/6), digit (n/6/6/6/6),
    digit (n/6/6/6/6/6)]

theorem decode_code (p : Wire) : decode (code p) = p := by
  have dm (i : Fin 6) (n : ℕ) : ((i : ℕ) + 6*n)/6=n := by omega
  have mm (i : Fin 6) (n : ℕ) : digit ((i : ℕ) + 6*n)=i := by apply Fin.ext; change _%6=_; omega
  funext j
  fin_cases j <;> simp [decode, code, dm, mm, digit, Nat.mod_eq_of_lt]

/-- An evaluator may absorb each packet's two-slot clasp on both sides. -/
def PacketInvariant (f : Wire → ℂ) : Prop :=
  ∀ a b c p, f (inner a b c ∘ p) = f p ∧ f (p ∘ inner a b c) = f p

theorem eval_normal {f : Wire → ℂ} (hf : PacketInvariant f) (p : Wire) :
    f (decode (code (normal p))) = f p := by
  rw [decode_code]
  unfold normal
  exact ((hf _ _ _ _).1).trans ((hf _ _ _ _).2)

abbrev Terms := List (ℤ × Wire)
abbrev Bins := List (ℕ × ℤ)

def weightedWires (c : ℤ) (l : List Wire) : Terms := l.map fun p => (c,p)
def gluedWires (a : List Wire) (s : Wire) (b : List Wire) : List Wire :=
  a.flatMap fun p => b.map fun q => p ∘ s ∘ q

/-- A spectator choice before simultaneous relabeling. All denominators
are cleared. The unit coefficient for the complete cyclic average is 288. -/
def correctionTerms : Terms :=
  weightedWires 96 (gluedWires pairList thinSwap pairList) ++
  weightedWires 4 (gluedWires fourList thinSwap fourList) ++
  weightedWires 3 (gluedWires fourList fullSwap fourList) ++
  weightedWires (-3) (gluedWires fourList fullSwap pairList) ++
  weightedWires (-3) (gluedWires pairList fullSwap fourList) ++
  weightedWires (-24) (gluedWires pairList fullSwap pairList)

def relabel (g : Wire × Wire) (x : ℤ × Wire) : ℤ × Wire :=
  (x.1, g.1 ∘ x.2 ∘ g.2)

def cyclicTerms : Terms :=
  packetOrders.flatMap fun g => correctionTerms.map (relabel g)

/-- Each fine shuffle carries 36=288·90/720. The six whole
packet routings each carry −288. -/
def targetTerms : Terms := weightedWires 36 allWires ++ weightedWires (-288) (packetOrders.map Prod.fst)

/-- Update a sparse sorted coefficient table. -/
def addBin (key : ℕ) (v : ℤ) : Bins → Bins
  | [] => [(key,v)]
  | (j,x)::xs => if key=j then (j,v+x)::xs else
      if key < j then (key,v)::(j,x)::xs else (j,x)::addBin key v xs

def table (l : Terms) : Bins :=
  (l.foldl (fun bins e => addBin (code (normal e.2)) e.1 bins) []).filter (fun e => e.2 ≠ 0)

def evalBins (f : Wire → ℂ) (bins : Bins) : ℂ :=
  (bins.map fun e => (e.2 : ℂ) * f (decode e.1)).sum

def evalTerms (f : Wire → ℂ) (l : Terms) : ℂ :=
  (l.map fun e => (e.1 : ℂ) * f e.2).sum

private theorem eval_addBin (f : Wire → ℂ) (key : ℕ) (v : ℤ) (bins : Bins) :
    evalBins f (addBin key v bins) = (v : ℂ)*f (decode key) + evalBins f bins := by
  induction bins with
  | nil => simp [evalBins,addBin]
  | cons e bins ih =>
    rcases e with ⟨j,x⟩
    simp only [addBin]
    split_ifs with h h'
    · subst j; simp [evalBins, add_mul]; ring
    · simp [evalBins, add_assoc]
    · change (x : ℂ)*f (decode j) + evalBins f (addBin key v bins) = (v : ℂ)*f (decode key) + ((x : ℂ)*f (decode j) + evalBins f bins)
      rw [ih]; ring

private theorem eval_filter (f : Wire → ℂ) (l : Bins) :
    evalBins f (l.filter fun e => e.2 ≠ 0) = evalBins f l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨j,x⟩
    by_cases h : x = 0
    · subst x; simpa [evalBins] using ih
    · simpa [evalBins,h] using congrArg (fun z : ℂ => (x : ℂ)*f (decode j)+z) ih

theorem table_sound {f : Wire → ℂ} (hf : PacketInvariant f) (l : Terms) :
    evalBins f (table l) = evalTerms f l := by
  rw [table, eval_filter]
  have aux (q : Terms) (b : Bins) :
      evalBins f (q.foldl (fun bins e => addBin (code (normal e.2)) e.1 bins) b) =
      evalTerms f q + evalBins f b := by
    induction q generalizing b with
    | nil => simp [evalTerms]
    | cons e q ih =>
      rw [List.foldl_cons, ih, eval_addBin, eval_normal hf]
      change _ = ((_ : ℂ)*f e.2 + evalTerms f q) + _
      ring
  simpa [evalBins] using aux l []

end BlockPermanents.ThreeWire
