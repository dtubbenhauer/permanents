import BlockPermanents.Occupation
import BlockPermanents.Quadratic
import BlockPermanents.Closures
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.OfFn

/-! Complex mixed closures for the five quadratic packets of Section 9.
A subset records precisely the positions colored by the second basis vector.
The ordinary complex coordinate pairing on these subsets is the thin-word
inner product. Distinct positions of equal packets remain distinct. -/

namespace BlockPermanents.MarkedWitness
open scoped BigOperators
open Negative Occupation Closures
noncomputable section

/-- The complex word vector of a quadratic with rational occupation coefficients. -/
def quadraticWord (p : Quad) (s : Finset (Fin 2)) : ℂ := expand (quadCoeff p) s

private theorem cast_wordPair {d : ℕ} (x y : Finset (Fin d) → ℚ) :
    (wordPair x y : ℂ) = bracket (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) := by
  simp [wordPair, bracket, Rat.cast_sum]

theorem gram_complex (p q : Quad) :
    (gram p q : ℂ) = bracket (quadraticWord p) (quadraticWord q) := by
  rw [gram_eq_wordPair]
  exact cast_wordPair _ _

/-- A thin factor e₀+u e₁. -/
def atom (u : ℂ) (i : Fin 2) : ℂ := if i = 0 then 1 else u

/-- Split the two positions into an orthonormal binary word. -/
def bits (s : Finset (Fin 2)) (i : Fin 2) : Fin 2 := if i ∈ s then 1 else 0

/-- Explicit two-slot symmetrization of two actual complex linear factors. -/
theorem factors_give_clasp {p : Quad} {u v : ℂ} (hs : coords p = linearProduct u v)
    (s : Finset (Fin 2)) :
    quadraticWord p s = clasp (pureWord ![atom u, atom v]) (bits s) := by
  have ha := congrArg Prod.fst hs
  have hb := congrArg (fun z : ℂ × ℂ × ℂ => z.2.1) hs
  have hc := congrArg (fun z : ℂ × ℂ × ℂ => z.2.2) hs
  change (p.a : ℂ) = 1 at ha
  change (p.b : ℂ) = u+v at hb
  change (p.c : ℂ) = u*v at hc
  have split2 (f : Equiv.Perm (Fin 2) → ℂ) :
      ∑ σ, f σ = f 1 + f (Equiv.swap 0 1) := by
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp f, Fintype.sum_prod_type]
    simp [Fin.sum_univ_succ, Fintype.sum_unique]; rfl
  have hh : ∀ a : Finset (Fin 2), a = ∅ ∨ a = {0} ∨ a = {1} ∨ a = {0,1} := by decide
  rcases hh s with hs|hs|hs|hs <;> subst s <;>
    norm_num [clasp, sumSlots, split2, pureWord, Fin.prod_univ_succ, quadraticWord,
      expand, quadCoeff, Nat.choose, atom, bits, Equiv.swap_apply_def, ha,hb,hc] <;> ring

theorem witness_complex_factors (p : Quad) (hp : p ∈ witness) :
    ∃ u v : ℂ, ∀ s, quadraticWord p s = clasp (pureWord ![atom u,atom v]) (bits s) := by
  obtain ⟨u,v,h⟩ := witness_factors p hp
  exact ⟨u,v,factors_give_clasp h⟩

/-- Pick a labeled position and keep the remaining slots in their original order. -/
theorem picks_sum {α : Type} {R : Type*} [AddCommMonoid R] {n : ℕ}
    (x : Fin (n+1) → α) (F : α → List α → R) :
    ((picks (List.ofFn x)).map (fun t => F t.1 t.2)).sum =
    ∑ i : Fin (n+1), F (x i) (List.ofFn (x ∘ i.succAbove)) := by
  induction n generalizing F with
  | zero => simp [List.ofFn_succ, picks]
  | succ n ih =>
    rw [List.ofFn_succ, picks, List.map_cons, List.sum_cons, Fin.sum_univ_succ, List.map_map]
    simp only [Fin.zero_succAbove, Function.comp_def]
    congr 1
    have hh := ih (fun i => x i.succ) (fun a l => F a (x 0 :: l))
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [List.ofFn_succ]
    simp [Fin.succAbove_zero_apply, Fin.succ_succAbove_zero, Function.comp_def]

private theorem picks2_sum {α : Type} {R : Type*} [AddCommMonoid R] {n : ℕ}
    (x y : Fin (n+1) → α) (F : α → List α → α → List α → R) :
    ((picks (List.ofFn x)).map (fun a => ((picks (List.ofFn y)).map
      (fun b => F a.1 a.2 b.1 b.2)).sum)).sum =
    ∑ i, ∑ j, F (x i) (List.ofFn (x ∘ i.succAbove)) (y j) (List.ofFn (y ∘ j.succAbove)) := by
  rw [picks_sum x (fun a left => ((picks (List.ofFn y)).map (fun b => F a left b.1 b.2)).sum)]
  apply Finset.sum_congr rfl
  intro i _
  exact picks_sum y (F _ _)

private theorem permanent_sorted {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    A.permanent = ∑ j, A 0 j * (Matrix.of (fun u v : Fin n => A u.succ (j.succAbove v))).permanent := by
  rw [← Matrix.permanent_transpose A, Quadratic.permanent_succ]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.permanent_transpose (Matrix.of (fun u v : Fin n => A u.succ (j.succAbove v)))]
  congr 1
  let sw := Equiv.swap (0 : Fin (n+1)) j
  let f : Fin n ≃ {b : Fin (n+1) // b ≠ j} :=
    (finSuccAboveEquiv 0).trans (sw.subtypeEquiv (fun a => by
      change (a ≠ 0) ↔ sw a ≠ j
      rw [← show sw 0 = j from Equiv.swap_apply_left _ _, sw.injective.ne_iff]))
  let p := (finSuccAboveEquiv j).trans f.symm
  let B : Matrix (Fin n) (Fin n) R := fun u v => A v.succ (sw u.succ)
  have hf (u : Fin n) : sw (p u).succ = j.succAbove u :=
    congrArg Subtype.val (f.apply_symm_apply (finSuccAboveEquiv j u))
  change B.permanent = _
  rw [← Matrix.permanent_permute_cols p B]
  congr 1
  ext u v
  exact congrArg (A v.succ) (hf u)

/-- The recursively enumerated coarse evaluator is the mathlib permanent
of an actual complex mixed packet Gram matrix, for every number of packets. -/
theorem coarse_complex {n : ℕ} (x y : Fin n → Quad) :
    (coarse (List.ofFn x) (List.ofFn y) : ℂ) =
    (crossGram (quadraticWord ∘ x) (quadraticWord ∘ y)).permanent := by
  induction n with
  | zero => simp [coarse, Matrix.permanent_isEmpty]
  | succ n ih =>
    rw [List.ofFn_succ (f := x), coarse, picks_sum y (fun q rest => gram (x 0) q * coarse (List.ofFn fun a => x a.succ) rest),
      Rat.cast_sum, permanent_sorted]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Rat.cast_mul, gram_complex, Function.comp_apply, Matrix.of_apply]
    rw [ih (fun a => x a.succ) (y ∘ i.succAbove)]
    rfl

/-- The thin-slot symmetrizer on complex binary word coordinates. -/
def symWord {d : ℕ} (x : Finset (Fin d) → ℂ) (w : Finset (Fin d)) : ℂ :=
  (∑ σ : Equiv.Perm (Fin d), x (w.map σ.toEmbedding)) / (d.factorial : ℂ)

private theorem cast_symWord {d : ℕ} (x : Finset (Fin d) → ℚ) (w : Finset (Fin d)) :
    ((permSum x w / (d.factorial : ℚ) : ℚ) : ℂ) = symWord (fun v => (x v : ℂ)) w := by
  simp [symWord, permSum, Rat.cast_sum]

/-- Apply the full permutation clasp to an actual binary word tensor.
Both vectors can have arbitrary rational entries, embedded in ℂ. -/
def fineForm (n : ℕ) (x y : Fin n → Quad) : ℂ :=
  let d := 2*(List.ofFn x).length
  let z (a : Fin n → Quad) (w : Finset (Fin d)) : ℂ :=
    symWord (fun v => (packetWordVector d (List.ofFn a) v : ℂ)) w
  ((d.factorial : ℂ) / 2^(List.ofFn x).length) * bracket (z x) (z y)

theorem fine_complex {n : ℕ} (x y : Fin n → Quad) :
    (fine (List.ofFn x) (List.ofFn y) : ℂ) = fineForm n x y := by
  rw [fine_eq_symmetrized_tensor _ _ (by simp)]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, cast_wordPair, fineForm, symWord, permSum, Rat.cast_sum]
  ring


/-- Mixed fine minus coarse closure on actual complex quadratics. -/
def X {n : ℕ} (x y : Fin n → Quad) : ℂ :=
  fineForm n x y - (crossGram (quadraticWord ∘ x) (quadraticWord ∘ y)).permanent

theorem cast_defect {n : ℕ} (x y : Fin n → Quad) :
    (defect (List.ofFn x) (List.ofFn y) : ℂ) = X x y := by
  simp only [Negative.defect, Rat.cast_sub, fine_complex, coarse_complex, X]

/-- Extend a mixed form by an identity spectator and average its two ends
over all positions independently. Slot deletion is ordered by succAbove. -/
def liftForm {n : ℕ} (K : (Fin n → Quad) → (Fin n → Quad) → ℂ) (x y : Fin (n+1) → Quad) : ℂ :=
  (∑ i, ∑ j, bracket (quadraticWord (x i)) (quadraticWord (y j)) *
    K (x ∘ i.succAbove) (y ∘ j.succAbove)) / (n+1 : ℂ)^2

/-- The polarized recurrence for A_j, with the manuscript's j²/(j−1)
factor, on the chosen quadratic packets. -/
def A : (n : ℕ) → (Fin n → Quad) → (Fin n → Quad) → ℂ
  | 0, _, _ | 1, _, _ => 0
  | n+2, x, y => X x y + (n+2 : ℂ)^2 / (n+1) * liftForm (A (n+1)) x y

theorem transfer_complex {n : ℕ} (x y : Fin n → Quad) :
    (transfer n (List.ofFn x) (List.ofFn y) : ℂ) = A n x y := by
  match n with
  | 0 | 1 => simp [A, transfer]
  | n+2 =>
    change ((defect (List.ofFn x) (List.ofFn y) +
      ((picks (List.ofFn x)).map (fun ⟨p, left⟩ =>
        ((picks (List.ofFn y)).map (fun ⟨q, right⟩ =>
          gram p q * transfer (n+1) left right)).sum)).sum / (n+1 : ℚ) : ℚ) : ℂ) = _
    simp only [Rat.cast_add, Rat.cast_div, cast_defect, A, liftForm]
    congr 1
    rw [picks2_sum x y (fun p left q right => gram p q * transfer (n+1) left right)]
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, gram_complex,
      transfer_complex (n := n+1)]
    push_cast
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn2 : (n:ℂ)+2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+1)
    rw [show (n:ℂ)+1+1 = n+2 by ring]
    field_simp [hn, hn2]
    ring

private def prepend {n : ℕ} (t : Quad) (v : Fin n → Quad) : Fin (n+1) → Quad := Fin.cons t v

private theorem prepend_list {n : ℕ} (t : Quad) (v : Fin n → Quad) :
    List.ofFn (prepend t v) = t :: List.ofFn v := by
  rw [List.ofFn_succ]; simp [prepend]

/-- The mixed four-term marked transfer, before any specializing arithmetic.
The two single crossing terms have distinct bra and ket exits. -/
def marked (x : Fin 4 → Quad) (t : Quad) : ℂ :=
  let G (u v : Quad) := bracket (quadraticWord u) (quadraticWord v)
  let moved := (∑ i, ∑ j, G (x i) (x j) *
    A 4 (prepend t (x ∘ i.succAbove)) (prepend t (x ∘ j.succAbove))) / 16
  let bra := (∑ i, G (x i) t * A 4 (prepend t (x ∘ i.succAbove)) x) / 4
  let ket := (∑ j, G t (x j) * A 4 x (prepend t (x ∘ j.succAbove))) / 4
  X (prepend t x) (prepend t x) - G t t * A 4 x x + 4 * moved - 3/2 * (bra + ket)

theorem marked_complex (x : Fin 4 → Quad) (t : Quad) :
    (markedValue (List.ofFn x) t : ℂ) = marked x t := by
  unfold markedValue marked
  dsimp only
  rw [picks2_sum x x (fun p left q right => gram p q * transfer 4 (t::left) (t::right))]
  rw [picks_sum x (fun p left => gram p t * transfer 4 (t::left) (List.ofFn x)),
    picks_sum x (fun q right => gram t q * transfer 4 (List.ofFn x) (t::right))]
  simp only [← prepend_list, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_sum,
    Rat.cast_ofNat, cast_defect, gram_complex, transfer_complex]

def otherFive : Fin 4 → Quad := ![unitPacket,unitPacket,unitPacket,fourthPacket]

/-- The complex mixed form built from the full word clasp, the actual Gram
permanent, and all spectator exits has the negative fifth value in Section 9. -/
theorem marked_fifth : marked otherFive fifthPacket = (-565839/2000 : ℂ) := by
  rw [← marked_complex]
  change (markAtFive : ℂ) = _
  rw [fifth_value]
  norm_num

/-- All five marked endpoints and their mean are complex word contractions. -/
theorem other_marks :
    marked ![unitPacket,unitPacket,fourthPacket,fifthPacket] unitPacket = (9041984725911/2000:ℂ) ∧
    marked ![unitPacket,unitPacket,unitPacket,fifthPacket] fourthPacket = (18083516817/4:ℂ) := by
  constructor
  · rw [← marked_complex]
    change (markAtUnit : ℂ) = _
    rw [first_value]; norm_num
  · rw [← marked_complex]
    change (markAtFour : ℂ) = _
    rw [fourth_value]; norm_num

def five : Fin 5 → Quad := ![unitPacket,unitPacket,unitPacket,fourthPacket,fifthPacket]

theorem witness_complex_gap : X five five = (18083856010197/5000 : ℂ) := by
  rw [← cast_defect]
  change (Negative.defect witness witness : ℂ) = _
  rw [mean_value]; norm_num

end
end BlockPermanents.MarkedWitness
