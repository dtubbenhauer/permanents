import BlockPermanents.ThreeCertificateData
import BlockPermanents.Bridges

namespace BlockPermanents.ThreeWire
open scoped BigOperators ComplexConjugate
open Closures Bend

private theorem inner_involution (a b c : Bool) : Function.Involutive (inner a b c) := by
  cases a <;> cases b <;> cases c <;> intro i <;> fin_cases i <;> rfl

private def flip (a : Bool) : Equiv.Perm (Fin 2) :=
  if a then Equiv.swap 0 1 else 1

private theorem on_pair {D : Type*} (F : (Fin 2 → D) → ℂ)
    (h : ∀ (w : Fin 2 → D) (p : Equiv.Perm (Fin 2)), F (w ∘ p) = F w)
    (a : Bool) (x y : D) : F ![if a then y else x, if a then x else y] = F ![x,y] := by
  cases a with
  | false => rfl
  | true =>
    let p : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hp : (![x,y] : Fin 2 → D) ∘ p = ![y,x] := by funext i; fin_cases i <;> rfl
    change F ![y,x] = F ![x,y]
    rw [← hp, h]

theorem symmetric_word_perm {d k : ℕ} {F : Word d k → ℂ} (h : Symmetric F)
    (w : Word d k) (p : Equiv.Perm (Fin k)) : F (w ∘ p) = F w := by
  have h' : clasp F = F := (Bridges.symClasp_action d k F).symm.trans h
  rw [← h']
  exact clasp_invariant F p.symm w

private theorem boundary_inner {D : Type*} (F G H : (Fin 2 → D) → ℂ)
    (hF : ∀ w (p : Equiv.Perm (Fin 2)), F (w ∘ p) = F w)
    (hG : ∀ w (p : Equiv.Perm (Fin 2)), G (w ∘ p) = G w)
    (hH : ∀ w (p : Equiv.Perm (Fin 2)), H (w ∘ p) = H w)
    (w : Words D) (a b c : Bool) : boundary F G H (w ∘ inner a b c) = boundary F G H w := by
  unfold boundary
  have h (e : Bool) (i j : Fin 6) : w (if e then j else i) = if e then w j else w i := by
    cases e <;> rfl
  simp [inner, h, on_pair _ hF, on_pair _ hG, on_pair _ hH]

/-- Sums over words allow independent flips of either end when every packet
is symmetric. This is the hypothesis of the small routing-table certificate. -/
theorem boundary_invariant {d : ℕ} {F G H : Word d 2 → ℂ}
    (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H) :
    PacketInvariant (evaluateWord (boundary F G H)) := by
  intro a b c p
  let g := inner a b c
  let z := boundary F G H
  have iz (w : Words (Fin d)) : z (w ∘ g) = z w :=
    boundary_inner _ _ _ (symmetric_word_perm hF) (symmetric_word_perm hG)
      (symmetric_word_perm hH) w _ _ _
  constructor
  · apply Fintype.sum_equiv ((Function.Involutive.toPerm g (inner_involution a b c)).arrowCongr (Equiv.refl (Fin d)))
    intro w
    change conj (z w) * z (w ∘ g ∘ p) = conj (z (w ∘ g)) * z ((w ∘ g) ∘ p)
    rw [iz]
    rfl
  · unfold evaluateWord bracket
    apply Finset.sum_congr rfl
    intro w _
    exact congrArg _ (iz (w ∘ p))

private theorem weighted_eval (f : Wire → ℂ) (c : ℤ) (l : List Wire) :
    evalTerms f (weightedWires c l) = (c : ℂ) * (l.map f).sum := by
  simp [weightedWires, evalTerms, List.sum_map_mul_left, Function.comp_def]

private theorem glue_eval (f : Wire → ℂ) (l : List Wire) (s : Wire) (r : List Wire) :
    ((gluedWires l s r).map f).sum = glue f l s r := by
  unfold gluedWires glue
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_map] using congrArg (fun z : ℂ => (r.map (fun b => f (a ∘ s ∘ b))).sum+z) ih

private theorem append_eval (f : Wire → ℂ) (l r : Terms) :
    evalTerms f (l++r) = evalTerms f l + evalTerms f r := by simp [evalTerms]

/-- The transparent coefficients of the three halves after clearing
denominators. The positive D-square expands to the four gluing terms. -/
theorem correction_eval (f : Wire → ℂ) :
    evalTerms f correctionTerms =
      96 * glue f pairList thinSwap pairList + 4 * glue f fourList thinSwap fourList +
      3 * (glue f fourList fullSwap fourList - glue f fourList fullSwap pairList -
        glue f pairList fullSwap fourList + glue f pairList fullSwap pairList) -
      27 * glue f pairList fullSwap pairList := by
  simp only [correctionTerms, append_eval, weighted_eval, glue_eval]
  norm_num
  ring

end BlockPermanents.ThreeWire
