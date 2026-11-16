import BlockPermanents.OccupationSplit
import BlockPermanents.Routings
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.Finset.Option

/-! # Following the marked dual strands in the intersection form

A word permutation represents a term of the opened clasps. The partial trace sums
over the supported basis colours on each strand of the dual. Removing one such
strand either closes a loop or marks a surviving path, including paths that
already carry the support projection. -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section
variable {I D : Type*} [DecidableEq I] [DecidableEq D]

abbrev Tensor (I D : Type*) := (I → D) → ℂ
abbrev Operator (I D : Type*) := Tensor I D → Tensor I D

def wire (S : Finset D) (p : Perm I) (M : Finset I) : Operator I D :=
  fun f w => if ∀ i ∈ M, w i ∈ S then f (w ∘ p) else 0

def extendWord (w : I → D) (c : D) : Option I → D := fun i => i.elim c w

/-- Contract the distinguished input with the distinguished output, using
the support projector on that thin strand. -/
def trace (S : Finset D) (T : Operator (Option I) D) : Operator I D :=
  fun f w => ∑ c ∈ S, T (fun v => if v none = c then f (v ∘ some) else 0) (extendWord w c)

private theorem survives (S : Finset D) (w : I → D) {c : D} (hc : c ∈ S) (M : Finset (Option I)) :
    (∀ i ∈ M, extendWord w c i ∈ S) ↔ ∀ i ∈ M.eraseNone, w i ∈ S := by
  constructor
  · exact fun h i hi => h (some i) (mem_eraseNone.mp hi)
  · rintro h (_|i) hi
    · exact hc
    · exact h i (mem_eraseNone.mpr hi)

private theorem splice (p : Perm (Option I)) (w : I → D) (c : D)
    (h : extendWord w c (p none) = c) :
    (extendWord w c ∘ p ∘ some) = w ∘ p.removeNone := by
  funext i
  cases hi : p (some i) with
  | none =>
    have he := p.removeNone_none hi
    have hx := congrArg (extendWord w c) he
    rw [h] at hx
    simpa [Function.comp_def,hi,extendWord] using hx.symm
  | some j =>
    have he := (p.removeNone_some ⟨j,hi⟩).trans hi
    simp [Function.comp_def,hi,Option.some.inj he,extendWord]

def nextMarks (p : Perm (Option I)) (M : Finset (Option I)) : Finset I :=
  (p none).elim M.eraseNone (fun j => insert j M.eraseNone)

theorem trace_wire (S : Finset D) (p : Perm (Option I)) (M : Finset (Option I)) :
    trace S (wire S p M) =
      fun f w => (S.card : ℂ)^(if p none = none then 1 else 0) *
        wire S p.removeNone (nextMarks p M) f w := by
  funext f w
  let v := f (w ∘ p.removeNone)
  have summand (c : D) (hc : c ∈ S) :
      wire S p M (fun z => if z none=c then f (z ∘ some) else 0) (extendWord w c) =
        if (∀ i ∈ M.eraseNone,w i ∈ S) ∧ extendWord w c (p none)=c then v else 0 := by
    simp only [wire,survives S w hc]
    split_ifs with h g e <;> first | rfl | simp_all [v,splice p w c,Function.comp_assoc]
  simp only [trace,Finset.sum_congr rfl summand]
  cases h : p none with
  | none =>
    have hm : nextMarks p M = M.eraseNone := by simp [nextMarks,h]
    rw [hm]
    change (∑ c ∈ S, if (∀ i ∈ M.eraseNone, w i ∈ S) ∧ c=c then v else 0) = _
    let ok := ∀ i ∈ M.eraseNone, w i ∈ S
    change (∑ c ∈ S, if ok ∧ c=c then v else 0) =
      (S.card : ℂ)^(if (none : Option I)=none then 1 else 0) * (if ok then v else 0)
    by_cases e : ok
    · rw [if_pos e]
      have z (c : D) : (if ok ∧ c=c then v else 0) = v := if_pos ⟨e,rfl⟩
      rw [Finset.sum_congr rfl (fun c _ => z c)]
      simp
    · rw [if_neg e]
      have z (c : D) : (if ok ∧ c=c then v else 0) = 0 := if_neg (fun a => e a.1)
      rw [Finset.sum_congr rfl (fun c _ => z c)]
      simp

  | some j =>
    have hm : nextMarks p M = insert j M.eraseNone := by simp [nextMarks,h]
    rw [hm]
    change (∑ c ∈ S, if (∀ i ∈ M.eraseNone, w i ∈ S) ∧ w j=c then v else 0) = _
    let ok := ∀ i ∈ M.eraseNone, w i ∈ S
    have hj : (∀ i ∈ insert j M.eraseNone, w i ∈ S) ↔ w j ∈ S ∧ ok := Finset.forall_mem_insert _ _ _
    change (∑ c ∈ S, if ok ∧ w j=c then v else 0) =
      (S.card : ℂ)^(if (some j : Option I)=none then 1 else 0) *
        (if ∀ i ∈ insert j M.eraseNone, w i ∈ S then v else 0)
    rw [if_neg (Option.some_ne_none j),pow_zero,one_mul]
    by_cases e : ok
    · have z (c : D) : (if ok ∧ w j=c then v else 0) = (if w j=c then v else 0) := by
        by_cases g : w j=c
        · rw [if_pos ⟨e,g⟩,if_pos g]
        · rw [if_neg (fun a => g a.2),if_neg g]
      simp_rw [z]
      rw [Finset.sum_ite_eq]
      by_cases g : w j ∈ S
      · rw [if_pos g, if_pos (hj.mpr ⟨g,e⟩)]
      · rw [if_neg g, if_neg (fun a => g (hj.mp a).1)]
    · have z (c : D) : (if ok ∧ w j=c then v else 0) = 0 := if_neg (fun a => e a.1)
      simp_rw [z]
      rw [Finset.sum_const_zero,if_neg (fun a => e (hj.mp a).2)]


def Cable (I : Type*) : ℕ → Type _
  | 0 => I
  | r+1 => Option (Cable I r)

instance cableDecEq (r : ℕ) : DecidableEq (Cable I r) := by
  induction r with
  | zero => exact inferInstanceAs (DecidableEq I)
  | succ r ih => exact inferInstanceAs (DecidableEq (Option (Cable I r)))

def close (S : Finset D) : (r : ℕ) → Operator (Cable I r) D → Operator I D
  | 0, T => T
  | r+1, T => close S r (trace S T)

private theorem close_scale (S : Finset D) (r : ℕ) (T : Operator (Cable I r) D) (a : ℂ) :
    close S r (fun f w => a * T f w) = fun f w => a * close S r T f w := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change close S r (trace S (fun f w => a*T f w)) = _
    have e : trace S (fun f w => a*T f w) = fun f w => a * trace S T f w := by
      funext f w
      simp only [trace,Finset.mul_sum]
    rw [e,ih]; rfl

private theorem count_step (p : Perm (Option I)) (M : Finset (Option I)) :
    (if p none=none then 1 else 0) + (nextMarks p M).card ≤ M.card+1 := by
  have h := Finset.card_erase_le (s:=M) (a:=none)
  rw [← M.map_some_eraseNone,Finset.card_map] at h
  cases e : p none with
  | none => simpa [nextMarks,e,Nat.add_comm] using Nat.add_le_add_right h 1
  | some j =>
    have ht := Finset.card_insert_le j M.eraseNone
    simp only [nextMarks,e,Option.elim_some,Option.some_ne_none,if_false,zero_add]
    omega

/-- Each opened gluing has one permutation of surviving paths, a set of
marked survivors, and a loop count. All three are independent of the colours. -/
theorem follow (r : ℕ) (p : Perm (Cable I r)) (M : Finset (Cable I r)) :
    ∃ (j : ℕ) (q : Finset I) (u : Perm I), j+q.card ≤ r+M.card ∧
      ∀ (S : Finset D), close S r (wire S p M) =
        fun f w => (S.card : ℂ)^j * wire S u q f w := by
  induction r with
  | zero => exact ⟨0,M,p,by simp,fun _ => by funext f w; simp [close]⟩
  | succ r ih =>
    obtain ⟨j,q,u,hq,he⟩ := ih p.removeNone (nextMarks p M)
    let e := if p none=none then 1 else 0
    have hn : e+(nextMarks p M).card ≤ M.card+1 := count_step p M
    refine ⟨e+j,q,u,by omega,?_⟩
    intro S
    change close S r (trace S (wire S p M)) = _
    rw [trace_wire,close_scale,he]
    funext f w
    change (S.card : ℂ)^e*((S.card : ℂ)^j * wire S u q f w) = (S.card : ℂ)^(e+j)*_
    rw [pow_add,mul_assoc]

end
end BlockPermanents.RoutedTrace
