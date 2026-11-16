import BlockPermanents.RoutedSector

/-! # Gluing two routed caps along their positive and supported dual cables

A thin routing is a bijection from the ordered survivors and marked slots to
the positive slots. An internal clasp is a finite average of these routings.
The lower cap inserts a supported cup in each dual slot. -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section
variable {I D : Type*} [DecidableEq D]

universe u
def Mark {D : Type u} (S : Finset D) : ℕ → Type u
  | 0 => PUnit.{u+1}
  | r+1 => Mark S r × S

def contract (S : Finset D) : (r : ℕ) →
    ((Cable I r → D) → Mark S r → ℂ) → Tensor I D
  | 0,x => fun w => x w PUnit.unit
  | r+1,x => contract S r (fun v c => ∑ b : S,x (extendWord v b.val) (c,b))

def reflect (S : Finset D) : (r : ℕ) → Tensor I D → (Cable I r → D) → Mark S r → ℂ
  | 0,f => fun w _ => f w
  | r+1,f => fun w c => if w none=c.2.val then reflect S r f (w ∘ some) c.1 else 0

theorem contract_reflect (S : Finset D) (r : ℕ) (T : Operator (Cable I r) D)
    (f : Tensor I D) : contract S r (fun v c => T (fun u => reflect S r f u c) v) =
      close S r T f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change contract S r (fun v c => ∑ b : S,T (fun u =>
      if u none=b.val then reflect S r f (u ∘ some) c else 0) (extendWord v b.val)) = _
    have h (v : Cable I r → D) (c : Mark S r) :
        (∑ b : S,T (fun u => if u none=b.val then reflect S r f (u ∘ some) c else 0)
          (extendWord v b.val)) = trace S T (fun u => reflect S r f u c) v := by
      unfold trace
      exact S.sum_coe_sort (fun b : D => T (fun u => if u none=b then
        reflect S r f (u ∘ some) c else 0) (extendWord v b))
    rw [show (fun v c => ∑ b : S,T (fun u => if u none=b.val then
      reflect S r f (u ∘ some) c else 0) (extendWord v b.val)) =
      (fun v c => trace S T (fun u => reflect S r f u c) v) from funext fun v => funext (h v)]
    exact ih _

def routedCap (S : Finset D) (r : ℕ) (p : Perm (Cable I r))
    (x : (Cable I r → D) → Mark S r → ℂ) : Tensor I D :=
  contract S r (fun v c => x (v ∘ p) c)

def reflectedCap (S : Finset D) (r : ℕ) (p : Perm (Cable I r))
    (f : Tensor I D) (v : Cable I r → D) (c : Mark S r) :=
  reflect S r f (v ∘ p.symm) c

theorem glued (S : Finset D) (r : ℕ) (p q : Perm (Cable I r)) (f : Tensor I D) :
    routedCap S r p (reflectedCap S r q f) =
      close S r (wire S (q.symm.trans p) ∅) f := by
  rw [← contract_reflect]
  simp only [routedCap,reflectedCap,wire,Finset.not_mem_empty,false_implies,
    forall_const,if_true]
  rfl

/-- The reflected and upright actual thin cap compose to the claimed
occupation monomial, uniformly in the support and the output sector. -/
theorem cap_sector {N d : ℕ} (r : ℕ) (p q : Perm (Cable (Fin N) r)) :
    ∃ j t : ℕ, t≤N ∧ j+t≤r ∧
      ∀ (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
        Closures.clasp (routedCap S r p (reflectedCap S r q f)) w =
          (S.card : ℂ)^j * (((occupied S w).card.choose t : ℕ) : ℂ) /
            (N.choose t : ℂ) * f w := by
  simpa only [glued] using sector_monomial (d:=d) r (q.symm.trans p)

end
end BlockPermanents.RoutedTrace
