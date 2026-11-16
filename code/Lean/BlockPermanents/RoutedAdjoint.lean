import BlockPermanents.RoutedGluing

/-! # Reflection of an actual routed cap in the word inner product -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section
variable {I D : Type*} [DecidableEq D]

instance markFintype (S : Finset D) (r : ℕ) : Fintype (Mark S r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih => exact inferInstanceAs (Fintype (Mark S r × S))

instance cableFintype [Fintype I] (r : ℕ) : Fintype (Cable I r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype I)
  | succ r ih => exact inferInstanceAs (Fintype (Option (Cable I r)))

def join (S : Finset D) : (r : ℕ) → (I → D) → Mark S r → Cable I r → D
  | 0,w,_ => w
  | r+1,w,c => extendWord (join S r w c.1) c.2.val

theorem join_injective (S : Finset D) (r : ℕ) (c : Mark S r) :
    Function.Injective (fun w : I → D => join S r w c) := by
  induction r with
  | zero => exact Function.injective_id
  | succ r ih =>
    intro w v h
    apply ih c.1
    exact funext fun i => congrFun h (some i)

theorem contract_apply (S : Finset D) (r : ℕ) (x : (Cable I r → D) → Mark S r → ℂ) (w : I → D) :
    contract S r x w = ∑ c, x (join S r w c) c := by
  induction r with
  | zero => simp [contract,join,markFintype,Mark]
  | succ r ih =>
    change contract S r (fun u a => ∑ b : S,x (extendWord u b.val) (a,b)) w = _
    rw [ih]
    change _ = ∑ c : Mark S r × S, x (extendWord (join S r w c.1) c.2.val) c
    rw [Fintype.sum_prod_type]

theorem reflected_basis [Fintype I] [Fintype D] [DecidableEq I]
    (S : Finset D) (r : ℕ) (v : Cable I r → D) (c : Mark S r) (w : I → D) :
    reflect S r (fun u => if u=w then 1 else 0) v c =
      if join S r w c = v then 1 else 0 := by
  induction r with
  | zero => simp [reflect,join,eq_comm]
  | succ r ih =>
    have test : join S (r+1) w c=v ↔ v none=c.2.val ∧ join S r w c.1=v ∘ some := by
      constructor
      · rintro rfl; exact ⟨rfl,rfl⟩
      · rintro ⟨h,k⟩
        funext i
        cases i with
        | none => exact h.symm
        | some i => exact congrFun k i
    change (if v none=c.2.val then _ else 0)=_
    rw [ih,if_congr test rfl rfl]
    split_ifs <;> simp_all

/-- The seam matrix on orthonormal words. Its transpose-conjugate
is precisely the routed reflected cup on each output basis vector. -/
def capMatrix [Fintype I] [Fintype D] [DecidableEq I] (S : Finset D) (r : ℕ)
    (p : Perm (Cable I r)) :
    Matrix (I → D) ((Cable I r → D) × Mark S r) ℂ :=
  fun w v => if join S r w v.2 ∘ p = v.1 then 1 else 0

theorem reflect_adjoint [Fintype I] [Fintype D] [DecidableEq I]
    (S : Finset D) (r : ℕ) (p : Perm (Cable I r)) (w : I → D)
    (v : Cable I r → D) (c : Mark S r) :
    (capMatrix S r p).conjTranspose (v,c) w =
      reflectedCap S r p (fun u => if u=w then 1 else 0) v c := by
  rw [reflectedCap,reflected_basis,Matrix.conjTranspose_apply]
  have rel : join S r w c ∘ p=v ↔ join S r w c=v ∘ p.symm := by
    constructor
    · intro h; funext i; simpa [Function.comp_def] using congrFun h (p.symm i)
    · intro h; funext i; simpa [Function.comp_def] using congrFun h (p i)
  simp [capMatrix,rel]

end
end BlockPermanents.RoutedTrace
