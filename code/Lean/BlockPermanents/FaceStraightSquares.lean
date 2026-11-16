import BlockPermanents.FaceExit
import BlockPermanents.FiveOuterSquares

/-! Positive-order cuts left by straightening unit spectators on a marked face. -/
namespace BlockPermanents.FaceStraightSquares
open Bend Closures FaceExit MatchingFine FiveOuterSquares
noncomputable section

/-- All nonstraight cuts encountered when successively testing one spectator
against the remaining ones. An empty family contributes zero. -/
def spectatorRemainder {d : ℕ} : {n : ℕ} → (Fin n → Fin d → ℂ) → ℝ
  | 0, _ => 0
  | n+1, y =>
    properEnergy (fun _ : Fin 1 => y 0) (fun i : Fin n => y i.succ) +
      spectatorRemainder (fun i : Fin n => y i.succ)

theorem spectatorRemainder_nonneg {d n : ℕ} (y : Fin n → Fin d → ℂ) : 0 ≤ spectatorRemainder y := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (properEnergy_nonneg _ _) (ih _)

private theorem split {p n d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (e : Fin p ⊕ Fin n ≃ I) (x : I → Fin d → ℂ) :
    let l := fun i => x (e (.inl i))
    let r := fun i => x (e (.inr i))
    fine x = fine l * fine r + properEnergy l r := by
  have hp := straight_squares (fun i => x (e (.inl i))) (fun i => x (e (.inr i)))
  have he : Sum.elim (fun i => x (e (.inl i))) (fun i => x (e (.inr i))) = x ∘ e := by
    funext i
    cases i <;> rfl
  rw [he, fine_reindex] at hp
  exact hp

open private singleton from BlockPermanents.FaceExit in
/-- The straight term of the unit spectator permanent has weight one. -/
theorem spectator_squares {d n : ℕ} (y : Fin n → Fin d → ℂ) (hu : ∀ i, energy (y i) = 1) :
    fine y = 1 + spectatorRemainder y := by
  induction n with
  | zero => simp [fine, Matrix.permanent, spectatorRemainder]
  | succ n ih =>
    let e : Fin 1 ⊕ Fin n ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    have hl (i : Fin 1) : e (.inl i) = 0 := by fin_cases i; rfl
    have hr (i : Fin n) : e (.inr i) = i.succ := by apply Fin.ext; simp [e, finCongr]
    have eqn := split e y
    dsimp only at eqn
    simp only [hl, hr, singleton, hu, one_mul] at eqn
    rw [eqn, ih _ (fun i => hu i.succ), spectatorRemainder]
    ring

/-- The proper cuts between the prescribed face and its spectators, together
with the proper cuts within the spectator family weighted by the straight face. -/
def keepRemainder {p n d : ℕ} (x : Fin p → Fin d → ℂ) (y : Fin n → Fin d → ℂ) : ℝ :=
  properEnergy x y + fine x * spectatorRemainder y

theorem keepRemainder_nonneg {p n d : ℕ} (x : Fin p → Fin d → ℂ) (y : Fin n → Fin d → ℂ) :
    0 ≤ keepRemainder x y := by
  unfold keepRemainder
  apply add_nonneg (properEnergy_nonneg _ _)
  rw [fine_eq_energy]
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (spectatorRemainder_nonneg y)

/-- Keep any prescribed group of labels, with the other unit labels removed. -/
theorem keep_squares {p n d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (e : Fin p ⊕ Fin n ≃ I) (x : I → Fin d → ℂ) (hu : ∀ i, energy (x (e (.inr i))) = 1) :
    let l := fun i => x (e (.inl i))
    let r := fun i => x (e (.inr i))
    fine x = fine l + keepRemainder l r := by
  dsimp only
  rw [split e x, spectator_squares _ hu, keepRemainder]
  ring

open private singleton from BlockPermanents.FaceExit in
/-- Straightening to the three distinguished labels retains their
unsymmetrized survivor D and all positive-order cut energies. -/
theorem keep_three_squares {d n : ℕ} (A B C : Fin d → ℂ) (y : Fin n → Fin d → ℂ)
    (hu : ∀ i, energy (y i) = 1) :
    exitEnergy A B C y = energy (survivor A B C) + keepRemainder (fun _ : Fin 1 => survivor A B C) y := by
  let e : Fin 1 ⊕ Fin n ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
  have hl (i : Fin 1) : e (.inl i) = 0 := by fin_cases i; rfl
  have hr (i : Fin n) : e (.inr i) = i.succ := by apply Fin.ext; simp [e, finCongr]
  rw [exitEnergy_eq]
  simpa only [hl,hr, Fin.cons_zero, Fin.cons_succ,singleton] using
    keep_squares e (Fin.cons (survivor A B C) y) (by simpa only [hr,Fin.cons_succ] using hu)

/-- If one spectator H is retained, the prescribed face is the two-column
packet on D,H. The other spectators contribute precisely the proper cuts. -/
theorem keep_four_squares {d n : ℕ} (A B C H : Fin d → ℂ) (y : Fin n → Fin d → ℂ)
    (hu : ∀ i, energy (y i) = 1) :
    exitEnergy A B C (Fin.cons H y) = fine ![survivor A B C,H] + keepRemainder ![survivor A B C,H] y := by
  let V := survivor A B C
  let e : Fin 2 ⊕ Fin n ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 n))
  have hr (i : Fin n) : e (.inr i) = i.succ.succ := by apply Fin.ext; simp [e, finCongr]
  have hl : (fun j : Fin 2 => (Fin.cons V (Fin.cons H y) : Fin (n+2) → Fin d → ℂ) (e (.inl j))) = ![V,H] := by
    funext j
    fin_cases j
    · exact Fin.cons_zero ..
    · change (Fin.cons V (Fin.cons H y) : Fin (n+2) → Fin d → ℂ) (0 : Fin (n+1)).succ = H
      rw [Fin.cons_succ, Fin.cons_zero]
  rw [exitEnergy_eq]
  have eqn := keep_squares e (Fin.cons V (Fin.cons H y)) (by simpa only [hr, Fin.cons_succ] using hu)
  dsimp only at eqn
  simpa only [hl, hr, Fin.cons_succ] using eqn

end
end BlockPermanents.FaceStraightSquares
