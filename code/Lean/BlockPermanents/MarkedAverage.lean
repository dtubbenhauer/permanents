import BlockPermanents.MarkedWitness
import Mathlib.Data.List.FinRange

/-! Independent permutations at the input and output of the iterated transfer.
These identities connect spectator deletion with the packet-clasp average. -/
namespace BlockPermanents.MarkedWitness
open Negative Occupation Closures
open scoped BigOperators
noncomputable section

def Invariant {n : ℕ} (K : (Fin n → Quad) → (Fin n → Quad) → ℂ) : Prop :=
  ∀ x y (σ τ : Equiv.Perm (Fin n)), K (x ∘ σ) (y ∘ τ) = K x y

private theorem X_invariant {n : ℕ} : Invariant (@X n) := by
  intro x y σ τ
  have hf : fineForm n (x ∘ σ) (y ∘ τ) = fineForm n x y := by
    rw [← fine_complex, ← fine_complex]
    unfold fine
    simp only [List.length_ofFn]
    simp_rw [productCoeffs_perm (σ.ofFn_comp_perm x), productCoeffs_perm (τ.ofFn_comp_perm y)]
  unfold X
  rw [hf]
  congr 1
  let M := crossGram (quadraticWord ∘ x) (quadraticWord ∘ y)
  change ((M.submatrix σ id).submatrix id τ).permanent = M.permanent
  rw [Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

/-- The permutation induced on the remaining ordered slots after deleting i. -/
private def remaining {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) : Equiv.Perm (Fin n) :=
  ((finSuccAboveEquiv i).trans (σ.subtypeEquiv (fun a => by
      change a ≠ i ↔ σ a ≠ σ i
      rw [σ.injective.ne_iff]))).trans (finSuccAboveEquiv (σ i)).symm

private theorem remaining_eq {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) (j : Fin n) :
    (σ i).succAbove (remaining σ i j) = σ (i.succAbove j) := by
  apply congrArg Subtype.val ((finSuccAboveEquiv (σ i)).apply_symm_apply _)

private theorem reindexed_form {n : ℕ} {K : (Fin n → Quad) → (Fin n → Quad) → ℂ} (hK : Invariant K)
    (x y : Fin (n+1) → Quad) (σ τ : Equiv.Perm (Fin (n+1))) (i j : Fin (n+1)) :
    K ((x ∘ σ) ∘ i.succAbove) ((y ∘ τ) ∘ j.succAbove) =
    K (x ∘ (σ i).succAbove) (y ∘ (τ j).succAbove) := by
  rw [← hK (x ∘ (σ i).succAbove) (y ∘ (τ j).succAbove) (remaining σ i) (remaining τ j)]
  congr 1 <;> funext a <;> simp [remaining_eq]

private theorem lift_invariant {n : ℕ} {K : (Fin n → Quad) → (Fin n → Quad) → ℂ}
    (hK : Invariant K) : Invariant (liftForm K) := by
  intro x y σ τ
  unfold liftForm
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  apply Fintype.sum_equiv τ
  intro j
  simp only [Function.comp_apply, reindexed_form hK]

theorem A_invariant (n : ℕ) : Invariant (A n) := by
  match n with
  | 0 | 1 => unfold Invariant; intros; rfl
  | n+2 =>
    intro x y σ τ
    simp only [A, X_invariant x y σ τ, lift_invariant (A_invariant (n+1)) x y σ τ]

private theorem fixed_slot {n : ℕ} (f : Fin (n+1) → ℂ) :
    ∑ σ : Equiv.Perm (Fin (n+1)), f (σ 0) = (n.factorial : ℂ) * ∑ i, f i := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp (fun σ => f (σ 0)), Fintype.sum_prod_type]
  simp [Equiv.Perm.decomposeFin_symm_apply_zero, Fintype.card_perm, Finset.mul_sum]

/-- Polarized closure of R(D ⊗ I)R, opening both packet clasps into the
full permutation sums, with the identity on the chosen spectator. -/
def liftByClasps {n : ℕ} (K : (Fin n → Quad) → (Fin n → Quad) → ℂ)
    (x y : Fin (n+1) → Quad) : ℂ :=
  (∑ σ : Equiv.Perm (Fin (n+1)), ∑ τ : Equiv.Perm (Fin (n+1)),
    bracket (quadraticWord (x (σ 0))) (quadraticWord (y (τ 0))) *
    K ((x ∘ σ) ∘ Fin.succ) ((y ∘ τ) ∘ Fin.succ)) / (((n+1).factorial : ℂ)^2)

theorem liftByClasps_eq {n : ℕ} {K : (Fin n → Quad) → (Fin n → Quad) → ℂ} (hK : Invariant K)
    (x y : Fin (n+1) → Quad) : liftByClasps K x y = liftForm K x y := by
  have core (σ τ : Equiv.Perm (Fin (n+1))) :
      K ((x ∘ σ) ∘ Fin.succ) ((y ∘ τ) ∘ Fin.succ) =
      K (x ∘ (σ 0).succAbove) (y ∘ (τ 0).succAbove) :=
    reindexed_form hK x y σ τ 0 0
  let f (i j : Fin (n+1)) := bracket (quadraticWord (x i)) (quadraticWord (y j)) *
      K (x ∘ i.succAbove) (y ∘ j.succAbove)
  have hc (i : Fin (n+1)) := fixed_slot (f i)
  unfold liftByClasps liftForm
  simp_rw [core]
  change (∑ σ : Equiv.Perm (Fin (n+1)), ∑ τ : Equiv.Perm (Fin (n+1)), f (σ 0) (τ 0)) / _ =
    (∑ i, ∑ j, f i j) / _
  simp_rw [hc, ← Finset.mul_sum]
  rw [fixed_slot (fun i => ∑ j, f i j), Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hf, hn]
  ring

/-- The actual mixed recurrence with both occurrences of R expanded.
It holds for arbitrary choices of rational quadratics on the two boundaries. -/
theorem A_recurrence_clasps {n : ℕ} (x y : Fin (n+2) → Quad) :
    A (n+2) x y = X x y + (n+2:ℂ)^2/(n+1) * liftByClasps (A (n+1)) x y := by
  rw [liftByClasps_eq (A_invariant (n+1))]
  rfl


private def replaceFirst (t : Quad) (y : Fin 4 → Quad) : Fin 4 → Quad :=
  Fin.cons t (y ∘ Fin.succ)

private def afterExit (t : Quad) (x : Fin 4 → Quad) (i : Fin 4) : Fin 4 → Quad :=
  Fin.cons t (x ∘ i.succAbove)

private def fixHead (ρ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  Equiv.Perm.decomposeFin.symm (0,ρ)

private theorem exit_order (t : Quad) (x : Fin 4 → Quad) (σ : Equiv.Perm (Fin 4)) :
    replaceFirst t (x ∘ σ) = afterExit t x (σ 0) ∘ fixHead (remaining σ 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [replaceFirst, afterExit, fixHead]
  · simp [replaceFirst, afterExit, fixHead, remaining_eq]

private theorem single4 (f : Fin 4 → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), f (σ 0)) / 24 = (∑ i, f i) / 4 := by
  rw [fixed_slot f]
  norm_num [Nat.factorial]; ring

private theorem double4 (f : Fin 4 → Fin 4 → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), ∑ τ : Equiv.Perm (Fin 4), f (σ 0) (τ 0)) / 24^2 =
    (∑ i, ∑ j, f i j) / 16 := by
  simp_rw [fixed_slot (f _), ← Finset.mul_sum]
  rw [fixed_slot (fun i => ∑ j, f i j)]
  norm_num [Nat.factorial]; ring

/-- Polarized word evaluation of the marked operator X−A + 4 f A' f
− (3/2)(Atf + ftA). In a term containing f, the permutation sum goes
over all 24 orders at that boundary before the marked interchange. -/
def markedByClasps (x : Fin 4 → Quad) (t : Quad) : ℂ :=
  let G (a b : Quad) := bracket (quadraticWord a) (quadraticWord b)
  let mx := Fin.cons t x
  let moved := (∑ σ : Equiv.Perm (Fin 4), ∑ τ : Equiv.Perm (Fin 4), G (x (σ 0)) (x (τ 0)) *
    A 4 (replaceFirst t (x ∘ σ)) (replaceFirst t (x ∘ τ))) / 24^2
  let bra := (∑ σ : Equiv.Perm (Fin 4), G (x (σ 0)) t * A 4 (replaceFirst t (x ∘ σ)) x) / 24
  let ket := (∑ τ : Equiv.Perm (Fin 4), G t (x (τ 0)) * A 4 x (replaceFirst t (x ∘ τ))) / 24
  X mx mx - G t t * A 4 x x + 4 * moved - 3/2 * (bra + ket)

theorem markedByClasps_eq (x : Fin 4 → Quad) (t : Quad) :
    markedByClasps x t = marked x t := by
  have both (σ τ : Equiv.Perm (Fin 4)) :
      A 4 (replaceFirst t (x ∘ σ)) (replaceFirst t (x ∘ τ)) =
      A 4 (afterExit t x (σ 0)) (afterExit t x (τ 0)) := by
    rw [exit_order, exit_order, A_invariant 4]
  have left (σ : Equiv.Perm (Fin 4)) :
      A 4 (replaceFirst t (x ∘ σ)) x = A 4 (afterExit t x (σ 0)) x := by
    rw [exit_order]
    exact A_invariant 4 _ x _ 1
  have right (τ : Equiv.Perm (Fin 4)) :
      A 4 x (replaceFirst t (x ∘ τ)) = A 4 x (afterExit t x (τ 0)) := by
    rw [exit_order]
    exact A_invariant 4 x _ 1 _
  unfold markedByClasps marked
  dsimp only
  simp_rw [both, left, right]
  rw [double4 (fun i j => bracket (quadraticWord (x i)) (quadraticWord (x j)) *
      A 4 (afterExit t x i) (afterExit t x j)),
    single4 (fun i => bracket (quadraticWord (x i)) (quadraticWord t) * A 4 (afterExit t x i) x),
    single4 (fun j => bracket (quadraticWord t) (quadraticWord (x j)) * A 4 x (afterExit t x j))]
  rfl

/-- The sign persists for the full permutation-clasp evaluation, including both
crossed terms with the marked quadratic. -/
theorem negative_fifth_full_clasps :
    (markedByClasps otherFive fifthPacket).re = -565839/2000 := by
  rw [markedByClasps_eq, marked_fifth]
  norm_num

end
end BlockPermanents.MarkedWitness
