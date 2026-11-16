import BlockPermanents.MatchingCoarse
import BlockPermanents.MatchingFine

/-! # Straightening the surviving four-face

For the fixed mark and two different exits in slots 0,1,2, their difference
is the symmetric packet on one vector D and all the unchanged spectators.
The two face inequalities are principal cuts on that genuine Gram permanent.
-/
namespace BlockPermanents.FaceExit
open Closures MatchingCoarse MatchingFine SchurNormalization
noncomputable section

variable {T : Type*}

/-- Multilinearity at the surviving slot of a symmetric packet. -/
theorem packet_cons_difference {n : ℕ} (a b : ℂ) (u v : T → ℂ) (y : Fin n → T → ℂ) :
    packet (Fin.cons (fun t => a*u t - b*v t) y) =
      fun w => a*packet (Fin.cons u y) w - b*packet (Fin.cons v y) w := by
  funext w
  unfold packet orderSum
  simp_rw [← pure_reindex, pureWord, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Keep the three distinguished labels first. -/
def marked {n : ℕ} (A B C : T → ℂ) (y : Fin n → T → ℂ) : Fin (n+3) → T → ℂ :=
  Fin.cons A (Fin.cons B (Fin.cons C y))

variable [Fintype T]

/-- The unsymmetrized survivor in Appendix A.1. -/
def survivor (A B C : T → ℂ) : T → ℂ :=
  fun t => bracket A B * C t - bracket A C * B t

/-- The signed exit difference is a single ordinary packet with first
column D. The equality includes its factorial normalization. -/
theorem exit_difference {n : ℕ} (A B C : T → ℂ) (y : Fin n → T → ℂ) :
    (fun w => exit (marked A B C y) 0 w -
      exit (marked A B C y) (0 : Fin (n+1)).succ w) =
      packet (Fin.cons (survivor A B C) y) := by
  have h₁ : remainder (marked A B C y) 0 = Fin.cons C y := by
    funext j
    exact Fin.cases (by simp only [remainder, omitSlot, marked, Equiv.swap_self, Equiv.Perm.one_apply, Equiv.refl_apply, Fin.cons_succ, Fin.cons_zero])
      (fun i => by simp [remainder, omitSlot, marked]) j
  have h₂ : remainder (marked A B C y) (0 : Fin (n+1)).succ = Fin.cons B y := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [remainder, omitSlot, marked]
    · have he : Equiv.swap (0 : Fin (n+2)) (0 : Fin (n+1)).succ i.succ.succ = i.succ.succ :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
          intro he
          exact Fin.succ_ne_zero i (Fin.succ_injective _ he))
      simp only [remainder, omitSlot, he, marked, Fin.cons_succ]
  unfold survivor
  rw [packet_cons_difference]
  simp only [exit, h₁, h₂]
  simp only [marked, Fin.cons_succ, Fin.cons_zero]

private theorem singleton {d : ℕ} (x : Fin 1 → Fin d → ℂ) :
    fine x = Bend.energy (x 0) := by simp [fine, crossGram, Coarse.bracket_self]

/-- Straight cuts down to singleton unit vectors. -/
theorem unit_permanent {n d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin n → Fin d → ℂ) (hu : ∀ i, Bend.energy (x i) = 1) : 1 ≤ fine x := by
  let z : Fin n → Fin 1 → Fin d → ℂ := fun i _ => x i
  let e := Equiv.prodUnique (Fin n) (Fin 1)
  have h := group_product schur n z
  have h₁ (i) : fine (z i) = 1 := (singleton _).trans (hu _)
  have he : Function.uncurry z = x ∘ e := rfl
  simpa only [h₁, Finset.prod_const_one, he, fine_reindex] using h

/-- Keep an arbitrary prescribed subfamily while removing unit spectators. -/
theorem keep {p n d : ℕ} (schur : ∀ a b, HomogeneousSchur d a b)
    (x : Fin (p+n) → Fin d → ℂ) (hu : ∀ i, Bend.energy (x (Fin.natAdd p i)) = 1) :
    fine (fun i : Fin p => x (Fin.castAdd n i)) ≤ fine x := by
  have h := principal (schur _ _) finSumFinEquiv x
  have hr := unit_permanent schur (fun i : Fin n => x (Fin.natAdd p i)) hu
  have hn : 0 ≤ fine (fun i : Fin p => x (Fin.castAdd n i)) := by
    rw [fine_eq_energy]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  change fine (fun i : Fin p => x (Fin.castAdd n i)) *
    fine (fun i : Fin n => x (Fin.natAdd p i)) ≤ fine x at h
  exact (le_mul_of_one_le_right hn hr).trans h

/-- The canonical fixed-mark squared difference, before averaging labels. -/
def exitEnergy {d n : ℕ} (A B C : Fin d → ℂ) (y : Fin n → Fin d → ℂ) : ℝ :=
  Bend.energy fun w => exit (marked A B C y) 0 w -
    exit (marked A B C y) (0 : Fin (n+1)).succ w

theorem exitEnergy_eq {d n : ℕ} (A B C : Fin d → ℂ) (y : Fin n → Fin d → ℂ) :
    exitEnergy A B C y = fine (Fin.cons (survivor A B C) y) := by
  rw [exitEnergy, exit_difference, fine_eq_energy]

/-- The triple-face bound on the squared exit, before summing over marks. -/
theorem keep_three {n d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (A B C : Fin d → ℂ) (y : Fin n → Fin d → ℂ) (hu : ∀ i, Bend.energy (y i) = 1) :
    Bend.energy (survivor A B C) ≤ exitEnergy A B C y := by
  let V := survivor A B C
  let e : Fin 1 ⊕ Fin n ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
  have hi (i : Fin n) : e (.inr i) = i.succ := by apply Fin.ext; simp [e,finCongr]
  have h := principal (schur _ _) e (Fin.cons V y)
  simp only [singleton, show e (.inl 0) = 0 from rfl, hi, Fin.cons_zero, Fin.cons_succ] at h
  have hn : 0 ≤ Bend.energy V := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [exitEnergy_eq]
  exact (le_mul_of_one_le_right hn (unit_permanent schur y hu)).trans h

/-- Keep a fourth label while cutting all remaining unit spectators. -/
theorem keep_four {n d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (A B C H : Fin d → ℂ) (y : Fin n → Fin d → ℂ) (hu : ∀ i, Bend.energy (y i) = 1) :
    fine ![survivor A B C,H] ≤ exitEnergy A B C (Fin.cons H y) := by
  let V := survivor A B C
  let e : Fin 2 ⊕ Fin n ≃ Fin (n+2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 n))
  have hi (i : Fin n) : e (.inr i) = i.succ.succ := by apply Fin.ext; simp [e,finCongr]
  have hl : (fun j : Fin 2 => (Fin.cons V (Fin.cons H y) : Fin (n+2) → Fin d → ℂ) (e (.inl j))) = ![V,H] := by
    funext j
    fin_cases j
    · change (Fin.cons V (Fin.cons H y) : Fin (n+2) → Fin d → ℂ) 0 = V
      rw [Fin.cons_zero]
    · change (Fin.cons V (Fin.cons H y) : Fin (n+2) → Fin d → ℂ) (0 : Fin (n+1)).succ = H
      rw [Fin.cons_succ, Fin.cons_zero]
  have h := principal (schur _ _) e (Fin.cons V (Fin.cons H y))
  rw [hl] at h
  simp only [hi, Fin.cons_succ] at h
  have hn : 0 ≤ fine ![V,H] := by
    rw [fine_eq_energy]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [exitEnergy_eq]
  exact (le_mul_of_one_le_right hn (unit_permanent schur y hu)).trans h

end
end BlockPermanents.FaceExit
