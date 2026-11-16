import BlockPermanents.FiveOuter
import BlockPermanents.FiveFreeResidual
import BlockPermanents.PairResidualSquares

/-! The positive-order cuts of the five-packet outer split and its pair remainder. -/
namespace BlockPermanents.FiveOuterSquares
open Bend Closures FiveProjection FiveMerge MatchingFine SchurNormalization
noncomputable section

/-- Every positive-order cut across the division of two arbitrary groups of atoms. -/
def properEnergy {d p q : ℕ} (l : Fin p → Fin d → ℂ) (r : Fin q → Fin d → ℂ) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : CutIndex p q), (weight p q i : ℝ) *
    energy ((wordCap d p q i).mulVec (product (packet l) (fun j => star (packet r j))))

theorem properEnergy_nonneg {d p q : ℕ} (l : Fin p → Fin d → ℂ) (r : Fin q → Fin d → ℂ) :
    0 ≤ properEnergy l r :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- Keep the complete bent Schur expansion when the two cable sizes differ. -/
theorem straight_squares {d p q : ℕ} (l : Fin p → Fin d → ℂ) (r : Fin q → Fin d → ℂ) :
    fine (Sum.elim l r) = fine l * fine r + properEnergy l r := by
  let term (i : CutIndex p q) : ℝ := (weight p q i : ℝ) *
    energy ((wordCap d p q i).mulVec (product (packet l) (fun j => star (packet r j))))
  have total := congrArg Complex.re (closed_bent_schur d p q
    (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d p q)) (packet l) (packet r))
  rw [StraightCut.fine_permanent] at total
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at total
  change fine (Sum.elim l r) = ∑ i, term i at total
  rw [← Finset.sum_erase_add Finset.univ term (Finset.mem_univ (0 : CutIndex p q))] at total
  have hz : term 0 = fine l * fine r := by
    unfold term
    have hz' : energy ((wordCap d p q 0).mulVec (product (packet l) (fun j => star (packet r j)))) = energy (packet l) * energy (packet r) :=
      StraightCut.straight_energy (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)
    rw [hz', fine_eq_energy, fine_eq_energy]
    simp [weight]
  rw [hz, add_comm] at total
  exact total

def tripleAtoms {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) :=
  Sum.elim (joined (x (σ 2)) (x (σ 1))) (x (σ 0)) ∘
    (finSumFinEquiv : Fin (k+k) ⊕ Fin k ≃ Fin (k+k+k)).symm

def outerRemainder {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) : ℝ :=
  properEnergy (tripleAtoms x σ) (joined (x (σ 3)) (x (σ 4)))

theorem outerRemainder_nonneg {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) :
    0 ≤ outerRemainder x σ := properEnergy_nonneg _ _

open private positions from BlockPermanents.FiveOuter in
/-- The labeled five-packet Gram permanent splits into the actual triple
and pair closures and all positive-order cuts between them. -/
theorem straight_outer_squares {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) :
    fine (Function.uncurry x) =
      tripleFine (packet (x (σ 1))) (packet (x (σ 2))) (packet (x (σ 0))) *
      fine (Sum.elim (x (σ 3)) (x (σ 4))) + outerRemainder x σ := by
  let a := (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).symm
  let b := (finSumFinEquiv : Fin (k+k) ⊕ Fin k ≃ Fin (k+k+k)).symm
  let pair := joined (x (σ 3)) (x (σ 4))
  let e := (b.sumCongr a).trans (((a.sumCongr (Equiv.refl _)).sumCongr (Equiv.refl _)).trans
    ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _))))
  have h : Sum.elim (tripleAtoms x σ) pair = Function.uncurry x ∘ e := by
    funext u
    rcases u with i|j
    · obtain ⟨t,rfl⟩ := b.symm.surjective i
      cases t with
      | inl j =>
        obtain ⟨v,rfl⟩ := a.symm.surjective j
        change Sum.elim (joined (x (σ 2)) (x (σ 1))) (x (σ 0)) (b (b.symm _)) =
          Function.uncurry x ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _))
            (.inl ((a.sumCongr (Equiv.refl _)) (b (b.symm _)))))
        rw [b.apply_symm_apply]
        change Sum.elim (x (σ 2)) (x (σ 1)) (a (a.symm v)) =
          Function.uncurry x ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _))
            (.inl (.inl (a (a.symm v)))))
        rw [a.apply_symm_apply]
        cases v <;> rfl
      | inr v => simp [a,b,e,tripleAtoms,positions,Equiv.sumCongr_apply]
    · obtain ⟨t,rfl⟩ := a.symm.surjective j
      change Sum.elim (x (σ 3)) (x (σ 4)) (a (a.symm t)) =
        Function.uncurry x ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _)) (.inr (a (a.symm t))))
      rw [a.apply_symm_apply]
      cases t <;> rfl
  have hp := straight_squares (tripleAtoms x σ) pair
  have ht : fine (tripleAtoms x σ) =
      tripleFine (packet (x (σ 1))) (packet (x (σ 2))) (packet (x (σ 0))) := by
    unfold tripleAtoms tripleFine
    rw [fine_reindex, triple_permanent]
    rfl
  have hpair : fine pair = fine (Sum.elim (x (σ 3)) (x (σ 4))) := fine_reindex a _
  rwa [h, fine_reindex, ht, hpair] at hp

/-- The pair contribution above the constant seven includes the unused
full-cap weight and the individual proper-cut complements. -/
def pairRemainder {d k : ℕ} (a b : Fin k → Fin d → ℂ) : ℝ :=
  (∑ r ∈ Finset.univ.erase (zeroCut k), PairResidual.residualSummand 1 a (packet b) r) +
    ((2:ℝ)^k - 8) * Complex.normSq (bracket (packet a) (packet b))

theorem pair_squares {d k : ℕ} (a b : Fin k → Fin d → ℂ)
    (ha : energy (packet a) = 1) (hb : energy (packet b) = 1) :
    fine (Sum.elim a b) = 1 + 7 * Complex.normSq (bracket (packet a) (packet b)) +
      pairRemainder a b := by
  have hs : PairResidual.scaled 1 a = packet a := funext fun _ => one_mul _
  have h := PairResidual.full_caps_residual_squares 1 a (by rwa [hs]) (Bridges.packet_symmetric _ _ b)
  rw [hs,hb] at h
  have hf := congrArg Complex.re (StraightCut.fine_permanent a b)
  rw [PairBound.product_quadratic_energy] at hf
  simp only [Complex.mul_re, Complex.natCast_re, Complex.ofReal_re, Complex.natCast_im, zero_mul, sub_zero] at hf
  unfold pairRemainder
  change _ = fine (Sum.elim a b) at hf
  rw [← hf]
  linear_combination h

theorem pairRemainder_nonneg {d k : ℕ} (hk : 3 ≤ k) (a b : Fin k → Fin d → ℂ)
    (ha : energy (packet a) = 1) : 0 ≤ pairRemainder a b := by
  have hs : PairResidual.scaled 1 a = packet a := funext fun _ => one_mul _
  have hx := PairResidual.packet_ne_zero_of_unit (a := 1) (x := a) (by rwa [hs])
  have hpow : (2:ℝ)^3 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
  exact add_nonneg (Finset.sum_nonneg fun r _ => PairResidual.summand_nonneg 1 a hx _ r)
    (mul_nonneg (by norm_num at hpow; linarith) (Complex.normSq_nonneg _))

/-- The remainder in (8B.1) for one labeling. Retain the full triple closure
as the spectator when extracting the residual of the disjoint pair. -/
def assignmentRemainder {d k : ℕ} (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) : ℝ :=
  let F := packet (x (σ 1))
  let H := packet (x (σ 2))
  let g := x (σ 0)
  let a := x (σ 3)
  let b := x (σ 4)
  outerRemainder x σ + pairRemainder a b * tripleFine F H (packet g) +
    (1 + 7 * Complex.normSq (bracket (packet a) (packet b))) * FiveFreeResidual.tripleRemainder F H g

/-- The exact triple-pair outer cut prior to the permutation average. -/
theorem outer_squares {d k : ℕ} (hk : 3 ≤ k)
    (x : Fin 5 → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1) (σ : FiveCycles.S) :
    fine (Function.uncurry x) =
      (1 + 7 * Complex.normSq (bracket (packet (x (σ 3))) (packet (x (σ 4))))) *
      ((pairGram (packet (x (σ 2))) (packet (x (σ 1))) (packet (x (σ 1)))).re +
       41/20 * Complex.normSq (pairGram (packet (x (σ 2))) (packet (x (σ 0))) (packet (x (σ 1))))) +
      assignmentRemainder x σ := by
  rw [straight_outer_squares x σ, pair_squares _ _ (hu _) (hu _)]
  dsimp only [assignmentRemainder]
  simp only [FiveFreeResidual.testing_free_cable_squares hk _ _ _ (hu (σ 2)) (hu (σ 0))]
  ring

theorem assignmentRemainder_nonneg {d k : ℕ} (hk : 3 ≤ k)
    (x : Fin 5 → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1) (σ : FiveCycles.S) :
    0 ≤ assignmentRemainder x σ := by
  have ht : 0 ≤ tripleFine (packet (x (σ 1))) (packet (x (σ 2))) (packet (x (σ 0))) := by
    rw [tripleFine, triple_permanent]
    change 0 ≤ fine _
    rw [fine_eq_energy]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  exact add_nonneg (add_nonneg (outerRemainder_nonneg x σ)
    (mul_nonneg (pairRemainder_nonneg hk _ _ (hu _)) ht))
    (mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
      (FiveFreeResidual.tripleRemainder_nonneg hk _ _ _ (hu _)))

end
end BlockPermanents.FiveOuterSquares
