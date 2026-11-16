import BlockPermanents.FiveOuterSquares
import BlockPermanents.MatchingFine

/-! # The exact matching remainder of Lemma 7B.3

Each group split contributes its positive-order Schur cuts. At the matched
leaves the trace-cup projection retains the binomial full-cap term. The
remaining squared components telescope through the ordered product.
-/

namespace BlockPermanents.MatchingFineSquares
open Bend Closures MatchingFine PairResidual SchurNormalization
open scoped BigOperators Matrix
noncomputable section

/-- The squared trace-cup complement and the binomial rank surplus, summed
over the nonzero cuts of a matched pair. A zero first packet has zero cuts. -/
def pairSurplus {k d : ℕ} (x y : Fin k → Fin d → ℂ) : ℝ := by
  classical
  exact if packet x = 0 then 0 else
    ∑ r ∈ Finset.univ.erase (zeroCut k), residualSummand 1 x (packet y) r

theorem pairSurplus_nonneg {k d : ℕ} (x y : Fin k → Fin d → ℂ) :
    0 ≤ pairSurplus x y := by
  classical
  unfold pairSurplus
  split_ifs with hx
  · rfl
  · exact Finset.sum_nonneg fun r _ => summand_nonneg 1 x hx _ r

open private choose_sum_nonzero from BlockPermanents.PairBound in
theorem pair_identity {k d : ℕ} (x : Fin 2 → Fin k → Fin d → ℂ) :
    fine (Function.uncurry x) =
      energy (packet (x 0)) * energy (packet (x 1)) +
        ((2:ℝ)^k-1) * Complex.normSq (bracket (packet (x 0)) (packet (x 1))) +
        pairSurplus (x 0) (x 1) := by
  classical
  have total := congrArg Complex.re (closed_bent_schur d k k
    (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d k k))
    (packet (x 0)) (packet (x 1)))
  rw [Bridges.two_fine_permanent x] at total
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at total
  change fine (Function.uncurry x) = ∑ r, cutTerm (packet (x 0)) (packet (x 1)) r at total
  have straight : cutTerm (packet (x 0)) (packet (x 1)) (zeroCut k) =
      energy (packet (x 0)) * energy (packet (x 1)) := by
    rw [cutTerm, zero_cap_energy (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)]
    simp [weight, zeroCut]
  rw [total, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (zeroCut k)), straight]
  by_cases hx : packet (x 0) = 0
  · have hp : product (0 : Word d k → ℂ) (fun j => star (packet (x 1) j)) = 0 := by
      ext; simp [product]
    simp only [hx, cutTerm, hp, Matrix.mulVec_zero]
    simp [pairSurplus, hx, bracket, energy]
  · have hu : scaled 1 (x 0) = packet (x 0) := by ext; simp [scaled]
    have split (r : CutIndex k k) : cutTerm (packet (x 0)) (packet (x 1)) r =
        residualSummand 1 (x 0) (packet (x 1)) r +
          (k.choose r : ℝ) * Complex.normSq (bracket (packet (x 0)) (packet (x 1))) := by
      have h := cut_resolution 1 (x 0) (Bridges.packet_symmetric d k (x 1)) r (rank_pos _ hx r)
      rw [hu] at h
      rw [h, residualSummand, hu]
      ring
    simp_rw [split]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, choose_sum_nonzero]
    simp only [pairSurplus, if_neg hx]
    ring

variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]

/-- The positive-order cuts between two labeled sets of raw columns. -/
def principalRemainder {d : ℕ} (e : I ⊕ J ≃ L) (f : L → Fin d → ℂ) : ℝ :=
  FiveOuterSquares.properEnergy
    ((fun i => f (e (.inl i))) ∘ (Fintype.equivFin I).symm)
    ((fun j => f (e (.inr j))) ∘ (Fintype.equivFin J).symm)

omit [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq L] in
theorem principalRemainder_nonneg {d : ℕ} (e : I ⊕ J ≃ L) (f : L → Fin d → ℂ) :
    0 ≤ principalRemainder e f := FiveOuterSquares.properEnergy_nonneg _ _

theorem principal_identity {d : ℕ} (e : I ⊕ J ≃ L) (f : L → Fin d → ℂ) :
    fine f = fine (fun i => f (e (.inl i))) * fine (fun j => f (e (.inr j))) +
      principalRemainder e f := by
  let a := (Fintype.equivFin I).symm
  let b := (Fintype.equivFin J).symm
  let l := fun i => f (e (.inl i))
  let r := fun j => f (e (.inr j))
  let c := (a.sumCongr b).trans e
  have hs := FiveOuterSquares.straight_squares (l ∘ a) (r ∘ b)
  have he : Sum.elim (l ∘ a) (r ∘ b) = f ∘ c := by
    funext t; cases t <;> rfl
  rwa [he, fine_reindex, fine_reindex, fine_reindex] at hs

open private firstGroup thinGroups fine_nonneg from BlockPermanents.MatchingFine

/-- Product telescoping through the group cuts. At each step the discarded
leaf squares multiply the entire remaining fine closure, and the retained
leaf factor multiplies the remaining group's squares. -/
def groupRemainder {d : ℕ} :
    (n : ℕ) → (Fin n → J → Fin d → ℂ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | 0, _, _, _ => 0
  | n+1, x, w, s =>
    principalRemainder (firstGroup n J) (Function.uncurry x) +
      s 0 * fine (Function.uncurry (fun i : Fin n => x i.succ)) +
      w 0 * groupRemainder n (fun i => x i.succ) (fun i => w i.succ) (fun i => s i.succ)

theorem group_identity {d : ℕ} (n : ℕ) (x : Fin n → J → Fin d → ℂ)
    (w s : Fin n → ℝ) (h : ∀ i, fine (x i) = w i + s i) :
    fine (Function.uncurry x) = (∏ i, w i) + groupRemainder n x w s := by
  induction n with
  | zero => simp [fine, Matrix.permanent_isEmpty, groupRemainder]
  | succ n ih =>
    have p := principal_identity (firstGroup n J) (Function.uncurry x)
    change fine (Function.uncurry x) = fine (x 0) * fine (Function.uncurry
      (fun i : Fin n => x i.succ)) + principalRemainder _ _ at p
    rw [groupRemainder, Fin.prod_univ_succ, p, h 0,
      ih (fun i => x i.succ) (fun i => w i.succ) (fun i => s i.succ) (fun i => h i.succ)]
    ring

theorem groupRemainder_nonneg {d : ℕ} (n : ℕ) (x : Fin n → J → Fin d → ℂ)
    (w s : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, 0 ≤ s i) :
    0 ≤ groupRemainder n x w s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact add_nonneg (add_nonneg (principalRemainder_nonneg _ _)
      (mul_nonneg (hs 0) (fine_nonneg _))) (mul_nonneg (hw 0)
        (ih _ _ _ (fun i => hw i.succ) (fun i => hs i.succ)))

variable {m k d : ℕ}

/-- The physical factors of each matched leaf. -/
def pairAtoms (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m))
    (e : Fin (m/2)) (j : Fin 2) := x (σ (partner m e j))

def spectatorAtoms (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m))
    (t : Fin (m%2)) := x (σ (spectator m t))

def leafWeight (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m)) (e : Fin (m/2)) : ℝ :=
  let p := pairAtoms x σ e
  energy (packet (p 0)) * energy (packet (p 1)) +
    ((2:ℝ)^k-1) * Complex.normSq (bracket (packet (p 0)) (packet (p 1)))

private theorem leafWeight_nonneg (x : Fin m → Fin k → Fin d → ℂ)
    (σ : Equiv.Perm (Fin m)) (e : Fin (m/2)) : 0 ≤ leafWeight x σ e :=
  add_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
    (mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) (Complex.normSq_nonneg _))

/-- Ordered squared remainder, including the split between the matched
pairs and possible spectator, the cuts among the groups, and the pair
trace-cup complements and rank surpluses. -/
def orderedRemainder (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m)) : ℝ :=
  let p := pairAtoms x σ
  let y := spectatorAtoms x σ
  let w := leafWeight x σ
  principalRemainder (thinGroups m k σ) (Function.uncurry x) +
    groupRemainder (m/2) (fun e => Function.uncurry (p e)) w
      (fun e => pairSurplus (p e 0) (p e 1)) * fine (Function.uncurry y) +
    (∏ e, w e) * groupRemainder (m%2) y (fun t => energy (packet (y t))) (fun _ => 0)

theorem orderedRemainder_nonneg (x : Fin m → Fin k → Fin d → ℂ)
    (σ : Equiv.Perm (Fin m)) : 0 ≤ orderedRemainder x σ :=
  add_nonneg (add_nonneg (principalRemainder_nonneg _ _)
    (mul_nonneg (groupRemainder_nonneg _ _ _ _ (leafWeight_nonneg x σ) (fun _ => pairSurplus_nonneg _ _))
      (fine_nonneg _)))
    (mul_nonneg (Finset.prod_nonneg (fun e _ => leafWeight_nonneg x σ e))
      (groupRemainder_nonneg _ _ _ _ (fun _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        (fun _ => le_rfl)))

theorem ordered_identity (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m)) :
    fine (Function.uncurry x) =
      orderedWeight m ((2:ℝ)^k-1) (fun i => energy (packet (x i)))
        (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j)))) σ +
        orderedRemainder x σ := by
  let p := pairAtoms x σ
  let y := spectatorAtoms x σ
  let w := leafWeight x σ
  let s := fun e => pairSurplus (p e 0) (p e 1)
  let v := fun t => energy (packet (y t))
  have hp := group_identity (m/2) (fun e => Function.uncurry (p e)) w s
    (fun e => pair_identity (p e))
  have hy := group_identity (m%2) y v (fun _ => 0) (fun t => by simp [v, fine_eq_energy])
  have h := principal_identity (thinGroups m k σ) (Function.uncurry x)
  change fine (Function.uncurry x) = fine (Function.uncurry (fun e => Function.uncurry (p e))) *
    fine (Function.uncurry y) + principalRemainder _ _ at h
  change fine (Function.uncurry x) = (∏ e, w e) * (∏ t, v t) +
    (principalRemainder _ _ + groupRemainder _ _ w s * fine (Function.uncurry y) +
      (∏ e, w e) * groupRemainder _ y v (fun _ => 0))
  rw [h, hp, hy]
  ring

theorem ordered_bound (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m)) :
    orderedWeight m ((2:ℝ)^k-1) (fun i => energy (packet (x i)))
      (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j)))) σ ≤
      fine (Function.uncurry x) := by
  rw [ordered_identity x σ]
  exact le_add_of_nonneg_right (orderedRemainder_nonneg x σ)

/-- Exact normalized permutation average with the matching coefficients of (7B.4).
Packet energies on unused labels are kept, including for a zero packet. -/
theorem average_identity (x : Fin m → Fin k → Fin d → ℂ) :
    fine (Function.uncurry x) =
      (∑ r ∈ Finset.range (m/2+1), ((m/2).choose r : ℝ) * ((2:ℝ)^k-1)^r *
        Matchings.moment m r (fun i => energy (packet (x i)))
          (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j))))) +
      Matchings.average m (orderedRemainder x) := by
  let W := orderedWeight m ((2:ℝ)^k-1) (fun i => energy (packet (x i)))
    (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j))))
  have h : (fun _ : Equiv.Perm (Fin m) => fine (Function.uncurry x)) =
      fun σ => W σ + orderedRemainder x σ := funext (ordered_identity x)
  rw [← average_orderedWeight, ← Matchings.average_add, ← h, Matchings.average_const]

theorem averageRemainder_nonneg (x : Fin m → Fin k → Fin d → ℂ) :
    0 ≤ Matchings.average m (orderedRemainder x) := by
  rw [← Matchings.average_const m 0]
  exact Matchings.average_le (orderedRemainder_nonneg x)

theorem average_bound (x : Fin m → Fin k → Fin d → ℂ) :
    ∑ r ∈ Finset.range (m/2+1), ((m/2).choose r : ℝ) * ((2:ℝ)^k-1)^r *
      Matchings.moment m r (fun i => energy (packet (x i)))
        (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j)))) ≤
        fine (Function.uncurry x) := by
  rw [average_identity x]
  exact le_add_of_nonneg_right (averageRemainder_nonneg x)

/-- The normalized case with unit weights on unmatched labels. -/
theorem unit_identity (x : Fin m → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1) :
    fine (Function.uncurry x) =
      (∑ r ∈ Finset.range (m/2+1), ((m/2).choose r : ℝ) * ((2:ℝ)^k-1)^r *
        Matchings.moment m r (fun _ => 1)
          (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j))))) +
      Matchings.average m (orderedRemainder x) := by
  simpa only [hu] using average_identity x

end
end BlockPermanents.MatchingFineSquares
