import BlockPermanents.MatchingWeight
import BlockPermanents.Matchings
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset

/-! # Expanding the fine closure on maximum matchings

Choose which of the disjoint pairs is capped, retain the other endpoints
as straight strands and average over the labels.
-/
namespace BlockPermanents.MatchingFine
open scoped BigOperators
noncomputable section

private def maxSlots (m : ℕ) : ((Fin (m/2) × Fin 2) ⊕ Fin (m%2)) ≃ Fin m :=
  ((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by omega))

private lemma maxLeft (m : ℕ) (a : Fin (m/2)) (j : Fin 2) :
    maxSlots m (Sum.inl (a,j)) = partner m a j := by
  apply Fin.ext
  simp [maxSlots, partner, finProdFinEquiv, Nat.mul_comm]

private lemma maxRight (m : ℕ) (t : Fin (m%2)) :
    maxSlots m (Sum.inr t) = spectator m t := by
  apply Fin.ext
  simp [maxSlots, spectator]

private abbrev unmatched {m : ℕ} (u : Finset (Fin (m/2))) :=
  ({a : Fin (m/2) // a ∉ u} × Fin 2) ⊕ Fin (m%2)

/-- Recode each unselected pair as its two separate, labeled ends. -/
private def selectSlots (m : ℕ) (u : Finset (Fin (m/2))) :
    ((u × Fin 2) ⊕ unmatched u) ≃ Fin m :=
  (Equiv.sumAssoc _ _ _).symm.trans <|
    (((Equiv.sumProdDistrib _ _ _).symm.trans
      ((Equiv.sumCompl (fun i => i ∈ u)).prodCongr (Equiv.refl _))).sumCongr (Equiv.refl _)).trans (maxSlots m)

private theorem selectCap (m : ℕ) (u : Finset (Fin (m/2))) (a : u) (j : Fin 2) :
    selectSlots m u (Sum.inl (a,j)) = partner m a j := maxLeft m a j
private theorem selectStraight (m : ℕ) (u : Finset (Fin (m/2)))
    (a : {i : Fin (m/2) // i ∉ u}) (j : Fin 2) :
    selectSlots m u (Sum.inr (Sum.inl (a,j))) = partner m a j := maxLeft m a j
private theorem selectSpectator (m : ℕ) (u : Finset (Fin (m/2))) (t : Fin (m%2)) :
    selectSlots m u (Sum.inr (Sum.inr t)) = spectator m t := maxRight m t

private def term (m : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (u : Finset (Fin (m/2))) :=
  (∏ i ∈ u, p (σ (partner m i 0)) (σ (partner m i 1))) *
  (∏ i ∈ Finset.univ \ u, v (σ (partner m i 0)) * v (σ (partner m i 1))) *
  ∏ j : Fin (m%2), v (σ (spectator m j))

private theorem expandWeight (m : ℕ) (b : ℝ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) : orderedWeight m b v p σ =
    ∑ u ∈ Finset.univ.powerset, b^u.card * term m v p σ u := by
  unfold orderedWeight edgeFactor
  simp_rw [add_comm (v _ * v _) (b * _)]
  rw [Finset.prod_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, term]
  ring

private theorem byCard {n : ℕ} (f : ℕ → ℝ) :
    (∑ u ∈ (Finset.univ : Finset (Fin n)).powerset, f u.card) =
    ∑ r ∈ Finset.range (n+1), (n.choose r : ℝ) * f r := by
  classical
  have h (u : Finset (Fin n)) (_ : u ∈ Finset.univ.powerset) : u.card ∈ Finset.range (n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using u.card_le_univ))
  rw [← Finset.sum_fiberwise_of_maps_to h]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.powersetCard_eq_filter]
  calc
    _ = ∑ u ∈ (Finset.univ : Finset (Fin n)).powersetCard r, f r := by
      apply Finset.sum_congr rfl
      intro u hu; rw [(Finset.mem_powersetCard.mp hu).2]
    _ = _ := by simp

private theorem term_eq_weight (m : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (u : Finset (Fin (m/2))) :
    term m v p σ u = Matchings.weight v p (σ ∘ selectSlots m u) := by
  unfold term Matchings.weight
  simp only [Function.comp_apply, selectCap, Finset.prod_coe_sort, Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fin.prod_univ_two, selectStraight, selectSpectator]
  rw [Finset.prod_subtype (p := fun i => i ∉ u) (Finset.univ \ u) (by simp),
    Finset.prod_subtype (p := fun i => i ∈ u) u (fun _ => Iff.rfl)]
  ring

/-- The averaged product of the maximum-matching pair bounds, including
the straight factor for an odd number of labels. Each degree has precisely
`(m/2).choose r` admissible subsets in a fixed maximum matching. -/
theorem average_orderedWeight (m : ℕ) (b : ℝ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) :
    Matchings.average m (orderedWeight m b v p) =
      ∑ r ∈ Finset.range (m/2+1), ((m/2).choose r : ℝ) * b^r * Matchings.moment m r v p := by
  classical
  have h (u : Finset (Fin (m/2))) : Matchings.average m (fun σ => term m v p σ u) =
      Matchings.moment m u.card v p := by
    simp_rw [term_eq_weight]
    exact Matchings.average_weight_eq_moment v p (selectSlots m u) (by simp)
  calc
    Matchings.average m (orderedWeight m b v p) =
        ∑ u ∈ Finset.univ.powerset, b^u.card * Matchings.average m (fun σ => term m v p σ u) := by
      unfold Matchings.average
      simp_rw [expandWeight]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.mul_sum]; ring
    _ = _ := by simp_rw [h]; simpa [mul_assoc] using byCard (n := m/2) (fun r => b^r * Matchings.moment m r v p)


end
end BlockPermanents.MatchingFine
