import BlockPermanents.MatchingFineAverage
import BlockPermanents.PairBound
import BlockPermanents.StraightCut

/-! # The fine bound on disjoint matchings

The principal cut can be applied repeatedly, including to an empty family.
Each matched pair of packets then supplies the two terms of Lemma 7A.1.
All energies are retained so that zero packets and unnormalized inputs are
handled directly.
-/
namespace BlockPermanents.MatchingFine
open scoped BigOperators
open Closures SchurNormalization
noncomputable section

variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]

/-- Real value of the ordinary permanent of a raw column Gram matrix. -/
def fine {d : ℕ} (f : I → Fin d → ℂ) : ℝ := (crossGram f f).permanent.re

theorem fine_eq_energy {d : ℕ} (f : I → Fin d → ℂ) : fine f = Bend.energy (packet f) := by
  rw [fine, ← packet_gram, Coarse.bracket_self, Complex.ofReal_re]

private theorem fine_nonneg {d : ℕ} (f : I → Fin d → ℂ) : 0 ≤ fine f := by
  rw [fine_eq_energy]
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem fine_reindex {d : ℕ} (e : I ≃ J) (f : J → Fin d → ℂ) :
    fine (f ∘ e) = fine f := by
  exact congrArg Complex.re (permanent_reindex e (crossGram f f))

/-- Apply the straight cut after independently choosing labels for both principal groups
and their combined set. The only Schur instance needed has their actual cardinalities. -/
theorem principal {d : ℕ} (h : HomogeneousSchur d (Fintype.card I) (Fintype.card J))
    (e : (I ⊕ J) ≃ L) (f : L → Fin d → ℂ) :
    fine (fun i => f (e (Sum.inl i))) * fine (fun j => f (e (Sum.inr j))) ≤ fine f := by
  let a := (Fintype.equivFin I).symm
  let b := (Fintype.equivFin J).symm
  let l := fun i => f (e (Sum.inl i))
  let r := fun j => f (e (Sum.inr j))
  let c := (a.sumCongr b).trans e
  have hs := StraightCut.principal_gram h (l ∘ a) (r ∘ b)
  change fine (l ∘ a) * fine (r ∘ b) ≤ fine (Sum.elim (l ∘ a) (r ∘ b)) at hs
  have he : Sum.elim (l ∘ a) (r ∘ b) = f ∘ c := by
    funext t; cases t <;> rfl
  rwa [he, fine_reindex, fine_reindex, fine_reindex] at hs

/-- Separate the first group of J columns from a sequence of equal-sized groups. -/
private def firstGroup (n : ℕ) (J : Type*) : J ⊕ (Fin n × J) ≃ Fin (n+1) × J where
  toFun := Sum.elim (fun j => (0,j)) (fun u => (u.1.succ,u.2))
  invFun := fun u => Fin.cases (Sum.inl u.2) (fun i => Sum.inr (i,u.2)) u.1
  left_inv := by intro u; cases u <;> simp
  right_inv := by
    rintro ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- Repeated straight cuts lower-bound a fine permanent by the product
of the fine permanents of the individual groups, each indexed by J. -/
theorem group_product {d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (n : ℕ) (x : Fin n → J → Fin d → ℂ) :
    ∏ i, fine (x i) ≤ fine (Function.uncurry x) := by
  induction n with
  | zero => simp [fine, Matrix.permanent_isEmpty]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have h := principal (schur _ _) (firstGroup n J) (Function.uncurry x)
    exact (mul_le_mul_of_nonneg_left (ih (fun i => x i.succ)) (fine_nonneg _)).trans h

/-- Consecutive pairs followed by the remaining m mod 2 singleton positions. -/
def labelGroups (m : ℕ) : (Fin (m/2) × Fin 2) ⊕ Fin (m%2) ≃ Fin m :=
  ((finProdFinEquiv.sumCongr (Equiv.refl (Fin (m%2)))).trans finSumFinEquiv).trans
    (finCongr (by omega))

private def thinGroups (m k : ℕ) (σ : Equiv.Perm (Fin m)) :
    (Fin (m/2) × (Fin 2 × Fin k)) ⊕ (Fin (m%2) × Fin k) ≃ Fin m × Fin k :=
  (((Equiv.prodAssoc _ _ _).symm.sumCongr (Equiv.refl _)).trans (Equiv.sumProdDistrib _ _ _).symm).trans
    (((labelGroups m).trans σ).prodCongr (Equiv.refl _))

/-- Fine estimate before averaging (the first displayed product in the proof
of Lemma 7B.3). It holds for every ordering and every unnormalized packet family. -/
theorem ordered_fine_bound {m k d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin m → Fin k → Fin d → ℂ) (σ : Equiv.Perm (Fin m)) :
    orderedWeight m ((2:ℝ)^k-1) (fun i => Bend.energy (packet (x i)))
      (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j)))) σ ≤
      fine (Function.uncurry x) := by
  let p (e : Fin (m/2)) (j : Fin 2) := x (σ (partner m e j))
  let y (t : Fin (m%2)) := x (σ (spectator m t))
  let v (i : Fin m) := Bend.energy (packet (x i))
  let g (i j : Fin m) := Complex.normSq (bracket (packet (x i)) (packet (x j)))
  let b : ℝ := 2^k-1
  let w (e : Fin (m/2)) := edgeFactor b v g (σ (partner m e 0)) (σ (partner m e 1))
  have h0 (i : Fin m) : 0 ≤ v i := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hb : 0 ≤ b := sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hw (e : Fin (m/2)) : 0 ≤ w e :=
    add_nonneg (mul_nonneg (h0 _) (h0 _)) (mul_nonneg hb (Complex.normSq_nonneg _))
  have hp (e : Fin (m/2)) : w e ≤ fine (Function.uncurry (p e)) :=
    PairBound.two_packet_lower_bound (schur k k) (p e)
  have hpairs : (∏ e, w e) ≤ fine (Function.uncurry (fun e => Function.uncurry (p e))) :=
    (Finset.prod_le_prod (fun e _ => hw e) (fun e _ => hp e)).trans (group_product schur _ _)
  have hsingle : (∏ t, v (σ (spectator m t))) ≤ fine (Function.uncurry y) := by
    simpa only [fine_eq_energy] using group_product schur (m%2) y
  have hn : 0 ≤ ∏ t, v (σ (spectator m t)) := Finset.prod_nonneg fun t _ => h0 _
  have hcut := principal (schur _ _) (thinGroups m k σ) (Function.uncurry x)
  exact (mul_le_mul hpairs hsingle hn (fine_nonneg _)).trans hcut

/-- Lemma 7B.3, with all norm factors included. The moments are uniform
over the ordered edges and unused labels. In unit norm they are the Z_r of
the manuscript. -/
theorem average_fine_bound {m k d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin m → Fin k → Fin d → ℂ) :
    ∑ r ∈ Finset.range (m/2+1), ((m/2).choose r : ℝ) * ((2:ℝ)^k-1)^r *
      Matchings.moment m r (fun i => Bend.energy (packet (x i)))
        (fun i j => Complex.normSq (bracket (packet (x i)) (packet (x j)))) ≤
        fine (Function.uncurry x) := by
  rw [← average_orderedWeight, ← Matchings.average_const m (fine (Function.uncurry x))]
  exact Matchings.average_le (ordered_fine_bound schur x)

end
end BlockPermanents.MatchingFine
