import BlockPermanents.DisjointCycles
import BlockPermanents.MatchingFineSquares
import BlockPermanents.PieceProductSquares
import BlockPermanents.PieceScoreProduct

/-! Exact signed square certificate for the disjoint-cycle estimate in Appendix AC. -/
namespace BlockPermanents.DisjointCycleCertificate
open CycleClasses CycleAllocation CyclePlans CycleTen CycleMatching CyclePolynomial CycleComposition
open CycleCoefficients CycleParameters CyclePartitionSum SchurNormalization DisjointCycles
open scoped BigOperators
noncomputable section

private theorem label_eq {m : ℕ} {l : List ℕ} (hl : l ∈ partitions m) {τ : S m} :
    label τ = l ↔ τ.cycleType = nontriv l := by
  constructor
  · intro ht
    rw [← label_type, ht]
  · intro ht
    obtain ⟨hp,hs⟩ := partition_data hl
    let L := (l : Multiset ℕ)
    have filt : nontriv l = L.filter (1 < ·) := by simp [L,nontriv]
    have split : nontriv l + Multiset.replicate (l.count 1) 1 = L := by
      have h := Multiset.filter_add_not (1 < ·) L
      have hf : L.filter (fun x => ¬1<x) = L.filter (·=1) :=
        Multiset.filter_congr (fun x hx => by have := hp x hx; omega)
      rw [hf,Multiset.filter_eq',Multiset.coe_count] at h
      exact filt ▸ h
    have hm : (nontriv l).sum + l.count 1 = m := by
      simpa [L,hs] using congrArg Multiset.sum split
    have sort : l.Pairwise (· ≤ ·) := by simpa using (List.mem_filter.mp hl).2
    rw [label, Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, ht, Fintype.card_fin,
      show m - (nontriv l).sum = l.count 1 by omega, split, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ sort

/-- The entire permutation fiber of a partition has its exact centralizer
multiplicity, including the fixed labels. -/
theorem class_card {m : ℕ} {l : List ℕ} (hl : l ∈ partitions m) :
    (Finset.univ.filter (fun τ : S m => label τ = l)).card = classSize m l := by
  have eqn : Finset.univ.filter (fun τ : S m => label τ = l) =
      Finset.univ.filter (fun τ : S m => τ.cycleType = nontriv l) := by
    ext τ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,label_eq hl]
  rw [eqn, Equiv.Perm.card_of_cycleType, Fintype.card_fin, ← class_count hl]
  rfl

private theorem sum_partitions {m : ℕ} (g : Gram m) (c : List ℕ → ℕ → ℝ)
    (R : List ℕ → ℝ)
    (bound : ∀ l ∈ partitions m, ∀ τ : S m, τ.cycleType = nontriv l →
      (∑ j ∈ Finset.range (m/2+1), c l j * Z g j) - (mean g τ).re = R l) :
    (∑ j ∈ Finset.range (m/2+1), totals m c j * Z g j) - (Matrix.permanent g).re =
      ∑ l ∈ (partitions m).toFinset, (classSize m l : ℝ) * R l := by
  classical
  let T := (partitions m).toFinset
  let P := fun l => ∑ j ∈ Finset.range (m/2+1), c l j * Z g j
  have cover (τ : S m) (_ : τ ∈ Finset.univ) : label τ ∈ T := List.mem_toFinset.mpr (label_mem τ)
  have lhs : (∑ j ∈ Finset.range (m/2+1), totals m c j * Z g j) =
      ∑ l ∈ T, (classSize m l : ℝ) * P l := by
    simp only [P,totals,T,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm
  rw [lhs, permanent_sum, ← Finset.sum_fiberwise_of_maps_to cover, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := List.mem_toFinset.mp hl
  let F := Finset.univ.filter (fun τ : S m => label τ = l)
  have h (τ : S m) (ht : τ ∈ F) : (mean g τ).re = P l - R l := by
    have hb := bound l hl' τ ((label_eq hl').mp (Finset.mem_filter.mp ht).2)
    dsimp [P]
    linarith
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  change _ - (F.card : ℝ) * _ = _
  rw [show F.card = classSize m l from class_card hl']
  ring

open Closures

/-- Negative-sign half-web energy of a cycle plan on the given ambient packets.
The partition sum only uses plans whose sizes equal the number of packets. -/
def planEnergy {I : Type*} [Fintype I] {m : ℕ} (p : List Piece) (u : ℕ → ℝ)
    (x : Fin m → I → ℂ) : ℝ :=
  if h : planSize p = m then PieceProductSquares.energy p u (fun i => x (Fin.cast h i)) false
  else 0

theorem planEnergy_nonneg {I : Type*} [Fintype I] {m : ℕ} (p : List Piece) (u : ℕ → ℝ)
    (hu : ∀ i, 0 < u i) (x : Fin m → I → ℂ) : 0 ≤ planEnergy p u x := by
  unfold planEnergy
  split
  · exact PieceProductSquares.energy_nonneg p u hu _ false
  · rfl

private theorem class_gap {I : Type*} [Fintype I] {m : ℕ}
    (p : List Piece) (hp : planSize p = m) (u : ℕ → ℝ) (hu : ∀ i, 0 < u i)
    (x : Fin m → I → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (τ : S m) (hτ : τ.cycleType = (planParts p : Multiset ℕ)) :
    (∑ j ∈ Finset.range (m/2+1), pcoeff p u j * Z (crossGram x x) j) -
      (mean (crossGram x x) τ).re = planEnergy p u x := by
  subst m
  rw [← PieceScoreProduct.score_eq_sum]
  have hs := PieceProductSquares.class_squares p u hu τ hτ x unit false
  simpa [planEnergy,ReflectedCycles.sign,sub_eq_add_neg] using hs

/-- Lemma AC.1 as an exact sum of class remainders. Each partition contributes
its centralizer multiplicity times the reflected energy of its disjoint cycle plan. -/
theorem certificate {I : Type*} [Fintype I] {m : ℕ} (u : List ℕ → ℕ → ℝ)
    (hu : ∀ l ∈ partitions m, ∀ i, 0 < u l i)
    (x : Fin m → I → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) :
    (∑ j ∈ Finset.range (m/2+1), D m u j * Z (crossGram x x) j) -
      (crossGram x x).permanent.re =
      ∑ l ∈ (partitions m).toFinset, (classSize m l : ℝ) * planEnergy (plan l) (u l) x := by
  apply sum_partitions
  intro l hl τ hτ
  obtain ⟨hpos,hs⟩ := partition_data hl
  obtain ⟨hn,ht⟩ := plan_data l hpos
  exact class_gap (plan l) (hn.trans hs) (u l) (hu l hl) x unit τ (hτ.trans ht.symm)

/-- Fine minus coarse is the sum of the fine clasp remainder, the disjoint-cycle
remainders, and the surplus between the fine and coarse matching coefficients. -/
theorem matrix_gap {m k d : ℕ} (u : List ℕ → ℕ → ℝ)
    (hu : ∀ l ∈ partitions m, ∀ i, 0 < u l i)
    (x : Fin m → Fin k → Fin d → ℂ) (unit : ∀ i, Bend.energy (packet (x i)) = 1) :
    let y := fun i => packet (x i)
    MatchingFine.fine (Function.uncurry x) - (crossGram y y).permanent.re =
      Matchings.average m (MatchingFineSquares.orderedRemainder x) +
      (∑ l ∈ (partitions m).toFinset, (classSize m l : ℝ) * planEnergy (plan l) (u l) y) +
      ∑ j ∈ Finset.range (m/2+1),
        (((m/2).choose j : ℝ) * ((2:ℝ)^k-1)^j - D m u j) * Z (crossGram y y) j := by
  let y := fun i => packet (x i)
  let g := crossGram y y
  have hf := MatchingFineSquares.unit_identity x unit
  change MatchingFine.fine (Function.uncurry x) =
    (∑ j ∈ Finset.range (m/2+1), ((m/2).choose j : ℝ) * ((2:ℝ)^k-1)^j * Z g j) + _ at hf
  have hc := certificate u hu y unit
  dsimp only
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  linarith only [hf,hc]

/-- The numerical coefficient criterion in AC.1 implies the inequality for
every complex positive semidefinite input of this block size and thickness. -/
theorem marcus {m k : ℕ} (hk : 0 < k) (u : List ℕ → ℕ → ℝ)
    (hu : ∀ l ∈ partitions m, ∀ i, 0 < u l i)
    (fit : ∀ j ∈ Finset.range (m/2+1), D m u j ≤ ((m/2).choose j : ℝ)*((2:ℝ)^k-1)^j) :
    MarcusAt m k := by
  apply MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit hk ?_)
  intro x unit
  apply sub_nonneg.mp
  rw [matrix_gap u hu x unit]
  apply add_nonneg (add_nonneg (MatchingFineSquares.averageRemainder_nonneg _) ?_) ?_
  · apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (by positivity) (planEnergy_nonneg _ _ (hu l (List.mem_toFinset.mp hl)) _)
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (sub_nonneg.mpr (fit j hj)) (Z_nonneg _ _)

end
end BlockPermanents.DisjointCycleCertificate
