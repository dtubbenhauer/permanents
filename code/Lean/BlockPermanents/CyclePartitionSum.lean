import BlockPermanents.CycleAllocation
import BlockPermanents.CycleUnbounded
import BlockPermanents.TenEndpoint

/-! # Grouping the disjoint-cycle estimates for an arbitrary number of packets -/
namespace BlockPermanents.CyclePartitionSum
open CycleTen CycleCoefficients CycleMatching CycleComposition CyclePlans CyclePolynomial
open CycleClasses CycleAllocation Closures Bend SchurNormalization
open scoped BigOperators
noncomputable section

/-- One representative of each partition, with fixed labels distributed among its odd cycles. -/
theorem realizes {m : ℕ} {l : List ℕ} (hl : l ∈ partitions m) :
    Realizes m (l.filter (· > 1)) (planPolynomial (plan l)) := by
  obtain ⟨hp,hs⟩ := partition_data hl
  obtain ⟨hn,ht⟩ := plan_data l hp
  rw [hs] at hn
  obtain ⟨τ,hτ,hb⟩ := CycleUnbounded.plan_realizes (plan l)
  rw [ht] at hτ
  rw [← hn]
  exact ⟨τ,hτ,hb⟩

/-- Appendix A with the positive half-integer choices, for every partition and label count. -/
theorem canonical_bound {m : ℕ} (g : Gram m) (hg : UnitGram g) :
    (Matrix.permanent g).re ≤ ((partitions m).map (fun l =>
      (classSize m l : ℝ) * evaluate g (planPolynomial (plan l)))).sum :=
  partition_bound g hg (fun _ => realizes) (fun _ => class_count) (partitions_nodup m)

private theorem multiplicity {m} (l : List ℕ) (hl : l ∈ partitions m) :
    (Finset.univ.filter (fun τ : S m => label τ = l)).card ≤ classSize m l := by
  calc
    _ ≤ (Finset.univ.filter (fun τ : S m => τ.cycleType = nontriv l)).card := by
      apply Finset.card_le_card
      intro τ ht
      obtain ⟨_,ht⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht ▸ (label_type τ).symm⟩
    _ = _ := by
      rw [Equiv.Perm.card_of_cycleType,Fintype.card_fin,← class_count hl]
      rfl

/-- The degree-j global coefficient adds the class multiplicities times their local coefficients. -/
def totals (m : ℕ) (c : List ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ (partitions m).toFinset, (classSize m l : ℝ) * c l j

theorem sum_classes {m : ℕ} (g : Gram m) (c : List ℕ → ℕ → ℝ)
    (bound : ∀ l ∈ partitions m, ∀ τ : S m, τ.cycleType=nontriv l →
      |(mean g τ).re| ≤ ∑ j ∈ Finset.range (m/2+1), c l j * Z g j) :
    (Matrix.permanent g).re ≤ ∑ j ∈ Finset.range (m/2+1), totals m c j * Z g j := by
  let T := (partitions m).toFinset
  have cover (τ : S m) (_ : τ ∈ Finset.univ) : label τ ∈ T := List.mem_toFinset.mpr (label_mem τ)
  rw [permanent_sum, ← Finset.sum_fiberwise_of_maps_to cover]
  calc
    _ ≤ ∑ l ∈ T,(classSize m l:ℝ) * ∑ j ∈ Finset.range (m/2+1),c l j * Z g j := by
      apply Finset.sum_le_sum
      intro l hl
      have hl' := List.mem_toFinset.mp hl
      let F := Finset.univ.filter (fun τ : S m => label τ=l)
      let v := ∑ j ∈ Finset.range (m/2+1),c l j * Z g j
      have hb (τ : S m) (ht : τ ∈ F) : (mean g τ).re ≤ v := by
        have h := (Finset.mem_filter.mp ht).2
        exact (le_abs_self _).trans (bound l hl' τ (h ▸ (label_type τ).symm))
      obtain ⟨π,hπ,_⟩ := realizes hl'
      have hv : 0≤v := (abs_nonneg _).trans (bound l hl' π hπ)
      change (∑ τ ∈ F,(mean g τ).re) ≤ _ * v
      calc
        _ ≤ ∑ _τ ∈ F,v := Finset.sum_le_sum hb
        _ ≤ _ := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast multiplicity l hl') hv
    _ = _ := by
      simp only [Finset.mul_sum,totals,Finset.sum_mul,mul_assoc]
      exact Finset.sum_comm

/-- The disjoint-pair lower bound turns any dominating real matching coefficients into Marcus's
inequality on all complex positive semidefinite block matrices. -/
theorem marcus_of_real_bound {m k : ℕ} (hk : 0<k) (c : ℕ → ℝ)
    (bound : ∀ g : Gram m, UnitGram g → (Matrix.permanent g).re ≤
      ∑ j ∈ Finset.range (m/2+1), c j*Z g j)
    (fit : ∀ j ∈ Finset.range (m/2+1), c j ≤ ((m/2).choose j:ℝ)*((2:ℝ)^k-1)^j)
    (schur : ∀ p q, HomogeneousSchur (m*k) p q) : MarcusAt m k := by
  apply MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit hk ?_)
  intro x hu
  let F := fun i => packet (x i)
  let g := crossGram F F
  have hg : UnitGram g := by
    constructor
    · intro i; simp [g,F,crossGram,Coarse.bracket_self,hu]
    · intro i j; simp [g,F,crossGram,bracket,star_sum,star_mul',mul_comm]
    · intro i j
      simpa [sqEdge,g,F,crossGram,hu] using FiveProjection.bracket_bound (packet (x i)) (packet (x j))
  have hf := MatchingFine.average_fine_bound schur x
  simp only [hu] at hf
  apply (bound g hg).trans (le_trans (Finset.sum_le_sum ?_) hf)
  intro j hj
  exact mul_le_mul_of_nonneg_right (fit j hj) (Z_nonneg _ _)

end
end BlockPermanents.CyclePartitionSum
