import BlockPermanents.CycleParameters
import BlockPermanents.CyclePartitionSum

/-! # Appendix A's disjoint-cycle estimate and block-permanent criterion -/
namespace BlockPermanents.DisjointCycles
open CycleClasses CycleAllocation CyclePlans CycleTen CycleMatching CyclePolynomial CycleComposition
open CycleCoefficients CycleParameters CyclePartitionSum SchurNormalization
open scoped BigOperators
noncomputable section

/-- Sum of the class-size-weighted coefficients of the product of the odd-cycle factors
and the alternating even-cycle monomials. Parameters can depend on the partition and on
the occurrence of the odd cycle, independently for repeated cycle lengths. -/
def D (m : ℕ) (u : List ℕ → ℕ → ℝ) := totals m (fun l => pcoeff (plan l) (u l))

theorem signed_sum {m : ℕ} (u : List ℕ → ℕ → ℝ)
    (hu : ∀ l ∈ partitions m, ∀ i, 0<u l i) (g : Gram m) (hg : UnitGram g) :
    (Matrix.permanent g).re ≤ ∑ j ∈ Finset.range (m/2+1), D m u j * Z g j := by
  apply sum_classes
  intro l hl τ hτ
  obtain ⟨hp,hs⟩ := partition_data hl
  obtain ⟨hn,ht⟩ := plan_data l hp
  rw [hs] at hn
  generalize hw : plan l = p at hn ht ⊢
  clear hs
  subst m
  exact class_bound_sum p (u l) (hu l hl) τ (hτ.trans ht.symm) g hg

/-- The numerical coefficient test implies Marcus's inequality for arbitrary complex PSD
matrices at the specified block count and positive thickness. -/
theorem marcus {m k : ℕ} (hk : 0<k) (u : List ℕ → ℕ → ℝ)
    (hu : ∀ l ∈ partitions m, ∀ i, 0<u l i)
    (fit : ∀ j ∈ Finset.range (m/2+1), D m u j ≤ ((m/2).choose j:ℝ)*((2:ℝ)^k-1)^j)
    (schur : ∀ p q, HomogeneousSchur (m*k) p q) : MarcusAt m k :=
  marcus_of_real_bound hk _ (signed_sum u hu) fit schur

end
end BlockPermanents.DisjointCycles
