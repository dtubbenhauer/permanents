import BlockPermanents.RoutingExits
import BlockPermanents.MarkedEdges

/-! # Recovering a marked operator coefficient by the forced-edge polynomial -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {m n k : ℕ} {R : Type*} [Ring R] [Algebra ℚ R]

theorem table_whole (p : Wire m k) : (table p).whole = MarkedEdges.whole p := by
  ext ⟨i,j⟩
  exact (Finset.mem_filter.trans (by simp only [Finset.mem_univ,true_and])).trans
    ((edge_iff p i j).trans (MarkedEdges.whole_iff p i j).symm)

theorem table_split_card (p : Wire m k) (hk : 0<k) :
    (table p).splitInputs.card = m-(MarkedEdges.whole p).card := by
  have h := (table p).splitInputs_add_whole hk
  rw [table_whole] at h; omega

def markedFactor (M : Routing m k) (a : Fin m) : ℚ :=
  (m:ℚ)/(2*M.splitInputs.card)*
    ((if a∈M.splitInputs then 1 else 0)+(if a∈M.splitOutputs then 1 else 0))

theorem table_markedFactor (p : Wire m k) (a : Fin m) (hk : 0<k) :
    markedFactor (table p) a =
      (m:ℚ)/(2*(m-(MarkedEdges.whole p).card : ℕ)) * MarkedEdges.splitEnds p a := by
  rw [markedFactor,table_split_card p hk]
  simp only [Routing.splitInputs,Routing.splitOutputs,
    table_whole, Finset.mem_sdiff, Finset.mem_univ,true_and,MarkedEdges.splitEnds]
  split_ifs <;> simp_all

/-- Expansion into individual strand permutations before evaluating the marked operator. -/
theorem marked_thin (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) (hk : 0<k) (hn : 0<n) :
    marked ρ a = ((k.factorial:ℚ)^(n+1))⁻¹ •
      ∑ p, markedFactor (table p) a • compressed ρ p := by
  rw [marked_expand _ _ hk hn,weighted_expand ρ (fun M => markedFactor M a)]
  simp only [markedFactor,Nat.cast_succ,mul_assoc]

/-- Any rational linear measurement of the actual marked operator is the
Appendix B polynomial readout, with weight equal to the same measurement
of each internally compressed wiring in permanent units. -/
theorem marked_polynomial (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) (hk : 0<k) (hn : 0<n)
    (L : R →ₗ[ℚ] ℚ) :
    L (marked ρ a) = ∑ h ∈ Finset.range (n+1), ((n+1:ℚ)/(2*(n+1-h:ℕ))) *
      (WholeEdges.certificate (MarkedEdges.whole (m:=n+1) (k:=k))
        (fun p => L (compressed ρ p)/(k.factorial:ℚ)^(n+1)) (MarkedEdges.ends a)).coeff h := by
  rw [← Nat.cast_succ]
  rw [marked_thin _ _ hk hn,map_smul,map_sum, WholeEdges.marked_readout]
  simp only [map_smul,smul_eq_mul,Finset.mul_sum,MarkedEdges.split_count hk]
  apply Finset.sum_congr rfl; intro p _
  rw [table_markedFactor p a hk]
  split_ifs with h
  · push_cast;ring
  · have hzero : n+1-(MarkedEdges.whole p).card=0 := by omega
    simp [hzero]

end
end BlockPermanents.RoutingFibres
