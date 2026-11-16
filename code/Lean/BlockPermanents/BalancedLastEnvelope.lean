import BlockPermanents.BalancedLastPlanes
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! Extending the span of the atoms to a marked plane of the prescribed
dimension, also for a zero packet or linearly dependent atoms. -/
namespace BlockPermanents.BalancedLast
open Closures ThreePlane FourPlaneBasis
open scoped Matrix
noncomputable section

private theorem extend_plane {d : ℕ} (W : Submodule ℂ (Ambient d)) {k : ℕ}
    (hW : Module.finrank ℂ W ≤ k) (hk : k ≤ d) :
    ∃ S : Submodule ℂ (Ambient d), W ≤ S ∧ Module.finrank ℂ S = k := by
  induction k, hW using Nat.le_induction with
  | base => exact ⟨W, le_rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨P,hP,rP⟩ := ih (by omega)
    have dimlt : Module.finrank ℂ P < Module.finrank ℂ (Ambient d) := by
      rw [rP,finrank_euclideanSpace_fin]; omega
    obtain ⟨v,hv⟩ := P.exists_of_finrank_lt dimlt
    have hmem : v ∉ P := by simpa using hv 1 one_ne_zero
    have hn : v ≠ 0 := fun h => hmem (h ▸ P.zero_mem)
    let line := Submodule.span ℂ {v}
    have disj : Disjoint P line := (Submodule.disjoint_span_singleton' hn).mpr hmem
    refine ⟨P ⊔ line, hP.trans le_sup_left, ?_⟩
    have dim := P.finrank_sup_add_finrank_inf_eq line
    rw [disj.eq_bot,finrank_bot,add_zero,rP,show Module.finrank ℂ line = 1 from finrank_span_singleton hn] at dim
    exact dim

/-- Any k atoms in a Gram space of dimension at least k fit in a k-plane.
The plane contains the atoms separately as well as their symmetric packet. -/
theorem packet_plane {d k : ℕ} (hkd : k ≤ d) (x : Fin k → Fin d → ℂ) :
    ∃ S : Submodule ℂ (Ambient d), Module.finrank ℂ S = k ∧
      (∀ i, (WithLp.equiv 2 _).symm (x i) ∈ S) ∧ packet x ∈ symmetricPower k S := by
  let v (i : Fin k) : Ambient d := (WithLp.equiv 2 _).symm (x i)
  let W := Submodule.span ℂ (Set.range v)
  have hW : Module.finrank ℂ W ≤ k := by
    simpa only [Fintype.card_fin] using finrank_range_le_card (R := ℂ) v
  obtain ⟨S,h,r⟩ := extend_plane W hW hkd
  have h' (i : Fin k) : v i ∈ S := h (Submodule.subset_span ⟨i,rfl⟩)
  exact ⟨S,r,h',Submodule.subset_span ⟨fun i => ⟨v i,h' i⟩,rfl⟩⟩

/-- The k-plane in coordinates gives an isometric k-column frame even when
the input atoms do not themselves form a basis. -/
theorem exists_packet_frame {d k : ℕ} (hkd : k ≤ d) (x : Fin k → Fin d → ℂ) :
    ∃ U : Matrix (Fin d) (Fin k) ℂ, Uᴴ * U = 1 ∧ packet x ∈ BalancedSupport.space k U := by
  obtain ⟨S,hS,_,h⟩ := packet_plane hkd x
  subst k
  exact ⟨basisMatrix S, basis_isometry S, (space_symmetricPower _ S).symm ▸ h⟩

/-- The bent packet belongs to the dual frame used by the balanced last cap. -/
theorem packet_turnedPlane {d k : ℕ} (hkd : k ≤ d) (x : Fin k → Fin d → ℂ) :
    ∃ (S : Submodule ℂ (Ambient d)) (hS : Module.finrank ℂ S = k),
      (fun w => star (packet x w)) ∈ BalancedSupport.space k (turnedFrame S hS) := by
  obtain ⟨S,hS,_,h⟩ := packet_plane hkd x
  refine ⟨S,hS,(turnedFrame_mem S hS k _).mpr ?_⟩
  simpa only [star_star] using h

end
end BlockPermanents.BalancedLast
