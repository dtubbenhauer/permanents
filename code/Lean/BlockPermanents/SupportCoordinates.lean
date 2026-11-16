import BlockPermanents.FiveProjection
import Mathlib.Analysis.InnerProductSpace.Projection

/-! # A coordinate support for any marked family of k atoms

The construction preserves the Gram matrix and works even when the marked
columns are dependent or zero. The extra coordinates pad their span to a
k-plane. -/
namespace BlockPermanents.SupportCoordinates
open Closures
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section

private theorem bracket_inner {I : Type*} [Fintype I] (x y : EuclideanSpace ℂ I) :
    bracket (fun i => x i) (fun i => y i) = @inner ℂ _ _ x y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, bracket, mul_comm]

private theorem basis_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (x y : V) :
    let b := stdOrthonormalBasis ℂ V
    bracket (fun j => b.repr x j) (fun j => b.repr y j) = @inner ℂ _ _ x y := by
  let b := stdOrthonormalBasis ℂ V
  exact (bracket_inner (b.repr x) (b.repr y)).trans (b.repr.inner_map_map x y)

abbrev Ambient (d : ℕ) := EuclideanSpace ℂ (Fin d)
abbrev rank {d : ℕ} (K : Submodule ℂ (Ambient d)) := Module.finrank ℂ K
abbrev Index {d : ℕ} (k : ℕ) (K : Submodule ℂ (Ambient d)) := (Fin (rank K) ⊕ Fin (k-rank K)) ⊕ Fin d

def coords {d : ℕ} (k : ℕ) (K : Submodule ℂ (Ambient d)) (x : Ambient d) : Index k K → ℂ :=
  Sum.elim (Sum.elim (fun i => (stdOrthonormalBasis ℂ K).repr (K.orthogonalProjection x) i) (fun _ => 0))
    (fun j => (x - (K.orthogonalProjection x : Ambient d)) j)

private theorem projection_pair {d : ℕ} (K : Submodule ℂ (Ambient d)) (x y : Ambient d) :
    @inner ℂ K _ (K.orthogonalProjection x) (K.orthogonalProjection y) +
      @inner ℂ (Ambient d) _ (x-(K.orthogonalProjection x:Ambient d)) (y-(K.orthogonalProjection y:Ambient d)) =
      @inner ℂ _ _ x y := by
  rw [inner_sub_left,inner_sub_right,inner_sub_right]
  rw [← Submodule.inner_orthogonalProjection_eq_of_mem_right (K := K) (K.orthogonalProjection y) x,
    ← Submodule.inner_orthogonalProjection_eq_of_mem_left (K := K) (K.orthogonalProjection x) y,
    ← K.coe_inner (K.orthogonalProjection x) (K.orthogonalProjection y)]
  ring

theorem coords_pair {d : ℕ} (k : ℕ) (K : Submodule ℂ (Ambient d)) (x y : Ambient d) :
    bracket (coords k K x) (coords k K y) = @inner ℂ _ _ x y := by
  rw [← projection_pair K x y]
  have h := basis_pair (V := ↥K) (K.orthogonalProjection x) (K.orthogonalProjection y)
  have e := bracket_inner (x - (K.orthogonalProjection x : Ambient d)) (y - (K.orthogonalProjection y : Ambient d))
  exact (show bracket (coords k K x) (coords k K y) = _ by
    unfold bracket coords at *
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,map_zero,zero_mul,Finset.sum_const_zero,add_zero]
    exact congrArg₂ (·+·) h e)

/-- Simultaneously express every vector in an orthonormal coordinate system
whose first summand contains the given marked columns. -/
theorem adapt {k d : ℕ} (z : Fin k → Fin d → ℂ) :
    ∃ (n : ℕ) (S : Finset (Fin n)) (U : (Fin d → ℂ) → Fin n → ℂ),
      S.card = k ∧ (∀ x y, bracket (U x) (U y) = bracket x y) ∧
      (∀ i j, j ∉ S → U (z i) j = 0) := by
  classical
  let v (x : Fin d → ℂ) : Ambient d := (WithLp.equiv 2 _).symm x
  let K := Submodule.span ℂ (Set.range (fun i => v (z i)))
  have hr : rank K ≤ k := by simpa only [Fintype.card_fin] using
      (finrank_range_le_card (R := ℂ) (fun i => v (z i)))
  let A := Fin (rank K) ⊕ Fin (k-rank K)
  let e := Fintype.equivFin (Index k K)
  let S := (Finset.univ : Finset A).map ⟨fun a => e (Sum.inl a), e.injective.comp Sum.inl_injective⟩
  refine ⟨_,S,fun x j => coords k K (v x) (e.symm j),?_,?_,?_⟩
  · simp [S,A,Nat.add_sub_of_le hr]
  · intro x y
    exact (e.symm.sum_comp (fun j => conj (coords k K (v x) j)*coords k K (v y) j)).trans
      ((coords_pair k K (v x) (v y)).trans (bracket_inner (v x) (v y)).symm)
  · intro i j hj
    have mem : v (z i) ∈ K := Submodule.subset_span ⟨i,rfl⟩
    have hp := Submodule.orthogonalProjection_eq_self_iff.mpr mem
    obtain ⟨t,rfl⟩ := e.surjective j
    cases t with
    | inl a => exact (hj (Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩)).elim
    | inr t => simp [coords,hp]

end
end BlockPermanents.SupportCoordinates
