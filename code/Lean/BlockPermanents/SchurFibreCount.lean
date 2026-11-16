import BlockPermanents.SchurDoubleCoset
import BlockPermanents.SchurSubsetCount
import Mathlib.GroupTheory.Perm.Finite

/-! # The number of slot permutations with a fixed crossing count -/
namespace BlockPermanents.SchurFibreCount
open WireSchur
noncomputable section

/-- Destinations of the left input slots. -/
def leftImage {p q : ℕ} (g : Equiv.Perm (Slots p q)) : Finset (Slots p q) :=
  Finset.univ.map (Function.Embedding.inl.trans g.toEmbedding)

private theorem mem_leftImage {p q : ℕ} (g : Equiv.Perm (Slots p q)) (y : Slots p q) :
    y ∈ leftImage g ↔ ∃ i : Fin p, g (.inl i) = y := by
  simp [leftImage]

private theorem card_leftImage {p q : ℕ} (g : Equiv.Perm (Slots p q)) :
    (leftImage g).card = p := by simp [leftImage]

private theorem cross_card {p q : ℕ} (g : Equiv.Perm (Slots p q)) :
    SchurClass.crossCount g = (leftImage g).toRight.card := by
  unfold SchurClass.crossCount
  apply Finset.card_bij (fun i hi => (g (.inl i)).getRight (Finset.mem_filter.mp hi).2)
  · intro i hi
    exact Finset.mem_toRight.mpr ((mem_leftImage _ _).mpr ⟨i, (Sum.inr_getRight _ _).symm⟩)
  · intro i hi j hj he
    apply Sum.inl.inj (β := Fin q)
    apply g.injective
    exact (Sum.inr_getRight _ _).symm.trans ((congrArg Sum.inr he).trans (Sum.inr_getRight _ _))
  · intro j hj
    obtain ⟨i, hi⟩ := (mem_leftImage _ _).mp (Finset.mem_toRight.mp hj)
    have h : (g (.inl i)).isRight := by rw [hi]; rfl
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
      Sum.inr.inj ((Sum.inr_getRight _ _).trans hi)⟩

private theorem exists_leftImage {p q : ℕ} (s : Finset (Slots p q)) (hs : s.card = p) :
    ∃ g : Equiv.Perm (Slots p q), leftImage g = s := by
  classical
  let a : Fin p ≃ s := Fintype.equivOfCardEq (by simp [hs])
  let b : Fin q ≃ {x : Slots p q // x ∉ s} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl]; simp [Slots,hs])
  let g := (a.sumCongr b).trans (Equiv.sumCompl (· ∈ s))
  refine ⟨g, ?_⟩
  ext x
  rw [mem_leftImage]
  constructor
  · rintro ⟨i,rfl⟩
    exact (a i).property
  · intro hx
    obtain ⟨i, hi⟩ := a.surjective ⟨x,hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- Ordering the left and right sources independently accounts for every
permutation with a given left image, including for either empty packet. -/
theorem card_leftImage_fibre {p q : ℕ} (s : Finset (Slots p q)) (hs : s.card = p) :
    Fintype.card {g : Equiv.Perm (Slots p q) // leftImage g = s} = p.factorial * q.factorial := by
  classical
  obtain ⟨b,hb⟩ := exists_leftImage s hs
  let block := Equiv.Perm.sumCongrHom (Fin p) (Fin q)
  let f : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) → {g : Equiv.Perm (Slots p q) // leftImage g = s} :=
    fun h => ⟨b * block h, by
      rw [← hb]
      ext y
      simp only [mem_leftImage, Equiv.Perm.mul_apply]
      change (∃ i : Fin p, b (.inl (h.1 i)) = y) ↔ ∃ j : Fin p, b (.inl j) = y
      constructor
      · rintro ⟨i, hi⟩; exact ⟨h.1 i, hi⟩
      · rintro ⟨j, hj⟩; exact ⟨h.1.symm j, by simpa using hj⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact Equiv.Perm.sumCongrHom_injective (mul_left_cancel (congrArg Subtype.val h))
    · rintro ⟨g,hg⟩
      have maps : Set.MapsTo (b⁻¹ * g) (Set.range Sum.inl) (Set.range Sum.inl) := by
        rintro _ ⟨i, rfl⟩
        have hmem : g (.inl i) ∈ leftImage g := (mem_leftImage _ _).mpr ⟨i,rfl⟩
        rw [hg, ← hb, mem_leftImage] at hmem
        obtain ⟨j,hj⟩ := hmem
        exact ⟨j, by rw [Equiv.Perm.mul_apply, ← hj, Equiv.Perm.inv_apply_self]⟩
      obtain ⟨h, hh⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl maps
      refine ⟨h, Subtype.ext ?_⟩
      change b * block h = g
      have he : block h = b⁻¹ * g := hh
      rw [he, mul_inv_cancel_left]
  simpa only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using
    (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- Exact multiplicity of the r-crossing double coset, before averaging
the two source packets and the two target packets. -/
theorem card_cross_fibre {p q : ℕ} (r : Bend.CutIndex p q) :
    Fintype.card {g : Equiv.Perm (Slots p q) // SchurClass.crossCount g = r.val} =
      p.factorial * q.factorial * p.choose r.val * q.choose r.val := by
  classical
  let good (s : Finset (Slots p q)) := s.card = p ∧ s.toRight.card = r.val
  have he (g : Equiv.Perm (Slots p q)) : SchurClass.crossCount g = r.val ↔ good (leftImage g) := by
    simp [good, card_leftImage, cross_card]
  rw [← Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype leftImage he), Fintype.card_sigma]
  simp_rw [fun s : Subtype good => card_leftImage_fibre s.val s.property.1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    show Fintype.card (Subtype good) = p.choose r.val * q.choose r.val from
      SchurSubsetCount.card_subsets (WireSchur.leftLe r)]
  simp only [Nat.cast_id]
  ring

end
end BlockPermanents.SchurFibreCount
