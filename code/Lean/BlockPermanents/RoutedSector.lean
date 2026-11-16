import BlockPermanents.RoutedTrace

/-! # Occupation-sector scalars of the symmetric outer cable -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset Closures Bend
open scoped BigOperators
noncomputable section

/-- Occupied output slots in the supported alphabet. -/
def occupied {N d : ℕ} (S : Finset (Fin d)) (w : Word d N) : Finset (Fin N) :=
  univ.filter (fun i => w i ∈ S)

private theorem placement {N d : ℕ} (S : Finset (Fin d)) (w : Word d N)
    (M : Finset (Fin N)) (p : Perm (Fin N)) :
    (∀ i ∈ M,(w ∘ p) i ∈ S) ↔ M.map p.toEmbedding ⊆ occupied S w := by
  constructor
  · rintro h j hj
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
    exact mem_filter.mpr ⟨mem_univ _,h i hi⟩
  · intro h i hi
    exact (mem_filter.mp (h (mem_map.mpr ⟨i,hi,rfl⟩))).2

theorem clasp_wire {N d : ℕ} (S : Finset (Fin d)) (p : Perm (Fin N)) (M : Finset (Fin N))
    {f : Word d N → ℂ} (hf : Symmetric f) (w : Word d N) :
    clasp (wire S p M f) w =
      (((occupied S w).card.choose M.card : ℕ) : ℂ) / (N.choose M.card : ℂ) * f w := by
  have hfix (σ : Perm (Fin N)) : f (w ∘ σ) = f w := by
    rw [Bend.Symmetric,Bridges.symClasp_action] at hf
    simpa only [hf,Equiv.symm_symm] using clasp_invariant f σ.symm w
  let W := occupied S w
  let g (v : Finset (Fin N)) : ℚ := if v ⊆ W then 1 else 0
  have av := Occupation.symmetrizer_word g M
  have ct : (∑ t ∈ univ.powersetCard M.card,g t) = (W.card.choose M.card : ℚ) := by
    change (∑ t ∈ univ.powersetCard M.card, if t ⊆ W then (1:ℚ) else 0) = _
    rw [← Finset.sum_filter,Routings.survivingPlacements]
    simp [card_powersetCard]
  rw [ct] at av
  have ac := congrArg (fun c : ℚ => (c:ℂ)) av
  simp only [Occupation.permSum,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast] at ac
  have t (σ : Perm (Fin N)) :
      wire S p M f (w ∘ σ.symm) = (g (M.map σ.symm.toEmbedding) : ℂ) * f w := by
    have ht := hfix (p.trans σ.symm)
    change f ((w ∘ σ.symm) ∘ p)=f w at ht
    simp only [wire,placement,ht,g,W]
    split <;> simp
  have inv := Equiv.sum_comp (Equiv.inv (Perm (Fin N)))
    (fun σ : Perm (Fin N) => (g (M.map σ.toEmbedding) : ℂ))
  simp only [clasp,sumSlots,Fintype.card_fin]
  simp_rw [t]
  rw [← Finset.sum_mul,← mul_assoc]
  change ((N.factorial : ℂ)⁻¹ * ∑ σ : Perm (Fin N), (g (M.map ((Equiv.inv _ σ).toEmbedding)) : ℂ)) * _ = _
  rw [inv,mul_comm ((N.factorial:ℂ)⁻¹),← div_eq_mul_inv,ac]

private theorem clasp_scale {N d : ℕ} (a : ℂ) (f : Word d N → ℂ) :
    clasp (fun w => a * f w) = fun w => a * clasp f w := by
  funext w
  simp only [clasp,sumSlots,← Finset.mul_sum]
  ring

/-- An arbitrary permutation left by opening the internal clasps yields one
of the claimed monomials. Its exponents depend only on the wiring. -/
theorem sector_monomial {N d : ℕ} (r : ℕ) (p : Perm (Cable (Fin N) r)) :
    ∃ (j q : ℕ), q ≤ N ∧ j+q ≤ r ∧
      ∀ (S : Finset (Fin d)) (f : Word d N → ℂ), Symmetric f → ∀ w,
        clasp (close S r (wire S p ∅) f) w =
          (S.card : ℂ)^j * (((occupied S w).card.choose q : ℕ) : ℂ) /
            (N.choose q : ℂ) * f w := by
  obtain ⟨j,M,u,h,he⟩ := follow (D:=Fin d) r p ∅
  refine ⟨j,M.card,by simpa using M.card_le_univ,by simpa using h,?_⟩
  intro S f hf w
  rw [he,clasp_scale]
  dsimp only
  rw [clasp_wire S u M hf w]
  ring

end
end BlockPermanents.RoutedTrace
