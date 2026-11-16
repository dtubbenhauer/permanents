import BlockPermanents.FourPlaneCompression

/-! # The four-quadratic matrix inequality using only switches in Gram dimension eight -/

namespace BlockPermanents.FourPlaneCompression
open FourPlaneBasis FourCompression FourTarget FourUpright FourMatrixHalves FourCapOrbit
open FourRoutes FourSupportedTensor Closures Bend SchurNormalization MatchingThreshold
open scoped BigOperators Matrix ComplexOrder
noncomputable section

private theorem marked_nonnegative {d : ℕ} (x : Fin 4 → Fin 2 → Fin d → ℂ)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) :
    0 ≤ (bracket (flatPackets x) (Q d 2 (flatPackets x))).re := by
  classical
  let a := x ∘ ori
  let F := unmarked a
  let H := packet (a 3)
  let atoms (i : Fin 2) : Ambient d := (WithLp.equiv 2 _).symm (a 3 i)
  let K := Submodule.span ℂ (Set.range atoms)
  have hK : Module.finrank ℂ K ≤ 2 := by
    simpa only [Fintype.card_fin] using finrank_range_le_card (R := ℂ) atoms
  have hz : product F (fun j => star (H j)) ∈ planeSupport K :=
    Submodule.subset_span ⟨F, atoms, packet_inner _, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  have hf : pull (layout d) (product F H) = flatPackets x := by
    rw [FourCompression.ordinary_product]
    change packets d 2 ori (FourWireCut.product (FourFootAverage.first F) H) = flatPackets x
    rw [← FourMatrixHalves.flat a, oriented_flat]
    simp [a, Function.comp_def]
  have hn := FourPlaneCompression.nonnegative K hK h₂ h₄ h₆ hz
  rw [← evaluate_bend, marked_quadratic, hf] at hn
  exact hn

/-- Each marked summand uses the span of its own two atoms inside the same
eight-dimensional Gram realization. The three switch hypotheses are needed only there. -/
theorem marcus_four_quadratic (h₂ : HomogeneousSchur 8 2 2)
    (h₄ : HomogeneousSchur 8 4 2) (h₆ : HomogeneousSchur 8 6 2) : MarcusAt 4 2 := by
  apply marcusAt_of_gram
  intro x
  have h := congrArg Complex.re (averaged_gap x)
  simp only [Complex.re_sum, Complex.mul_re, show (24 : ℂ).re = 24 by norm_num,
    show (24 : ℂ).im = 0 by norm_num, zero_mul, sub_zero, Complex.sub_re, FourRestricted.relabel] at h
  have nn := Finset.sum_nonneg (s := (Finset.univ : Finset TransferBlocks.FourPerm))
    (fun σ _ => marked_nonnegative (x ∘ (σ⁻¹).symm) h₂ h₄ h₆)
  linarith

end
end BlockPermanents.FourPlaneCompression
