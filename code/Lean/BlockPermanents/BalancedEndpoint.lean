import BlockPermanents.BalancedCut
import BlockPermanents.PacketScale
import BlockPermanents.MatchingThreshold

/-! # Four matrix packets from the balanced cuts -/
namespace BlockPermanents.BalancedEndpoint
open Closures Bend BalancedCut FourTrade MatchingFine SchurNormalization
noncomputable section

/-- The fine permanent dominates the product of the two disjoint pair
cuts in each of the three actual divisions of the four packets. -/
theorem three_cut_lower {k d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 4 → Fin k → Fin d → ℂ) (hz : ∀ i, energy (packet (x i)) = 1) :
    let X := fun i => packet (x i)
    let g := crossGram X X
    let b := (2:ℝ)^k-1
    3+b*edges g+b^2*matchings g ≤ 3*fine (Function.uncurry x) := by
  let X := fun i => packet (x i)
  let b := (2:ℝ)^k-1
  have h (π : Equiv.Perm (Fin 4)) :
      (1+b*sq X (π 0) (π 1))*(1+b*sq X (π 2) (π 3)) ≤ fine (Function.uncurry x) := by
    have hc := ordered_fine_bound schur x π
    change ((∏ i : Fin 2, edgeFactor b (fun j => energy (packet (x j))) (sq X)
        (π (partner 4 i 0)) (π (partner 4 i 1)))) * (∏ t : Fin 0, _) ≤ _ at hc
    simpa [edgeFactor, Fin.prod_univ_succ, hz, partner] using hc
  have h₁ := h 1
  have h₂ := h (Equiv.swap 1 2)
  have h₃ := h (Equiv.swap 1 3)
  simp (config := {decide := true}) [Equiv.swap_apply_def] at h₁ h₂ h₃
  have flip : sq X 2 1 = sq X 1 2 := by
    have he : star (bracket (X 2) (X 1)) = bracket (X 1) (X 2) := by simp [bracket,star_sum,mul_comm,Complex.star_def]
    rw [BalancedCut.sq,BalancedCut.sq,← he,Complex.star_def,Complex.normSq_conj]
  rw [flip] at h₃
  change 3+b*(sq X 0 1+sq X 0 2+sq X 0 3+sq X 1 2+sq X 1 3+sq X 2 3)+
    b^2*(sq X 0 1*sq X 2 3+sq X 0 2*sq X 1 3+sq X 0 3*sq X 1 2) ≤ _
  linarith only [h₁,h₂,h₃]

/-- The unit-product proof compares the actual signed coarse routes with
the three balanced fine cuts. It holds in every Gram dimension. -/
theorem unit_four {k d : ℕ} (hk : 3 ≤ k) (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 4 → Fin k → Fin d → ℂ) (h : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      fine (Function.uncurry x) := by
  let X := fun i => packet (x i)
  let g := crossGram X X
  let b := (2:ℝ)^k-1
  have hu := three_cut_upper X h
  have hl := three_cut_lower schur x h
  have hb : 7 ≤ b := by
    have h' : (2:ℝ)^3 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    dsimp [b]; norm_num at h'; linarith
  have hbb : 9 ≤ b^2 := by nlinarith
  have hp : 0 ≤ edges g := by simp only [edges, Complex.normSq_eq_norm_sq]; positivity
  have hs : 0 ≤ matchings g := by simp only [matchings, Complex.normSq_eq_norm_sq]; positivity
  change 3*g.permanent.re ≤ _ at hu
  change 3+b*edges g+b^2*matchings g ≤ _ at hl
  change g.permanent.re ≤ _
  linarith only [hu,hl,mul_le_mul_of_nonneg_right hb hp,mul_le_mul_of_nonneg_right hbb hs]

/-- The four-block result at k=3 and every greater thickness, obtained
through the two-versus-two product cuts and the signed gluing. -/
theorem marcus_four {k : ℕ} (hk : 3 ≤ k) (schur : ∀ p q, HomogeneousSchur (4*k) p q) :
    MarcusAt 4 k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by omega) (unit_four hk schur))

end
end BlockPermanents.BalancedEndpoint
