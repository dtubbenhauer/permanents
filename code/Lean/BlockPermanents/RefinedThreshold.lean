import BlockPermanents.RefinedCoarse
import BlockPermanents.FaceSpectral
import BlockPermanents.MatchingThreshold
import BlockPermanents.PacketScale

/-! # Proposition 7D.2: the four-face matrix criterion

The entire deduction starts with homogeneous Schur, the finite packet
data, and the stated PSD condition on the numerical tridiagonal matrix.
-/
namespace BlockPermanents.RefinedThreshold
open Closures CycleMatching SchurNormalization MatchingFine
noncomputable section

theorem unit_bound {m k d : ℕ} (schur : ∀ a p q, HomogeneousSchur a p q)
    (psd : (Threshold.tradeMatrix m (2^k-1)).PosSemidef)
    (x : Fin m → Fin k → Fin d → ℂ) (unit : ∀ i, Bend.energy (packet (x i))=1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      fine (Function.uncurry x) := by
  classical
  let T := Fin k → Fin d
  let e := Fintype.equivFin T
  let F := fun i => packet (x i)
  let y (i : Fin m) (j : Fin (Fintype.card T)) := F i (e.symm j)
  let g := crossGram F F
  have hg : crossGram y y = g := by
    funext i j
    exact e.symm.sum_comp (fun t => star (F i t) * F j t)
  have hy (i) : Bend.energy (y i)=1 := (e.symm.sum_comp (fun t => Complex.normSq (F i t))).trans (unit i)
  let z := Z g
  have hz (s) : 0 ≤ z s := Matchings.moment_nonneg (fun _ => zero_le_one) (fun _ _ => Complex.normSq_nonneg _)
  have upper := RefinedCoarse.upper y (schur _ ) hy
  unfold fine at upper
  simp only [hg] at upper
  have spectral := FaceSpectral.compare z hz psd
  have lower := average_fine_bound (schur _) x
  have hb : (((2^k-1 : ℕ) : ℕ) : ℝ) = (2:ℝ)^k-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow k 2 (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  simp only [Nat.cast_mul,Nat.cast_pow,hb] at spectral
  simp only [unit] at lower
  exact (upper.trans spectral).trans lower

/-- On arbitrary complex PSD matrices, the numerical four-face PSD
test suffices. Unit normalization is removed, including zero packets. -/
theorem marcus {m k : ℕ} (hk : 0 < k) (schur : ∀ d p q, HomogeneousSchur d p q)
    (psd : (Threshold.tradeMatrix m (2^k-1)).PosSemidef) : MarcusAt m k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit hk (fun x h => unit_bound schur psd x h))

/-- The displayed six-block example follows directly from its tridiagonal
certificate, with no independently assumed matrix inequality. -/
theorem six_four (schur : ∀ d p q, HomogeneousSchur d p q) : MarcusAt 6 4 :=
  marcus (by decide) schur Threshold.tradeMatrix_six_four_psd

end
end BlockPermanents.RefinedThreshold
