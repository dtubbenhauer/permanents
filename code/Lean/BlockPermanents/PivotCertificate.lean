import BlockPermanents.MatchingFaceCertificate
import BlockPermanents.PivotBudget
import BlockPermanents.MatchingThreshold

/-! # The pivot certificate of Lemma 7D.3 on the original packets

The elimination parameters spend both incident trades at every interior degree.
The remaining term is the last nonnegative pivot times the final matching moment.
-/
namespace BlockPermanents.PivotCertificate
open Closures MatchingFine CycleMatching MatchingFaceCertificate PivotBudget
noncomputable section
variable {m k d : ℕ}

/-- Exact fine-minus-coarse decomposition obtained by choosing the pivot
parameters in the signed four-face trades. -/
theorem unit_identity (x : Fin m → Fin k → Fin d → ℂ) (unit : ∀ i, Bend.energy (packet (x i))=1)
    (hp : (Threshold.tradeMatrix m (2^k-1)).PosSemidef) :
    let g := crossGram (fun i => packet (x i)) (fun i => packet (x i))
    fine (Function.uncurry x) - g.permanent.re = physical x (choice m (2^k-1)) +
      terminal m (2^k-1) (Z g) := by
  have h := packet_identity x unit (choice m (2^k-1)) (choice_pos _ _ hp)
  dsimp only at h ⊢
  rw [h]
  exact congrArg _ (PivotBudget.identity m _ hp _)

theorem unit_bound (x : Fin m → Fin k → Fin d → ℂ) (unit : ∀ i, Bend.energy (packet (x i))=1)
    (hp : (Threshold.tradeMatrix m (2^k-1)).PosSemidef) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤ fine (Function.uncurry x) := by
  apply sub_nonneg.mp
  rw [unit_identity x unit hp]
  exact add_nonneg (physical_nonneg x _ (choice_pos _ _ hp)) (terminal_nonneg _ _ hp _ (Matchings.moment_nonneg (fun _ => zero_le_one) (fun _ _ => Complex.normSq_nonneg _)))

/-- The numerical tridiagonal PSD criterion, via pivot elimination, on all
complex PSD matrices, including matrices with zero packets. -/
theorem marcus (hk : 0<k) (hp : (Threshold.tradeMatrix m (2^k-1)).PosSemidef) : MarcusAt m k :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit hk (fun x h => unit_bound x h hp))

/-- Example 7D.4 follows from the pivot certificate at thickness four. -/
theorem six_four : MarcusAt 6 4 := marcus (by decide) Threshold.tradeMatrix_six_four_psd

end
end BlockPermanents.PivotCertificate
