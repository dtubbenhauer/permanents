import BlockPermanents.PairSeamRank

/-! # The two branches of an actual packet cut in Lemma 7A.1 -/
namespace BlockPermanents.PairResidual
open Closures Bend PairBound
open scoped BigOperators Matrix
noncomputable section

/-- The first packet may have any scalar normalization. -/
def scaled {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) : Word d k → ℂ :=
  fun w => a * packet x w

theorem scaled_symmetric {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) :
    Symmetric (scaled a x) := by
  change (symClasp d k).mulVec (a • packet x) = a • packet x
  rw [Matrix.mulVec_smul, Bridges.packet_symmetric]

private theorem cut_column {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    {H : Word d k → ℂ} (hH : Symmetric H) (r : CutIndex k k) (b : Word d (k-r)) :
    (fun i => cutMatrix (scaled a x) H r i b) ∈ space x r := by
  have h : (fun i => cutMatrix (scaled a x) H r i b) =
      a • (fun i => cutMatrix (packet x) H r i b) := by
    funext i
    rw [cutMatrix_entry (scaled_symmetric a x) hH]
    simp only [Pi.smul_apply, smul_eq_mul, cutMatrix_entry (Bridges.packet_symmetric _ _ _) hH,
      scaled, mul_assoc, Finset.mul_sum]
  rw [h]
  exact (space x r).smul_mem a (cut_columns_mem x hH r b)

/-- The actual partial contraction in the coordinates of the supported positive cable. -/
def cutCoords {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) (H : Word d k → ℂ)
    (r : CutIndex k k) : SupportCup.Seam (space x r) → ℂ :=
  SupportCup.coords (space x r) (cutMatrix (scaled a x) H r)

/-- The component of the halfweb perpendicular to the final trace cup. -/
def residual {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ) (H : Word d k → ℂ)
    (r : CutIndex k k) : SupportCup.Seam (space x r) → ℂ :=
  (SupportCup.J (space x r)).mulVec (cutCoords a x H r)

/-- Closing the last cap gives the same pairing at each cut. -/
theorem close_cut {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    {H : Word d k → ℂ} (hH : Symmetric H) (r : CutIndex k k) :
    (SupportCup.cap (space x r)).mulVec (cutCoords a x H r) () = bracket H (scaled a x) := by
  rw [cutCoords, SupportCup.close _ _ (cut_column a x hH r),
    cut_trace (scaled_symmetric a x) hH]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_comm _ _

/-- The supported final cap has a bubble equal to the dimension of its positive cable. -/
theorem cut_bubble {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :
    SupportCup.cap (space x r) * (SupportCup.cap (space x r))ᴴ = (rank x r : ℂ) • 1 :=
  SupportCup.bubble _

open private normSq_trace_pair from BlockPermanents.PairBound in
/-- The cut of multiplicity C² splits into the reflected residual halfweb
and C²/d copies of the complete cap. -/
theorem cut_resolution {d k : ℕ} (a : ℂ) (x : Fin k → Fin d → ℂ)
    {H : Word d k → ℂ} (hH : Symmetric H) (r : CutIndex k k) (hr : 0 < rank x r) :
    cutTerm (scaled a x) H r =
      (k.choose r : ℝ)^2 * energy (residual a x H r) +
      ((k.choose r : ℝ)^2 / rank x r) * Complex.normSq (bracket (scaled a x) H) := by
  have h := SupportCup.resolution (space x r) hr _ (cut_column a x hH r)
  rw [cut_frobenius, cut_trace (scaled_symmetric a x) hH, normSq_trace_pair] at h
  rw [cutTerm, h]
  simp only [weight, Nat.cast_mul, residual, cutCoords, rank, div_eq_mul_inv]
  ring

/-- After retaining one completed cap for each choice of r positive slots,
the leftover coefficient on its square is nonnegative. -/
theorem surplus_nonneg {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k)
    (hr : 0 < rank x r) :
    0 ≤ (k.choose r : ℝ)^2 / rank x r - (k.choose r : ℝ) := by
  apply sub_nonneg.mpr
  apply (le_div_iff₀ (by exact_mod_cast hr : 0 < (rank x r : ℝ))).mpr
  rw [sq]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast rank_le x r) (Nat.cast_nonneg _)

end
end BlockPermanents.PairResidual
