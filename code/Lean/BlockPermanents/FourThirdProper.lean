import BlockPermanents.FourThirdHalf

/-! # The third proper-cut family in the four-packet bend -/
namespace BlockPermanents.FourNative
open Bend FourRoutes FourTarget FourThickOpenings Support
open scoped Matrix BigOperators
noncomputable section

/-- The fixed r exchange in the all-three-packet opening, with the
multiplicities from choosing its ordinary and marked strands. -/
theorem third_proper_term {d k : ℕ} (r : CutIndex (3*k) k) :
    let P := localClasp d k 3
    let e := act d k (FourThickSlots.exchange k 3 (by decide) r)
    scale 3 k • read (ZeroCap.inner d k 3) (symClasp d k)
      ((weight (3*k) k r : ℚ) • (P * e * P)) =
      (scale 3 k * ((3*k).choose r : ℚ) * (k.choose r : ℚ)) •
        reflected (thirdProperHalf (d:=d) r) := by
  dsimp only
  rw [map_smul, smul_smul, read_third_cut]
  simp only [weight, Nat.cast_mul, mul_assoc]

theorem third_proper_family (d k : ℕ) :
    scale 3 k • read (ZeroCap.inner d k 3) (symClasp d k) (V d k) =
      ∑ r ∈ properIndices (3*k) k,
        (scale 3 k * ((3*k).choose r : ℚ) * (k.choose r : ℚ)) •
          reflected (thirdProperHalf (d:=d) r) := by
  unfold V proper
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun r _ => third_proper_term r)

/-- The unique proper cut in the quadratic three-packet merge. -/
theorem quadratic_third_family (d : ℕ) :
    scale 3 2 • read (ZeroCap.inner d 2 3) (symClasp d 2) (V d 2) =
      (1080 : ℚ) • reflected (thirdProperHalf (d:=d) (k:=2) 1) := by
  rw [third_proper_family, show properIndices (3*2) 2 = {1} by decide +kernel,
    Finset.sum_singleton]
  congr 1
  decide +kernel

end
end BlockPermanents.FourNative
