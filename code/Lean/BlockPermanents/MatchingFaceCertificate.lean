import BlockPermanents.FaceCoarseCertificate
import BlockPermanents.MatchingFineSquares

/-! Fine and coarse reflected cuts evaluated on the same packet family. -/
namespace BlockPermanents.MatchingFaceCertificate
open Closures MatchingFine CycleMatching
noncomputable section

variable {m d k : ℕ}

def fineBudget (m b : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m/2+1), (((m/2).choose r * b^r : ℕ):ℝ)*z r

def coarseBudget (m : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m/2+1), (Threshold.pathCoeff m r : ℝ)*z r

/-- Number the word coordinates before taking the four-face averages. -/
def flatten (x : Fin m → Fin k → Fin d → ℂ) (i : Fin m) (j : Fin (Fintype.card (Fin k → Fin d))) : ℂ :=
  packet (x i) ((Fintype.equivFin (Fin k → Fin d)).symm j)

theorem flatten_gram (x : Fin m → Fin k → Fin d → ℂ) :
    crossGram (flatten x) (flatten x) = crossGram (fun i => packet (x i)) (fun i => packet (x i)) := by
  funext i j
  exact (Fintype.equivFin (Fin k → Fin d)).symm.sum_comp
    (fun t => star (packet (x i) t) * packet (x j) t)

def physical (x : Fin m → Fin k → Fin d → ℂ) (u : ℕ → ℝ) : ℝ :=
  Matchings.average m (MatchingFineSquares.orderedRemainder x) + FaceCoarseCertificate.remainder (flatten x) u

theorem physical_nonneg (x : Fin m → Fin k → Fin d → ℂ) (u : ℕ → ℝ) (hu : ∀ r, 0 < u r) :
    0 ≤ physical x u :=
  add_nonneg (MatchingFineSquares.averageRemainder_nonneg x) (FaceCoarseCertificate.remainder_nonneg _ u hu)

theorem packet_identity (x : Fin m → Fin k → Fin d → ℂ) (unit : ∀ i, Bend.energy (packet (x i))=1)
    (u : ℕ → ℝ) (hu : ∀ r, 0 < u r) :
    let g := crossGram (fun i => packet (x i)) (fun i => packet (x i))
    let z := Z g
    fine (Function.uncurry x) - g.permanent.re = physical x u +
      (fineBudget m (2^k-1) z - coarseBudget m z + FaceCoarseCertificate.gain z m u) := by
  let g := crossGram (fun i => packet (x i)) (fun i => packet (x i))
  let z := Z g
  have uy (i) : Bend.energy (flatten x i)=1 :=
    ((Fintype.equivFin (Fin k → Fin d)).symm.sum_comp (fun t => Complex.normSq (packet (x i) t))).trans (unit i)
  have rightEq := FaceCoarseCertificate.coarse_identity (flatten x) uy u hu
  dsimp only at rightEq
  rw [MatchingFine.fine,flatten_gram] at rightEq
  change coarseBudget m z = g.permanent.re + FaceCoarseCertificate.gain z m u +
    FaceCoarseCertificate.remainder (flatten x) u at rightEq
  have leftEq := MatchingFineSquares.unit_identity x unit
  have coeff : (((2^k-1:ℕ)):ℝ) = (2:ℝ)^k-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow k 2 (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have lb : fineBudget m (2^k-1) z = ∑ r ∈ Finset.range (m/2+1), ((m/2).choose r:ℝ) * ((2:ℝ)^k-1)^r * z r := by
    simp only [fineBudget,Nat.cast_mul,Nat.cast_pow,coeff]
  change fine (Function.uncurry x) = _ + Matchings.average m (MatchingFineSquares.orderedRemainder x) at leftEq
  change fine (Function.uncurry x) - g.permanent.re = physical x u +
    (fineBudget m (2^k-1) z - coarseBudget m z + FaceCoarseCertificate.gain z m u)
  rw [lb]
  unfold physical
  change fine (Function.uncurry x) = (∑ r ∈ Finset.range (m/2+1), ((m/2).choose r:ℝ) * ((2:ℝ)^k-1)^r*z r) + _ at leftEq
  linarith only [leftEq,rightEq]

end
end BlockPermanents.MatchingFaceCertificate
