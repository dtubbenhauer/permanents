import BlockPermanents.ThreeCanonicalGlue

/-! # Identification of the original three-packet marked operator -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend ThreeTransfer TransferBlocks SchurNormalization
open scoped Matrix BigOperators
noncomputable section

/-- The original unbent Q₃ of Section 3C in the three ambient word
coordinates, with both whole-packet transpositions, the first and last
fine pairs and the complete fine clasp. -/
def original (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ :=
  let a : ℂ := (k+k).choose k
  let b : ℂ := (k+k+k).choose (k+k)
  let u := swapFront d k
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  let f := pair u
  let g := pair t
  let p := firstFine d k
  a • (b • allFine d k) - (6:ℚ) • triple u t +
    a • ((2:ℂ) • (f*secondFine d k*f)-p*g*f-f*g*p)

private theorem compression_algebra {I : Type*} [Fintype I] [DecidableEq I]
    (D f p q e t C : Matrix I I ℂ) (a b : ℂ)
    (hf : fᴴ=f) (hp : pᴴ=p) (pp : p*p=p) (fp : f*p=p) (pf : p*f=p)
    (pe : p*e=e) (ep : e*p=e) :
    a • (b • ((p*D)ᴴ*e*(p*D))) - Dᴴ*C*D +
      a • ((2:ℂ) • ((f*D)ᴴ*q*(f*D)) - (p*D)ᴴ*(p*D) -
        (1/2:ℂ) • ((p*D)ᴴ*t*(f*D)+(f*D)ᴴ*t*(p*D))) =
      Dᴴ*(a • (b • e)-C+
        a • ((2:ℂ) • (f*q*f)-p*pair t*f-f*pair t*p))*D := by
  have hmid : p*pair t*f + f*pair t*p = p+(1/2:ℂ) • (p*t*f+f*t*p) := by
    simp only [pair,Matrix.smul_mul,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,
      Matrix.one_mul,Matrix.mul_one,pf,fp,smul_add,Rat.smul_def]
    norm_num
    module
  have hm : (2:ℂ) • (f*q*f)-p*pair t*f-f*pair t*p = (2:ℂ) • (f*q*f)-(p+(1/2:ℂ) • (p*t*f+f*t*p)) := by
    rw [← hmid]; abel
  rw [hm]
  simp only [Matrix.conjTranspose_mul,hf,hp,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,
    Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc e p D,ep,← Matrix.mul_assoc p e D,pe,← Matrix.mul_assoc p p D,pp]
  module

theorem original_corrected (d k : ℕ) :
    (internal d k)ᴴ * original d k * internal d k = corrected (M d k) (P d k) (symClasp d k) := by
  have e : (allFine d k)ᴴ = allFine d k := by ext i j; exact column_star _ _
  have pe : firstFine d k * allFine d k = allFine d k := by
    simpa only [Matrix.conjTranspose_mul,fine_star,e] using congrArg Matrix.conjTranspose (all_first d k)
  unfold corrected
  rw [coarse_six,opened_small,opened_big,straight_big]
  simp only [mixed,← fine_leg, legs_pair]
  exact (compression_algebra _ _ _ _ _ _ _ _ _ (pair_star _ _) (fine_star _ _)
    (first_sq _ _) (first_pair _ _) (pair_first _ _) pe (all_first _ _)).symm

/-- Lemma 3C.5 on the actual symmetric-packet boundary for every positive
thickness, in the ordinary basis and with the marked cable bent. -/
theorem original_bent (d k : ℕ) (hk : 0<k) (hs : HomogeneousSchur d k k) (hb : HomogeneousSchur d (k+k) k) :
    let a : ℂ := (k+k).choose k
    let u := terminal (stack (M d k)) (symClasp d k)
    let v := terminal (stackedFine (P d k)) (symClasp d k)
    partialTranspose ((internal d k)ᴴ*original d k*internal d k) =
      (2:ℂ) • properSquares le_rfl (M d k) (symClasp d k) +
      a • properSquares (by omega) (fun _ : Unit => P d k) (symClasp d k) +
      Support.reflected (a • v-(1/2:ℂ) • u) - (9/4:ℂ) • Support.reflected u := by
  rw [original_corrected]
  exact canonical_raw d k hk hs hb

end
end BlockPermanents.ThreeGeneralOpen
