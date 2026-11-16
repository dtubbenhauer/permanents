import BlockPermanents.ThreeGeneralRaw
import BlockPermanents.ThreeSupport
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace BlockPermanents.ThreeGeneralOpen
open Bend SchurNormalization ThreeSupport
open scoped BigOperators Matrix ComplexOrder
noncomputable section
variable {I J Z : Type*}

def earlySquares {d k : ℕ} (M : K d k → Matrix (K d k) I ℂ) (N : Matrix (K d k) J ℂ) :=
  ∑ r ∈ (middle k k le_rfl).erase (lastProper k), (weight k k r : ℂ) •
    ∑ s, Support.reflected (routed M N r s)

private theorem proper_last {d k : ℕ} (hk : 2≤k)
    (M : K d k → Matrix (K d k) I ℂ) (N : Matrix (K d k) J ℂ) :
    properSquares le_rfl M N = earlySquares M N + (k:ℂ)^2 •
      ∑ s, Support.reflected (routed M N (lastProper k) s) := by
  have h : lastProper k ∈ middle k k le_rfl := by
    simp only [middle,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor <;> intro e <;> have h := congrArg Fin.val e <;>
      change k-1 = _ at h <;> simp only [emptyCut,lastCut] at h <;> omega
  have hc : k.choose (k-1) = k := by
    rw [Nat.choose_symm (show 1≤k by omega),Nat.choose_one_right]
  unfold properSquares earlySquares
  rw [← Finset.sum_erase_add _ _ h]
  simp only [weight,lastProper,hc,Nat.cast_mul,pow_two]

/-- Regrouping the three-packet expansion at its final proper two-line cut. -/
theorem resolve_raw {d k s : ℕ} (hk : 2≤k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (hM : ∀ t i, Symmetric (fun w => M t w i))
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    [Fintype Z] (perp : Matrix Z (I×J) ℂ)
    (hcut : ∑ t, Support.reflected (routed M N (lastProper k) t) =
      Support.reflected perp + (s:ℂ)⁻¹ • Support.reflected (terminal (stack M) N)) :
    let a : ℂ := (k+k).choose k
    let v := terminal (stackedFine P) N
    let u := terminal (stack M) N
    partialTranspose (corrected M P N) =
      (2:ℂ) • earlySquares M N + a • properSquares (by omega) (fun _ : Unit => P) N +
      (2*(k:ℂ)^2) • Support.reflected perp + Support.reflected (a • v - (1/2:ℂ) • u) +
      (2*(k:ℂ)^2/s - 9/4) • Support.reflected u := by
  rw [general_raw (by omega) hsmall hbig M P N hM hP hN,proper_last hk,hcut]
  simp only [div_eq_mul_inv]
  module

private theorem psd_sum {A B : Type*} [Fintype A] (s : Finset B) (f : B → Matrix A A ℂ)
    (hf : ∀ b, (f b).PosSemidef) : (∑ b ∈ s, f b).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Matrix.PosSemidef.zero : (0 : Matrix A A ℂ).PosSemidef)
  | insert b s h ih => rw [Finset.sum_insert h];exact (hf b).add ih

private theorem psd_scale {A : Type*} [Fintype A] (c : ℝ) (hc : 0≤c)
    {M : Matrix A A ℂ} (hM : M.PosSemidef) : ((c:ℂ) • M).PosSemidef := by
  refine ⟨?_,?_⟩
  · change ((c:ℂ) • M)ᴴ = _
    rw [Matrix.conjTranspose_smul,hM.1.eq]
    simp
  · intro x
    rw [Matrix.smul_mulVec_assoc,dotProduct_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr hc) (hM.2 x)

private theorem psd_nat {A : Type*} [Fintype A] (n : ℕ) {M : Matrix A A ℂ}
    (hM : M.PosSemidef) : ((n:ℂ) • M).PosSemidef := by
  simpa only [Complex.ofReal_natCast] using psd_scale (n:ℝ) (Nat.cast_nonneg n) hM

/-- Every coefficient remaining in the supported decomposition is positive
or a binomial multiplicity, including the full-cap coefficient. -/
theorem resolved_psd {d k s : ℕ} [Fintype I] [Fintype J] (hk : 2≤k) (hs : 0<s) (hsk : s≤k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (hM : ∀ t i, Symmetric (fun w => M t w i))
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    [Fintype Z] (perp : Matrix Z (I×J) ℂ)
    (hcut : ∑ t, Support.reflected (routed M N (lastProper k) t) =
      Support.reflected perp + (s:ℂ)⁻¹ • Support.reflected (terminal (stack M) N)) :
    (partialTranspose (corrected M P N)).PosSemidef := by
  rw [resolve_raw hk hsmall hbig M P N hM hP hN perp hcut]
  have left : (earlySquares M N).PosSemidef :=
    psd_sum _ _ fun r => psd_nat _ (psd_sum _ _ fun t => Matrix.posSemidef_conjTranspose_mul_self _)
  have right : (properSquares (show k≤k+k by omega) (fun _ : Unit => P) N).PosSemidef :=
    psd_sum _ _ fun r => psd_nat _ (psd_sum _ _ fun t => Matrix.posSemidef_conjTranspose_mul_self _)
  have hpos := Support.three_full_cap_weight k s hk hs hsk
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · apply Matrix.PosSemidef.add
      · exact (psd_nat 2 left).add (psd_nat _ right)
      · exact_mod_cast psd_nat (2*k^2) (Matrix.posSemidef_conjTranspose_mul_self perp)
    · exact Matrix.posSemidef_conjTranspose_mul_self _
  · convert psd_scale _ hpos.le (Matrix.posSemidef_conjTranspose_mul_self (terminal (stack M) N)) using 1
    push_cast
    rfl

end
end BlockPermanents.ThreeGeneralOpen
