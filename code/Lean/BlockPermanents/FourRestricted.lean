import BlockPermanents.FourGram
import BlockPermanents.SupportCoordinates

/-! # Passing from a marked coordinate plane to an arbitrary PSD matrix -/
namespace BlockPermanents.FourRestricted
open FourTarget Closures MatchingThreshold
open scoped BigOperators
noncomputable section

theorem relabel {d k : ℕ} (σ : TransferBlocks.FourPerm) (x : Fin 4 → Fin k → Fin d → ℂ) :
    packets d k σ (flatPackets x) = flatPackets (x ∘ σ.symm) := by
  funext w
  simpa [packets,wires,act,Transfer.tensorAction,flatPackets,Function.comp_def] using
    Equiv.prod_comp σ (fun i => packet (x (σ.symm i)) (fun t => w (i,t)))

/-- A coordinate plane of the marked thickness suffices. Every conjugation
term may choose its own coordinates, as witnessed by the mixed Gram invariant. -/
theorem matrix_of_supported {k : ℕ}
    (positive : ∀ (d : ℕ) (x : Fin 4 → Fin k → Fin d → ℂ) (S : Finset (Fin d)),
      S.card = k → (∀ i j, j ∉ S → x 3 i j = 0) →
      0 ≤ (bracket (flatPackets x) (Q d k (flatPackets x))).re) : MarcusAt 4 k := by
  apply marcusAt_of_gram
  intro x
  have pos (y : Fin 4 → Fin k → Fin (4*k) → ℂ) :
      0 ≤ (bracket (flatPackets y) (Q (4*k) k (flatPackets y))).re := by
    obtain ⟨n,S,U,hS,hU,hs⟩ := SupportCoordinates.adapt (y 3)
    let z i t := U (y i t)
    have eqn : crossGram (Function.uncurry y) (Function.uncurry y) =
        crossGram (Function.uncurry z) (Function.uncurry z) := by
      funext i j
      exact (hU _ _).symm
    rw [FourGram.gram_invariant y z eqn]
    exact positive n z S hS hs
  have h := congrArg Complex.re (averaged_gap x)
  simp only [Complex.re_sum, Complex.mul_re, show (24:ℂ).re=24 by norm_num, show (24:ℂ).im=0 by norm_num,zero_mul,sub_zero,
    Complex.sub_re,relabel] at h
  have nn := Finset.sum_nonneg (s := (Finset.univ : Finset TransferBlocks.FourPerm))
    (fun σ _ => pos (x ∘ (σ⁻¹).symm))
  linarith

end
end BlockPermanents.FourRestricted
