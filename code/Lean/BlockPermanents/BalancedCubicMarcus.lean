import BlockPermanents.BalancedCubicFine
import BlockPermanents.BalancedCubicTau
import BlockPermanents.BalancedLastEnvelope

/-! Positivity of the cubic 37/4 certificate gives the four-block permanent
inequality on arbitrary positive semidefinite input. Each cubic edge slack
is extracted on a physical three-plane containing that packet's atoms. -/
namespace BlockPermanents.BalancedCubicMarcus
open Closures Bend CubicSquares MatchingFine

private theorem en {I : Type*} [Fintype I] (f : I → ℂ) : 0 ≤ energy f :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem proper_nonneg {d : ℕ} (hd : 3 ≤ d) (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) : 0 ≤ properSquares x := by
  have ht (i j : Fin 4) : 0 ≤ tau x i j := by
    obtain ⟨U,hU,hs⟩ := BalancedLast.exists_packet_frame hd (x i)
    rw [BalancedCubicTau.tau_squares x h i j U hU hs]
    exact add_nonneg (mul_nonneg (by norm_num) (en _)) (mul_nonneg (by norm_num) (en _))
  have hf (i j : Fin 4) : 0 ≤ 1 + 11/2 * BalancedCut.sq (fun a => packet (x a)) i j :=
    add_nonneg zero_le_one (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  exact add_nonneg (add_nonneg (mul_nonneg (ht _ _) (hf _ _)) (mul_nonneg (ht _ _) (hf _ _)))
    (mul_nonneg (ht _ _) (ht _ _))

/-- Evaluate all four terms of the signed 37/4 identity on unit packets. -/
theorem unit {d : ℕ} (hd : 3 ≤ d) (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      fine (Function.uncurry x) := by
  let X := fun i => packet (x i)
  let g := crossGram X X
  have cert := cubic_identity x h
  change 3 * (fine (Function.uncurry x) - g.permanent.re) = _ at cert
  have fine_terms := fun p => BalancedCubicFine.fine_remainder x (division p)
  simp_rw [fine_terms] at cert
  have hf := Finset.sum_nonneg (s := Finset.univ) (fun (p : Fin 3) _ =>
    BalancedCubicFine.squares_nonneg (x ∘ division p))
  have hp := Finset.sum_nonneg (s := Finset.univ) (fun (p : Fin 3) _ =>
    proper_nonneg hd (x ∘ division p) (fun i => h _))
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun (p : Fin 3) _ =>
    signedSquares_nonneg (X ∘ division p) (fun i => h _))
  have hm : 0 ≤ FourTrade.matchings g := by
    simp only [FourTrade.matchings, Complex.normSq_eq_norm_sq]
    positivity
  change g.permanent.re ≤ _
  linarith only [cert,hf,hp,hs,hm]

/-- Theorem 6C.3 on all four-block PSD matrices of common thickness three. -/
theorem marcus : MarcusAt 4 3 :=
  MatchingThreshold.marcusAt_of_gram (PacketScale.remove_unit (by decide) (unit (by decide)))

end BlockPermanents.BalancedCubicMarcus
