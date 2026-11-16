import BlockPermanents.BalancedLastTrace
import BlockPermanents.CubicSquares
import BlockPermanents.PairResidualSquares
import BlockPermanents.HomogeneousSchurProof

/-! The complementary squares on an opposed cubic edge, and their total under
reversal of the bend. -/
namespace BlockPermanents.BalancedCubicTau
open Closures Bend CubicSquares SchurNormalization MatchingFine
open scoped Matrix
noncomputable section

variable {d : ℕ}

/-- Regard the supported packet as the column index of the balanced cut. -/
def boundary (F H : Word d 3 → ℂ) : Matrix (Word d 3) (Word d 3) ℂ :=
  fun i j => star (H i) * F j

/-- The perpendicular component on the chosen plane for one proper cut. -/
def half (U : Matrix (Fin d) (Fin 3) ℂ) (F H : Word d 3 → ℂ) (r : CutIndex 3 3) :=
  BalancedLastTrace.residual (PairBound.cut_le r) U (boundary F H)

private theorem norm_pair (F H : Word d 3 → ℂ) :
    Complex.normSq (∑ t, F t * star (H t)) = Complex.normSq (bracket F H) := by
  have he : (∑ t, F t * star (H t)) = (starRingEnd ℂ) (bracket F H) := by
    simp [bracket, map_sum, mul_comm, Complex.star_def]
  rw [he,Complex.normSq_conj]

private theorem cut_split (U : Matrix (Fin d) (Fin 3) ℂ) (hU : Uᴴ * U = 1)
    {F H : Word d 3 → ℂ} (hF : Symmetric F) (hH : Symmetric H)
    (hplane : F ∈ BalancedSupport.space 3 U) (r : CutIndex 3 3) :
    cutTerm F H r = (weight 3 3 r : ℝ) *
      (energy (half U F H r) + Complex.normSq (bracket F H) /
        ((3+(3-r.val)-1).choose (3-r.val) : ℝ)) := by
  have hs (w) : boundary F H w ∈ BalancedSupport.space 3 U :=
    Submodule.smul_mem _ (star (H w)) hplane
  have hr := BalancedLastTrace.resolution (by decide : 0 < 3) (PairBound.cut_le r) U hU
    (boundary F H) hs
  have hc (w v) : BalancedTrace.cutMatrix (PairBound.cut_le r) (boundary F H) w v =
      PairBound.cutMatrix F H r v w := by
    rw [PairBound.cutMatrix_entry hF hH]
    unfold BalancedTrace.cutMatrix boundary
    apply Finset.sum_congr rfl
    intro c _
    exact mul_comm _ _
  have ht : Complex.normSq (boundary F H).trace = Complex.normSq (bracket F H) := by
    simpa only [Matrix.trace, Matrix.diag_apply,boundary, mul_comm] using norm_pair F H
  simp only [hc,ht] at hr
  rw [Finset.sum_comm, PairBound.cut_frobenius] at hr
  exact congrArg ((weight 3 3 r : ℝ) * ·) hr

private theorem two_cuts (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (i j : Fin 4) :
    let F := packet (x i)
    let H := packet (x j)
    tau x i j = cutTerm F H 1 + cutTerm F H 2 - 9/2 * Complex.normSq (bracket F H) := by
  let y : Fin 2 → Fin 3 → Fin d → ℂ := ![x i,x j]
  have he := congrArg Complex.re (two_block_gap (by decide : 0 < 3)
    (homogeneousSchur_implies_unbent d 3 3 (homogeneousSchur d 3 3))
    (Bridges.packet_symmetric d 3 (y 0)) (Bridges.packet_symmetric d 3 (y 1)))
  rw [Bridges.two_fine_permanent y, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re,
    show properCuts 3 = ({1,2} : Finset (CutIndex 3 3)) by decide,
    Finset.sum_pair (by decide)] at he
  change pairFine x i j - (energy (packet (x i)) * energy (packet (x j)) + _) = _ at he
  rw [h i,h j,norm_pair] at he
  dsimp only
  unfold tau BalancedCut.sq
  change pairFine x i j - (1 + _ * Complex.normSq (bracket (packet (x i)) (packet (x j)))) = _
  change pairFine x i j - (1*1 + Complex.normSq (bracket (packet (x i)) (packet (x j)))) = cutTerm (packet (x i)) (packet (x j)) 1 + cutTerm (packet (x i)) (packet (x j)) 2 at he
  linarith

/-- With a fixed three-plane, the cubic edge slack is exactly the reflected
sum of the two proper-cut residuals. The bubbles are six and three. -/
theorem tau_squares (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (i j : Fin 4)
    (U : Matrix (Fin d) (Fin 3) ℂ) (hU : Uᴴ * U = 1)
    (hs : packet (x i) ∈ BalancedSupport.space 3 U) :
    tau x i j = 9 * energy (half U (packet (x i)) (packet (x j)) 1) +
      9 * energy (half U (packet (x i)) (packet (x j)) 2) := by
  have hcut := cut_split U hU (Bridges.packet_symmetric d 3 (x i))
    (Bridges.packet_symmetric d 3 (x j)) hs
  rw [two_cuts x h i j,hcut 1,hcut 2]
  norm_num [weight,Nat.choose]; ring

/-- In the smaller span of the actual surviving products, extra copies of the
full-cap square account for the difference from the three-plane bubble. -/
def rankCorrection (x : Fin 3 → Fin d → ℂ) (r : CutIndex 3 3) : ℝ :=
  9 / (PairResidual.rank x r : ℝ) - 9 / ((3+(3-r.val)-1).choose (3-r.val) : ℝ)

theorem correction_nonneg (x : Fin 3 → Fin d → ℂ) (hx : packet x ≠ 0)
    {r : CutIndex 3 3} (hr : r = 1 ∨ r = 2) : 0 ≤ rankCorrection x r := by
  have hp := PairResidual.rank_pos x hx r
  have hb := PairResidual.rank_le x r
  have hd : PairResidual.rank x r ≤ (3+(3-r.val)-1).choose (3-r.val) := by
    rcases hr with rfl | rfl <;> norm_num [Nat.choose] at * <;> omega
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_left (by norm_num)
  · exact_mod_cast hp
  · exact_mod_cast hd

/-- The same remainder on the intrinsic surviving packet spans, valid in
every Gram dimension, even when the three atoms are dependent. -/
theorem tau_packet_spans (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (i j : Fin 4) :
    let a := x i
    let H := packet (x j)
    tau x i j = 9 * energy (PairResidual.residual 1 a H 1) +
      9 * energy (PairResidual.residual 1 a H 2) +
      (rankCorrection a 1 + rankCorrection a 2) * Complex.normSq (bracket (packet a) H) := by
  have hc : PairResidual.scaled 1 (x i) = packet (x i) := by
    funext w; exact one_mul _
  have hx : packet (x i) ≠ 0 :=
    PairResidual.packet_ne_zero_of_unit (a:=1) (x:=x i) (by rw [hc,h])
  have he (r : CutIndex 3 3) := PairResidual.cut_resolution 1 (x i)
    (Bridges.packet_symmetric d 3 (x j)) r (PairResidual.rank_pos _ hx r)
  simp only [hc] at he
  dsimp only
  rw [two_cuts x h i j, he 1, he 2]
  norm_num [rankCorrection,Nat.choose]
  ring

open private sq_flip from BlockPermanents.BalancedCut in
/-- Reversing the bend preserves the sum of complementary squares, including
when the two packets were put in different three-planes. -/
theorem tau_swap (x : Fin 4 → Fin 3 → Fin d → ℂ) (i j : Fin 4) :
    tau x i j = tau x j i := by
  unfold tau
  rw [sq_flip (fun a => packet (x a)) i j]
  congr 1
  let e := (Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.refl (Fin 3))
  let f := Function.uncurry (![x j,x i] : Fin 2 → Fin 3 → Fin d → ℂ)
  have he : Function.uncurry (![x i,x j] : Fin 2 → Fin 3 → Fin d → ℂ) = f ∘ e := by
    funext ⟨a,b⟩
    fin_cases a <;> simp [f,e,Function.comp_def, Function.uncurry, Equiv.swap_apply_def]
  exact (congrArg fine he).trans (fine_reindex e f)

end
end BlockPermanents.BalancedCubicTau
