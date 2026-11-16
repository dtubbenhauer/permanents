import BlockPermanents.PairBound
import BlockPermanents.HomogeneousSchurProof

/-! # The orthogonal two-letter equality example following Lemma 7A.1 -/
namespace BlockPermanents.PairResidualExample
open Bend Closures PairBound SchurNormalization
open scoped BigOperators Matrix
noncomputable section

/-- The two coordinate vectors of the marked packet in ℂ². -/
def atoms (i j : Fin 2) : ℂ := if j = i then 1 else 0

abbrev F := packet atoms
abbrev middle : CutIndex 2 2 := 1

/-- Expanded normalized symmetric packet on two arbitrary atoms. -/
theorem two_packet_entry {d : ℕ} (x : Fin 2 → Fin d → ℂ) (w : Word d 2) :
    packet x w = packetScale (Fin 2) * (x 0 (w 0) * x 1 (w 1) + x 1 (w 0) * x 0 (w 1)) := by
  classical
  have perms : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide +kernel
  simp only [packet, orderSum, perms, Finset.sum_insert (by decide :
    (1 : Equiv.Perm (Fin 2)) ∉ {Equiv.swap (0 : Fin 2) 1}), Finset.sum_singleton,
    pureWord, Fin.prod_univ_two, Function.comp_apply, Equiv.Perm.one_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- This packet has coefficient 1/√2 on each of the words ef and fe. -/
theorem packet_entry (w : Word 2 2) :
    F w = if w 0 = w 1 then 0 else packetScale (Fin 2) := by
  rw [F, two_packet_entry]
  simp only [atoms]
  generalize w 0 = i
  generalize w 1 = j
  fin_cases i <;> fin_cases j <;> simp

private theorem scale_sq :
    packetScale (Fin 2) * star (packetScale (Fin 2)) = (2 : ℂ)⁻¹ := by
  have h := scale_cancel (I := Fin 2)
  norm_num [Nat.factorial] at h
  change star (packetScale (Fin 2)) * packetScale (Fin 2) * 2 = 1 at h
  linear_combination h / 2

private theorem split_zero (a t : Word 2 1) :
    splitWords 2 2 middle (a,t) 0 = a 0 := rfl

private theorem split_one (a t : Word 2 1) :
    splitWords 2 2 middle (a,t) 1 = t 0 := rfl

/-- The one-cap half on the surviving single-letter words is half the identity. -/
theorem middle_matrix :
    cutMatrix F F middle = (2 : ℂ)⁻¹ • (1 : Matrix (Word 2 1) (Word 2 1) ℂ) := by
  apply Matrix.ext
  intro (a : Word 2 1) (b : Word 2 1)
  rw [cutMatrix_entry (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)]
  simp_rw [packet_entry, split_zero, split_one]
  let e := Equiv.funUnique (Fin 1) (Fin 2)
  let f (t : Word 2 1) := (if a 0 = t 0 then 0 else packetScale (Fin 2)) *
    star (if b 0 = t 0 then 0 else packetScale (Fin 2))
  change ∑ t : Word 2 1, f t = _
  rw [← e.symm.sum_comp f]
  simp only [Fin.sum_univ_two]
  change (if a 0 = 0 then 0 else _) * star (if b 0 = 0 then 0 else _) +
      (if a 0 = 1 then 0 else _) * star (if b 0 = 1 then 0 else _) = _
  have hab : a = b ↔ a 0 = b 0 := e.injective.eq_iff.symm
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hab]
  generalize a 0 = i
  generalize b 0 = j
  fin_cases i <;> fin_cases j <;> simp <;> exact scale_sq

theorem middle_trace : (cutMatrix F F middle).trace = 1 := by
  rw [middle_matrix, Matrix.trace_smul, Matrix.trace_one]
  norm_num [Fintype.card_fun]

theorem middle_energy :
    energy ((wordCap 2 2 2 middle).mulVec (product F (fun i => star (F i)))) = 1/2 := by
  rw [← cut_frobenius, middle_matrix]
  simp [Matrix.one_apply, apply_ite Complex.normSq, Complex.normSq_mul, Complex.normSq_inv, Fintype.card_fun]

private theorem unit_pairing : bracket F F = 1 := by
  calc
    _ = (cutMatrix F F middle).trace := by
      rw [cut_trace (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)]
      simp [bracket, mul_comm]
    _ = 1 := middle_trace

theorem unit_energy : energy F = 1 := by
  have h := unit_pairing
  rw [Coarse.bracket_self] at h
  exact_mod_cast h

/-- Straight, one-cap and double-cap contributions of the actual open cuts. -/
theorem cut_values : cutTerm F F (zeroCut 2) = 1 ∧
    cutTerm F F middle = 2 ∧ cutTerm F F (fullCut 2) = 1 := by
  have hs := Bridges.packet_symmetric 2 2 atoms
  have tr := cut_trace hs hs middle
  rw [middle_trace] at tr
  constructor
  · rw [cutTerm, zero_cap_energy hs hs, unit_energy]; norm_num [weight, zeroCut]
  constructor
  · rw [cutTerm, middle_energy]; norm_num [weight, middle, Nat.choose]
  · rw [cutTerm, full_cap_energy hs hs, ← tr]; norm_num [weight, fullCut]

/-- The symmetric product evaluates to four in the units of Lemma 7A.1. -/
theorem equality_four :
    ((Nat.choose 4 2 : ℝ) * energy ((symmetricProductMatrix F).mulVec F)) = 4 := by
  have h := congrArg Complex.re (closed_bent_schur 2 2 2
    (homogeneousSchur_implies_unbent 2 2 2 (homogeneousSchur 2 2 2)) F F)
  rw [product_quadratic_energy] at h
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at h
  change _ = ∑ r : Fin 3, cutTerm F F r at h
  rw [Fin.sum_univ_three] at h
  rw [show (0 : CutIndex 2 2) = zeroCut 2 from rfl, show (2 : CutIndex 2 2) = fullCut 2 from rfl,
    cut_values.1, cut_values.2.1, cut_values.2.2] at h
  linarith

end
end BlockPermanents.PairResidualExample
