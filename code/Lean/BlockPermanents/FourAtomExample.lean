import BlockPermanents.PairBound
import BlockPermanents.HomogeneousSchurProof

/-! The normalized four-atom packet and its three proper cuts in Example 2F.3. -/
namespace BlockPermanents.FourAtomExample
open Bend Closures PairBound
open scoped Matrix
noncomputable section

def atoms (i j : Fin 4) : ℂ := if j = i then 1 else 0

abbrev D := packet atoms

/-- A surviving word has all four different labels. -/
private def valid (v : Word 4 4) : ℕ :=
  if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 ∧ v 0 ≠ v 3 ∧ v 1 ≠ v 3 ∧ v 2 ≠ v 3 then 1 else 0

private theorem word_count :
    ∀ v : Word 4 4, (∑ p : Equiv.Perm (Fin 4), if ∀ i, v i = p i then 1 else 0) = valid v := by
  decide +kernel

theorem packet_entry (v : Word 4 4) : D v = packetScale (Fin 4) * (valid v : ℂ) := by
  rw [← word_count]
  simp only [D,packet,orderSum,pureWord,atoms,Function.comp_apply,Fintype.prod_boole,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp_all

private theorem scale_norm : packetScale (Fin 4) * star (packetScale (Fin 4)) = (24:ℂ)⁻¹ := by
  have h := scale_cancel (I := Fin 4)
  norm_num [Nat.factorial] at h
  change star (packetScale (Fin 4)) * packetScale (Fin 4) * 24 = 1 at h
  linear_combination h / 24

/-- Count the common ordered strings contracted between the two survivor words. -/
def completions (r : CutIndex 4 4) (u v : Word 4 (4-r)) : ℕ :=
  ∑ c : Word 4 r, valid (splitWords 4 4 r (u,c)) * valid (splitWords 4 4 r (v,c))

theorem cut_entry (r : CutIndex 4 4) (u v : Word 4 (4-r)) :
    cutMatrix D D r u v = (completions r u v : ℂ) / 24 := by
  rw [cutMatrix_entry (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)]
  simp only [packet_entry,star_mul',star_natCast,completions,Nat.cast_sum,Nat.cast_mul,
    div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [← scale_norm]
  ring

private def totalCount (r : CutIndex 4 4) :=
  ∑ u : Word 4 (4-r), ∑ v : Word 4 (4-r), completions r u v ^ 2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem count_squares : ∀ r : CutIndex 4 4, 0 < r.val → r.val < 4 →
    totalCount r * ((4 : ℕ).choose r.val) = 576 := by
  decide +kernel

/-- The proper caps have squared norms 1/4, 1/6 and 1/4. -/
theorem cut_energy (r : CutIndex 4 4) (hr : 0 < r.val) (hr' : r.val < 4) :
    energy ((wordCap 4 4 4 r).mulVec (product D (fun w => star (D w)))) =
      1 / ((4 : ℕ).choose r.val : ℝ) := by
  have hc : (totalCount r : ℝ) * ((4 : ℕ).choose r.val : ℝ) = 576 := by exact_mod_cast count_squares r hr hr'
  have hp : ((4 : ℕ).choose r.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (cut_le r)).ne'
  have he (u v : Word 4 (4-r)) : Complex.normSq (cutMatrix D D r u v) =
      (completions r u v : ℝ)^2 / 576 := by
    rw [cut_entry,Complex.normSq_div]
    simp [Complex.normSq_apply,sq]
    ring
  rw [← cut_frobenius]
  simp_rw [he]
  simp_rw [← Finset.sum_div]
  change _ / _ = _
  rw [div_eq_div_iff (by norm_num : (576:ℝ) ≠ 0) hp]
  simpa only [totalCount,Nat.cast_sum,Nat.cast_pow,one_mul] using hc

/-- The three individual rows of the two-block square certificate. -/
theorem proper_values :
    cutTerm D D 1 = 4 ∧ cutTerm D D 2 = 6 ∧ cutTerm D D 3 = 4 := by
  have eval (r : CutIndex 4 4) (h : 0 < r.val) (h' : r.val < 4) :
      cutTerm D D r = ((4 : ℕ).choose r.val : ℝ) := by
    have hn : ((4 : ℕ).choose r.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (cut_le r)).ne'
    rw [cutTerm,cut_energy r h h',weight,Nat.cast_mul]
    field_simp
  rw [eval 1 (by decide) (by decide),eval 2 (by decide) (by decide),eval 3 (by decide) (by decide)]
  norm_num [show (3:CutIndex 4 4).val=3 from rfl,Nat.choose]

theorem gap_fourteen :
    ((4+4).choose 4 : ℂ) * quadratic (totalClasp 4 4 4) (product D D) -
      ((energy D * energy D + Complex.normSq (∑ t, D t * star (D t)) : ℝ) : ℂ) = 14 := by
  have h := two_block_gap (d:=4) (by decide : 0 < 4)
    (SchurNormalization.homogeneousSchur_implies_unbent _ _ _ (SchurNormalization.homogeneousSchur _ _ _))
    (Bridges.packet_symmetric _ _ atoms) (Bridges.packet_symmetric _ _ atoms)
  have hcuts : properCuts 4 = {1,2,3} := by decide
  rw [h, hcuts]
  rw [Finset.sum_insert (by decide : (1:CutIndex 4 4) ∉ ({2,3} : Finset (CutIndex 4 4))),
    Finset.sum_insert (by decide : (2:CutIndex 4 4) ∉ ({3} : Finset (CutIndex 4 4))), Finset.sum_singleton,
    proper_values.1,proper_values.2.1,proper_values.2.2]
  norm_num

/-- The six unordered two-letter survivors in the displayed middle half. -/
abbrev Pair := ↥((Finset.univ : Finset (Fin 4)).powersetCard 2)
private def present (T : Pair) (u : Word 4 2) : ℕ :=
  if u 0 ≠ u 1 ∧ u 0 ∈ T.val ∧ u 1 ∈ T.val then 1 else 0

/-- The unit symmetric word on T, with coefficient 1/√2 at both orders. -/
def survivor (T : Pair) (u : Word 4 2) : ℂ := packetScale (Fin 2) * (present T u : ℂ)

private theorem short_scale : packetScale (Fin 2) * star (packetScale (Fin 2)) = (2:ℂ)⁻¹ := by
  have h := scale_cancel (I := Fin 2)
  norm_num [Nat.factorial] at h
  change star (packetScale (Fin 2)) * packetScale (Fin 2) * 2 = 1 at h
  linear_combination h/2

theorem six_survivors : Fintype.card Pair = 6 := by decide +kernel

theorem survivor_gram (T R : Pair) : bracket (survivor T) (survivor R) = if T=R then 1 else 0 := by
  have hc : ∀ T R : Pair, (∑ u : Word 4 2, present T u * present R u) = if T=R then 2 else 0 := by
    decide +kernel
  have h : ((∑ u : Word 4 2, present T u * present R u : ℕ) : ℂ) = if T=R then 2 else 0 := by
    exact_mod_cast hc T R
  have ht (u : Word 4 2) : star (survivor T u)*survivor R u =
      (present T u : ℂ)*present R u/2 := by
    simp only [survivor,star_mul',star_natCast,div_eq_mul_inv]
    rw [← short_scale]; ring
  unfold bracket
  simp_rw [starRingEnd_apply,ht,← Finset.sum_div,← Nat.cast_mul,← Nat.cast_sum,h]
  split_ifs <;> norm_num

/-- The actual middle cut is one sixth the sum of the six orthogonal line projectors. -/
theorem middle_matrix (u v : Word 4 2) :
    cutMatrix D D 2 u v = (∑ T : Pair, survivor T u * star (survivor T v)) / 6 := by
  have hc : ∀ u v : Word 4 2, completions 2 u v = 2*(∑ T : Pair, present T u * present T v) := by
    decide +kernel
  have ht (T : Pair) : survivor T u * star (survivor T v) = (present T u:ℂ) * present T v / 2 := by
    simp only [survivor,star_mul',star_natCast,div_eq_mul_inv]
    rw [← short_scale]; ring
  rw [cut_entry, hc]
  simp only [ht,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,← Finset.sum_div]
  ring

end
end BlockPermanents.FourAtomExample
