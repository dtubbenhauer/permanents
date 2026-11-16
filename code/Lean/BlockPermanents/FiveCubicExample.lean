import BlockPermanents.PairBound

/-! Direct evaluation of the orthogonal cubic packet in Example 8A.2. -/
namespace BlockPermanents.FiveCubicExample
open Bend Closures PairBound
open scoped Matrix
noncomputable section

def atoms (i j : Fin 3) : ℂ := if j = i then 1 else 0

abbrev D := packet atoms

/-- A surviving word has all three different labels. -/
private def valid (v : Word 3 3) : ℕ :=
  if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 then 1 else 0

private theorem word_count :
    ∀ v : Word 3 3, (∑ p : Equiv.Perm (Fin 3), if ∀ i, v i = p i then 1 else 0) = valid v := by
  decide +kernel

theorem packet_entry (v : Word 3 3) : D v = packetScale (Fin 3) * (valid v : ℂ) := by
  rw [← word_count]
  simp only [D,packet,orderSum,pureWord,atoms,Function.comp_apply,Fintype.prod_boole,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp_all

private theorem scale_norm : packetScale (Fin 3) * star (packetScale (Fin 3)) = (6:ℂ)⁻¹ := by
  have h := scale_cancel (I := Fin 3)
  norm_num [Nat.factorial] at h
  change star (packetScale (Fin 3)) * packetScale (Fin 3) * 6 = 1 at h
  linear_combination h / 6

/-- Count the common ordered strings contracted between the two survivor words. -/
def completions (r : CutIndex 3 3) (u v : Word 3 (3-r)) : ℕ :=
  ∑ c : Word 3 r, valid (splitWords 3 3 r (u,c)) * valid (splitWords 3 3 r (v,c))

theorem cut_entry (r : CutIndex 3 3) (u v : Word 3 (3-r)) :
    cutMatrix D D r u v = (completions r u v : ℂ) / 6 := by
  rw [cutMatrix_entry (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)]
  simp only [packet_entry,star_mul',star_natCast,completions,Nat.cast_sum,Nat.cast_mul,
    div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [← scale_norm]
  ring

private def totalCount (r : CutIndex 3 3) :=
  ∑ u : Word 3 (3-r), ∑ v : Word 3 (3-r), completions r u v ^ 2

private theorem count_squares : ∀ r : CutIndex 3 3, totalCount r * ((3 : ℕ).choose r.val) = 36 := by
  decide +kernel

/-- The four actual cap energies are 1, 1/3, 1/3 and 1. -/
theorem cut_energy (r : CutIndex 3 3) :
    energy ((wordCap 3 3 3 r).mulVec (product D (fun w => star (D w)))) =
      1 / ((3 : ℕ).choose r.val : ℝ) := by
  have hc : (totalCount r : ℝ) * ((3 : ℕ).choose r.val : ℝ) = 36 := by exact_mod_cast count_squares r
  have hp : ((3 : ℕ).choose r.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (cut_le r)).ne'
  have he (u v : Word 3 (3-r)) : Complex.normSq (cutMatrix D D r u v) =
      (completions r u v : ℝ)^2 / 36 := by
    rw [cut_entry,Complex.normSq_div]
    simp [Complex.normSq_apply,sq]
    ring
  rw [← cut_frobenius]
  simp_rw [he]
  simp_rw [← Finset.sum_div]
  change _ / _ = _
  rw [div_eq_div_iff (by norm_num : (36:ℝ) ≠ 0) hp]
  simpa only [totalCount,Nat.cast_sum,Nat.cast_pow,one_mul] using hc

theorem packet_unit : energy D = 1 := by
  have h := cut_energy (zeroCut 3)
  rw [zero_cap_energy (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _)] at h
  simp only [zeroCut,Nat.choose_zero_right,Nat.cast_one,div_one] at h
  have hpos : 0 ≤ energy D := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  nlinarith

/-- The normalized symmetric two-letter vector [ij], indexed by its omitted letter. -/
def survivor (c : Fin 3) : Word 3 2 → ℂ := packet (fun i : Fin 2 => atoms (c.succAbove i))

private def short (c : Fin 3) (u : Word 3 2) := valid (splitWords 3 3 1 (u,fun _ => c))

private theorem short_count : ∀ (c : Fin 3) (u : Word 3 2),
    (∑ p : Equiv.Perm (Fin 2), if ∀ i, u i = c.succAbove (p i) then 1 else 0) = short c u := by
  decide +kernel

private theorem short_entry (c : Fin 3) (u : Word 3 2) :
    survivor c u = packetScale (Fin 2) * (short c u : ℂ) := by
  rw [← short_count]
  simp only [survivor,packet,orderSum,pureWord,atoms,Function.comp_apply,Fintype.prod_boole,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl; intro p _; split_ifs <;> simp_all

/-- After fixing the single letter, the two-letter slice is its complementary
symmetric packet with the common coefficient 1/√3. -/
theorem one_two_split (u : Word 3 2) (c : Fin 3) :
    D (splitWords 3 3 1 (u,fun _ => c)) = (Real.sqrt 3 : ℂ)⁻¹ * survivor c u := by
  have h : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : 0 ≤ (3:ℝ))]
    norm_num
  have hs : packetScale (Fin 3) = (Real.sqrt 3 : ℂ)⁻¹ * packetScale (Fin 2) := by
    simp only [packetScale,Fintype.card_fin]
    norm_num [Nat.factorial] at *
    rw [h]
    push_cast
    ring
  rw [packet_entry,short_entry,hs,mul_assoc]
  rfl

private theorem short_scale : packetScale (Fin 2) * star (packetScale (Fin 2)) = (2:ℂ)⁻¹ := by
  have h := scale_cancel (I := Fin 2)
  norm_num [Nat.factorial] at h
  change star (packetScale (Fin 2)) * packetScale (Fin 2) * 2 = 1 at h
  linear_combination h / 2

/-- The three survivor vectors form an orthonormal family. -/
theorem survivor_gram (c d : Fin 3) :
    bracket (survivor c) (survivor d) = if c = d then 1 else 0 := by
  have hcount : ∀ c d : Fin 3, (∑ u : Word 3 2, short c u * short d u) =
      if c = d then 2 else 0 := by decide +kernel
  have term (u : Word 3 2) : (starRingEnd ℂ) (survivor c u) * survivor d u =
      (short c u * short d u : ℕ) / (2:ℂ) := by
    simp only [short_entry,starRingEnd_apply,star_mul',star_natCast,Nat.cast_mul,div_eq_mul_inv]
    rw [← short_scale]; ring
  simp only [bracket,term,← Finset.sum_div,← Nat.cast_sum]
  rw [hcount]
  split_ifs <;> norm_num

/-- The one-cap diagram is a third of the sum of the three survivor projections. -/
theorem one_cap (u v : Word 3 2) : cutMatrix D D 1 u v =
    (∑ c : Fin 3, survivor c u * star (survivor c v)) / 3 := by
  have hcount : ∀ u v : Word 3 2, completions 1 u v = ∑ c, short c u * short c v := by
    decide +kernel
  have term (c : Fin 3) : survivor c u * star (survivor c v) =
      (short c u * short c v : ℕ) / (2:ℂ) := by
    simp only [short_entry,star_mul',star_natCast,Nat.cast_mul,div_eq_mul_inv]
    rw [← short_scale]; ring
  rw [cut_entry,hcount]
  simp only [term,← Finset.sum_div,← Nat.cast_sum]
  ring

theorem pair_cuts : (∑ r : CutIndex 3 3, cutTerm D D r) = 8 := by
  simp only [cutTerm,cut_energy]
  change (∑ r : Fin 4, _) = 8
  norm_num [Fin.sum_univ_succ,weight,Nat.choose]

/-- Expand both disjoint pairs, leaving the fifth packet to close straight. -/
theorem disjoint_pairs :
    (∑ r : CutIndex 3 3, ∑ t : CutIndex 3 3, cutTerm D D r * cutTerm D D t * energy D) = 64 := by
  simp only [packet_unit,mul_one,← Finset.mul_sum,pair_cuts,← Finset.sum_mul]
  norm_num

theorem coarse_five :
    (crossGram (fun _ : Fin 5 => D) (fun _ : Fin 5 => D)).permanent = 120 := by
  simp [Matrix.permanent,crossGram,Coarse.bracket_self,packet_unit,Fintype.card_perm,Nat.factorial]

end
end BlockPermanents.FiveCubicExample
