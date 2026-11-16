import BlockPermanents.FiveMean
import BlockPermanents.FiveMixed

/-! The two averages in the proof after (five-trace). The roles G,F,H,I,J
occupy slots 0,1,2,3,4. In the weighted average both spectator slots stay fixed. -/
namespace BlockPermanents.FiveAverage
open scoped BigOperators ComplexOrder
open FiveCycles
noncomputable section

abbrev Forms := Fin 5 → Matrix (Fin 5) (Fin 5) ℂ

def residual (Y T : Forms) (σ : S) : ℝ :=
  (T (σ 2) (σ 1) (σ 1)).re +
    2 * (star (Y (σ 2) (σ 0) (σ 1)) * T (σ 2) (σ 0) (σ 1)).re

private theorem trace_nonneg {q : ℕ} {Y T : Matrix (Fin q) (Fin q) ℂ}
    (hY : Y.PosSemidef) (hT : T.PosSemidef) (hd : ∀ i, (Y i i).re ≤ (q-1:ℝ)/2) :
    0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ((T i i).re + 2 * (star (Y j i)*T j i).re) := by
  have h := FiveMixed.mixed_trace hY.transpose hT.transpose
  apply le_trans _ h
  apply Finset.sum_nonneg
  intro i _
  have ht := hT.re_dotProduct_nonneg (Pi.single i 1)
  have hdiag : 0 ≤ (T i i).re := by
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one, single_dotProduct, one_mul] using ht
  have hy : (star (Y i i)*T i i).re = (Y i i).re*(T i i).re := by
    nth_rw 1 [← hY.isHermitian.coe_re_apply_self i]
    simp [Complex.mul_re]
  change 0 ≤ ((Fintype.card (Fin q) : ℝ) - 1) * (T i i).re - 2 * (star (Y i i)*T i i).re
  rw [hy, Fintype.card_fin]
  nlinarith only [mul_nonneg (by linarith [hd i] : 0 ≤ (q-1:ℝ)-2*(Y i i).re) hdiag]

private theorem avg_finset_sum {I : Type*} (s : Finset I) (f : I → S → ℝ) :
    avg (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, avg (f i) := by
  simp only [avg, ← Finset.sum_div]
  rw [Finset.sum_comm]

private theorem orbit {q : ℕ} (hq : 2 ≤ q) (idx : Fin q → Fin 5) (Y T : Forms)
    (hY : ∀ h, (Y h).PosSemidef) (hT : ∀ h, (T h).PosSemidef)
    (hd : ∀ h i, (Y h i i).re ≤ (q-1:ℝ)/2)
    (w : S → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (move : ∀ i j : Fin q, i ≠ j → ∃ τ : S,
      τ 0 = idx j ∧ τ 1 = idx i ∧ τ 2 = 2 ∧ ∀ σ : S, w (σ*τ) = w σ) :
    0 ≤ avg (fun σ => w σ * residual Y T σ) := by
  let term (i j : Fin q) (σ : S) :=
    w σ * ((T (σ 2) (σ (idx i)) (σ (idx i))).re +
      2 * (star (Y (σ 2) (σ (idx j)) (σ (idx i)))*T (σ 2) (σ (idx j)) (σ (idx i))).re)
  have point (σ : S) : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, term i j σ := by
    have h := trace_nonneg ((hY (σ 2)).submatrix (σ ∘ idx)) ((hT (σ 2)).submatrix (σ ∘ idx))
      (fun i => hd (σ 2) (σ (idx i)))
    convert mul_nonneg (hw σ) h using 1
    simp only [Finset.mul_sum]
    rfl
  have hm (i j : Fin q) (hij : j ∈ Finset.univ.erase i) :
      avg (term i j) = avg (fun σ => w σ * residual Y T σ) := by
    obtain ⟨τ,h0,h1,h2,hwτ⟩ := move i j (Finset.ne_of_mem_erase hij).symm
    rw [← avg_relabel τ (fun σ => w σ * residual Y T σ)]
    congr 1
    funext σ
    simp only [term, residual, hwτ, Equiv.Perm.mul_apply, h0, h1, h2]
  have hp := avg_mono point
  rw [avg_const, avg_sum] at hp
  simp_rw [avg_finset_sum] at hp
  have row (i : Fin q) : (∑ j ∈ Finset.univ.erase i, avg (term i j)) =
      (q-1 : ℕ) * avg (fun σ => w σ * residual Y T σ) := by
    rw [Finset.sum_congr rfl (fun j hj => hm i j hj)]
    simp [Finset.card_erase_of_mem, nsmul_eq_mul]
  simp only [row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpq : (0 : ℝ) < (q-1:ℕ) := by exact_mod_cast (by omega : 0 < q-1)
  exact (mul_nonneg_iff_of_pos_left hpq).mp ((mul_nonneg_iff_of_pos_left hqpos).mp hp)

private def moveSlots (a b : Fin 5) : S :=
  Equiv.swap ((Equiv.swap 0 a) 1) b * Equiv.swap 0 a

private def four : Fin 4 → Fin 5 := ![0,1,3,4]

private theorem four_move : ∀ i j : Fin 4, i ≠ j →
    let τ := moveSlots (four j) (four i)
    τ 0 = four j ∧ τ 1 = four i ∧ τ 2 = 2 := by decide

private def two : Fin 2 → Fin 5 := ![0,1]

private theorem two_move : ∀ i j : Fin 2, i ≠ j →
    let τ := moveSlots (two j) (two i)
    τ 0 = two j ∧ τ 1 = two i ∧ τ 2 = 2 ∧ τ 3 = 3 ∧ τ 4 = 4 := by decide

/-- Holding H fixed leaves four choices for either of the ordered mixed exits. -/
theorem plain (Y T : Forms) (hY : ∀ h, (Y h).PosSemidef) (hT : ∀ h, (T h).PosSemidef)
    (hd : ∀ h i, (Y h i i).re ≤ 3/2) : 0 ≤ avg (fun σ => residual Y T σ) := by
  have h := orbit (by decide : 2 ≤ 4) four Y T hY hT (by norm_num; exact hd)
    (fun _ => 1) (fun _ => by norm_num) (by
      intro i j hij
      obtain ⟨h0,h1,h2⟩ := four_move i j hij
      exact ⟨_,h0,h1,h2,fun _ => rfl⟩)
  simpa using h

/-- Holding H,I,J fixed leaves the two mixed exits. Their common spectator
weight can be any nonnegative function of the ordered spectator pair. -/
theorem weighted (Y T : Forms) (hY : ∀ h, (Y h).PosSemidef) (hT : ∀ h, (T h).PosSemidef)
    (hd : ∀ h i, (Y h i i).re ≤ 1/2) (w : Fin 5 → Fin 5 → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    0 ≤ avg (fun σ => w (σ 3) (σ 4) * residual Y T σ) := by
  apply orbit (by decide : 2 ≤ 2) two Y T hY hT (by norm_num; exact hd) _ (fun σ => hw _ _)
  intro i j hij
  obtain ⟨h0,h1,h2,h3,h4⟩ := two_move i j hij
  exact ⟨_,h0,h1,h2,fun σ => by simp only [Equiv.Perm.mul_apply, h3, h4]⟩

end
end BlockPermanents.FiveAverage
