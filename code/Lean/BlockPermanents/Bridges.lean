import BlockPermanents.Bend
import BlockPermanents.Closures
import BlockPermanents.Coarse
import BlockPermanents.Statement
import Mathlib.Tactic.FinCases

/-! # Passing between matrix entries and symmetric word coordinates -/
namespace BlockPermanents.Bridges
open scoped BigOperators ComplexOrder
open Closures Bend
noncomputable section

/-- The permutation-matrix average acts by the word-coordinate clasp. -/
theorem symClasp_action (d k : ℕ) (v : Word d k → ℂ) :
    (symClasp d k).mulVec v = clasp v := by
  classical
  funext w
  simp only [symClasp, Matrix.mulVec, dotProduct, clasp, Fintype.card_fin, sumSlots,
    mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have h (y : Word d k) : w = y ∘ p ↔ w ∘ p.symm = y := by
    constructor
    · rintro rfl
      ext t
      simp
    · rintro rfl
      ext t
      simp
  simp_rw [h]
  simp [ite_mul]

/-- Matrix packets have symmetric boundary, including repeated input vectors. -/
theorem packet_symmetric (d k : ℕ) (x : Fin k → Fin d → ℂ) : Symmetric (packet x) := by
  rw [Bend.Symmetric, symClasp_action]
  have h (p : Equiv.Perm (Fin k)) (w : Word d k) :
      orderSum x (w ∘ p.symm) = orderSum x w := by
    unfold orderSum
    simp_rw [pure_reindex]
    exact (Group.mulRight_bijective p).sum_comp (fun τ => pureWord (x ∘ τ) w)
  funext w
  unfold clasp sumSlots packet
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  have hk : ((Fintype.card (Fin k)).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

private def twoSlots (k : ℕ) : Fin 2 × Fin k ≃ Fin (k+k) where
  toFun a := if a.1 = 0 then Fin.castAdd k a.2 else Fin.natAdd k a.2
  invFun := Fin.addCases (fun i => (0,i)) (fun i => (1,i))
  left_inv := by
    rintro ⟨i,j⟩
    fin_cases i <;> simp [-Fin.natAdd_eq_addNat]
  right_inv := by
    intro t
    refine Fin.addCases (fun i => ?_) (fun i => ?_) t <;> simp [-Fin.natAdd_eq_addNat]

def joinWords (d k : ℕ) : Word d k × Word d k ≃ Word d (k+k) where
  toFun u := Fin.append u.1 u.2
  invFun w := (fun t => w (Fin.castAdd k t), fun t => w (Fin.natAdd k t))
  left_inv u := by simp [-Fin.natAdd_eq_addNat]
  right_inv w := Fin.append_castAdd_natAdd

theorem clasp_transport {I J D : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (z : (I → D) → ℂ) (w : J → D) :
    clasp (fun u => z (u ∘ e)) w = clasp z (w ∘ e) := by
  unfold clasp sumSlots
  rw [Fintype.card_congr e]
  congr 1
  symm
  apply Fintype.sum_equiv e.permCongr
  intro p
  congr 1
  ext i
  simp [Equiv.permCongr_def]

theorem quadratic_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix J J ℂ) (v : J → ℂ) :
    quadratic (fun i j => A (e i) (e j)) (v ∘ e) = quadratic A v := by
  unfold quadratic
  apply Fintype.sum_equiv e
  intro i
  exact e.sum_comp (fun j => star (v (e i)) * A (e i) j * v j)

theorem quadratic_bracket {I : Type*} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) :
    quadratic A v = bracket v (A.mulVec v) := by
  simp only [quadratic, bracket, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rfl

theorem bracket_transport {I J D : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype D] (e : I ≃ J) (z : (I → D) → ℂ) :
    bracket (fun u => z (u ∘ e)) (clasp (fun u => z (u ∘ e))) = bracket z (clasp z) := by
  unfold bracket
  simp only [clasp_transport]
  exact (e.symm.arrowCongr (Equiv.refl D)).sum_comp (fun w => (starRingEnd ℂ) (z w) * clasp z w)

private theorem flat_in_joined_word {d k : ℕ} (x : Fin 2 → Fin k → Fin d → ℂ)
    (u : Word d k × Word d k) :
    flatPackets x ((joinWords d k u) ∘ twoSlots k) = product (packet (x 0)) (packet (x 1)) u := by
  simp [flatPackets, Fin.prod_univ_two, -Fin.natAdd_eq_addNat, product, joinWords, twoSlots, Function.comp_def]

/-- For two arbitrary matrix packets, the normalized fine quadratic form is
the permanent of the full Gram matrix in the `Fin 2 × Fin k` slot ordering. -/
theorem two_fine_permanent {d k : ℕ} (x : Fin 2 → Fin k → Fin d → ℂ) :
    ((k+k).choose k : ℂ) * quadratic (totalClasp d k k)
      (product (packet (x 0)) (packet (x 1))) =
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent := by
  let z := fun w : Word d (k+k) => flatPackets x (w ∘ twoSlots k)
  have h : product (packet (x 0)) (packet (x 1)) = z ∘ joinWords d k :=
    funext (fun u => (flat_in_joined_word x u).symm)
  have q := quadratic_reindex (joinWords d k) (symClasp d (k+k)) z
  change quadratic (totalClasp d k k) _ = _ at q
  rw [h, q, quadratic_bracket, symClasp_action]
  change _ * bracket (fun w => flatPackets x (w ∘ twoSlots k))
    (clasp (fun w => flatPackets x (w ∘ twoSlots k))) = _
  rw [bracket_transport, ← bracket_clasp]
  have hf := fine_closure x x
  simp only [Fintype.card_fin, two_mul] at hf
  rw [← hf]
  congr 1
  apply (eq_div_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))).mpr
  rw [pow_two, ← mul_assoc]
  exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k k

/-- For two blocks of any positive thickness the actual permanent gap
is the sum of the proper-cut squares, using only the cited unbent Schur relation. -/
theorem two_block_gram_gap {d k : ℕ} (hk : 0 < k) (schur : UnbentSchur d k k)
    (x : Fin 2 → Fin k → Fin d → ℂ) :
    (crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
      (Matrix.of (fun i j => (crossGram (x i) (x j)).permanent)).permanent =
      ((∑ r ∈ properCuts k, cutTerm (packet (x 0)) (packet (x 1)) r : ℝ) : ℂ) := by
  rw [← two_fine_permanent, Coarse.two_packet_permanent]
  exact two_block_gap hk schur (packet_symmetric _ _ _) (packet_symmetric _ _ _)

/-- The two-block permanent gap is a nonnegative real for every complex
Hermitian PSD input, including singular matrices. The dimension in the
unbent Schur input is the number of columns. -/
theorem two_block_psd_gap {k : ℕ} (hk : 0 < k) (schur : UnbentSchur (k+k) k k)
    (A : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℂ) (hA : A.PosSemidef) :
    ∃ s : ℝ, 0 ≤ s ∧ A.permanent - (blockPermanentMatrix A).permanent = (s : ℂ) := by
  obtain ⟨B,hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  let x (i : Fin 2) (t : Fin k) (r : Fin (k+k)) := B ((twoSlots k).symm r) (i,t)
  have h : A = crossGram (Function.uncurry x) (Function.uncurry x) := by
    rw [hB]
    ext a b
    change (∑ j, star (B j a) * B j b) = ∑ r, star (B ((twoSlots k).symm r) a) * B ((twoSlots k).symm r) b
    exact ((twoSlots k).symm.sum_comp (fun j => star (B j a) * B j b)).symm
  rw [h]
  refine ⟨_, Finset.sum_nonneg (s := properCuts k) (fun r _ => cutTerm_nonneg (packet (x 0)) (packet (x 1)) r), ?_⟩
  exact two_block_gram_gap hk schur x

/-- The two-block instance of the matrix inequality for every positive thickness. -/
theorem two_block_psd_inequality {k : ℕ} (hk : 0 < k) (schur : UnbentSchur (k+k) k k)
    (A : Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℂ) (hA : A.PosSemidef) :
    (blockPermanentMatrix A).permanent.re ≤ A.permanent.re := by
  obtain ⟨s, hs, h⟩ := two_block_psd_gap hk schur A hA
  have he := congrArg Complex.re h
  rw [Complex.sub_re, Complex.ofReal_re] at he
  exact sub_nonneg.mp (he ▸ hs)

/-- The two-packet case in the shared statement of the manuscript's matrix theorem. -/
theorem marcus_two {k : ℕ} (hk : 0 < k) (schur : UnbentSchur (k+k) k k) :
    MarcusAt 2 k := two_block_psd_gap hk schur

end
end BlockPermanents.Bridges
