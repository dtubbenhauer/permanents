import BlockPermanents.CycleMatching
import BlockPermanents.TwoStepLocalSquares

/-! Multiplying the two-step resolution by disjoint spectator caps before
averaging gives the matching multiplicities used in the odd-cycle cut. -/
namespace BlockPermanents.TwoStepSpectator
open Closures Matchings CycleMatching
noncomputable section

variable {m : ℕ} {P : Type*} [Fintype P]

/-- The local diagonals at one middle and at two ordered distinct middles
add one and two edges to the spectator matching, respectively. -/
theorem count_extensions (g : Gram m) (e : P × Fin 2 ↪ Fin m)
    (i j : Fin m) (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    (U : Finset (Fin m)) (hU : ∀ v ∈ U, i ≠ v ∧ j ≠ v ∧ v ∉ Set.range e) :
    average m (fun σ => prefixWeight g e σ *
      ((∑ v ∈ U, sqEdge g (σ i) (σ v)) +
        ∑ v ∈ U, ∑ w ∈ U.erase v, sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j))) =
      (U.card : ℝ)*Z g (Fintype.card P+1) +
        (U.card : ℝ)*(U.card-1)*Z g (Fintype.card P+2) := by
  have single (v) (hv : v ∈ U) : average m (fun σ =>
      prefixWeight g e σ * sqEdge g (σ i) (σ v)) = Z g (Fintype.card P+1) := by
    simpa only [mul_comm] using mean_extension g e i v (hU v hv).1 hi (hU v hv).2.2
  have row (v) (hv : v ∈ U) :
      (∑ w ∈ U.erase v, average m (fun σ => prefixWeight g e σ *
        (sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j)))) =
      (U.card-1 : ℝ)*Z g (Fintype.card P+2) := by
    have distinct (w) (hw : w ∈ U.erase v) :
        average m (fun σ => prefixWeight g e σ * (sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j))) =
          Z g (Fintype.card P+2) := by
      have hvw := (Finset.ne_of_mem_erase hw).symm
      obtain ⟨hiw,hjw,hw'⟩ := hU w (Finset.mem_of_mem_erase hw)
      obtain ⟨hiv,hjv,hv'⟩ := hU v hv
      exact mean_two_edges g e hij hvw hiv hiw hjv hjw hi hj hv' hw'
    rw [Finset.sum_congr rfl distinct, Finset.sum_const, Finset.card_erase_of_mem hv, nsmul_eq_mul,
      Nat.cast_sub (Finset.card_pos.mpr ⟨v,hv⟩)]
    simp
  simp_rw [mul_add, Finset.mul_sum, average_add, average_sum]
  rw [Finset.sum_congr rfl single, Finset.sum_congr rfl row]
  simp [nsmul_eq_mul, mul_assoc]

variable {D : Type*} [Fintype D]

/-- The spectator caps multiply every local exterior and opposite-edge square. -/
def remainder (x : Fin m → D → ℂ) (e : P × Fin 2 ↪ Fin m)
    (i j : Fin m) (U : Finset (Fin m)) : ℝ :=
  average m (fun σ => prefixWeight (crossGram x x) e σ *
    TwoStepSquares.remainder (x ∘ σ) U i j)

theorem remainder_nonneg (x : Fin m → D → ℂ) (e : P × Fin 2 ↪ Fin m)
    (i j : Fin m) (U : Finset (Fin m)) : 0 ≤ remainder x e i j U :=
  mul_nonneg (by positivity : 0 ≤ (m.factorial : ℝ)⁻¹) (Finset.sum_nonneg fun σ _ =>
    mul_nonneg (prefix_nonneg _ _ _) (TwoStepSquares.remainder_nonneg (x ∘ σ) U i j))

/-- Exact spectator version of the path bound, valid also when the set
of available middles is empty or contains a single label. -/
theorem path_squares (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (e : P × Fin 2 ↪ Fin m) (i j : Fin m)
    (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    (U : Finset (Fin m)) (hU : ∀ v ∈ U, i ≠ v ∧ j ≠ v ∧ v ∉ Set.range e) :
    let g := crossGram x x
    (U.card : ℝ)*Z g (Fintype.card P+1) + (U.card : ℝ)*(U.card-1)*Z g (Fintype.card P+2) =
      average m (fun σ => prefixWeight g e σ * Complex.normSq (∑ v ∈ U, via g i j v σ)) +
        remainder x e i j U := by
  dsimp only
  let g := crossGram x x
  rw [← count_extensions g e i j hij hi hj U hU, remainder, ← average_add]
  apply congrArg (average m)
  funext σ
  have h := TwoStepSquares.local_squares (x ∘ σ) (fun a => unit _) U i j
  change (∑ v ∈ U, sqEdge g (σ i) (σ v)) +
      (∑ v ∈ U, ∑ w ∈ U.erase v, sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j)) -
      Complex.normSq (∑ v ∈ U, via g i j v σ) = TwoStepSquares.remainder (x ∘ σ) U i j at h
  rw [sub_eq_iff_eq_add.mp h, mul_add]
  ring

end
end BlockPermanents.TwoStepSpectator
