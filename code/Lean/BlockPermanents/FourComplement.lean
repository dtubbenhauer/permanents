import BlockPermanents.FourCapAction

/-! # Cancellation on the complementary spectator space in Section 5D -/
namespace BlockPermanents.FourComplement
open Bend FourRoutes FourCapAction Closures PairBound
open scoped BigOperators Matrix
noncomputable section

abbrev S (d : ℕ) := Spectator d 2 1
abbrev W (d : ℕ) := Word d 1
def properHalf {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (s : S d) :
    Matrix (W d) (W d) ℂ := fun a b =>
  (capHalf d 2 1 (by decide) 1 s).mulVec (product F (fun v => star (H v))) (a,b)
def complete {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (s : S d) :=
  (capHalf d 2 1 (by decide) (fullCut 2) s).mulVec (product F (fun v => star (H v)))
    (Fin.elim0,Fin.elim0)

private lemma partial_eq {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (s : S d) :
    properHalf F H s = cutMatrix ((merge d 2 1 (by decide) s).mulVec F) H 1 := by
  ext a b
  simp only [properHalf,capHalf,route,← Matrix.mulVec_mulVec,upright_product,cutMatrix]

theorem partial_trace {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Bend.Symmetric H) (s : S d) :
    (properHalf F H s).trace = complete F H s := by
  rw [partial_eq,cut_trace (merge_symmetric _ F s) hH]
  simp only [complete,capHalf,route,← Matrix.mulVec_mulVec,upright_product,
    full_cap (merge_symmetric _ F s) hH]

private lemma partial_cols {d : ℕ} (F : Triple d 2 → ℂ) (x : Fin 2 → Fin d → ℂ)
    (s : S d) (b : W d) : (fun a => (properHalf F (packet x) s)ᴴ a b) ∈
      PacketSupport.splitSupport x 1 (by decide) := by
  rw [partial_eq,ThreeSupport.cut_adjoint (merge_symmetric _ F s) (Bridges.packet_symmetric _ _ _)]
  exact cut_columns_mem x (merge_symmetric _ F s) 1 b

/-- Every linear combination of spectator outputs has the same marked
two-dimensional column support. This includes each row of the complementary
four-strand clasp, without requiring a choice of basis for the marked plane. -/
theorem spectator_row {d : ℕ} (F : Triple d 2 → ℂ) (x : Fin 2 → Fin d → ℂ) (L : S d → ℂ) :
    Complex.normSq (∑ s, L s * complete F (packet x) s) ≤
      2 * ∑ i, ∑ j, Complex.normSq (∑ s, L s * properHalf F (packet x) s i j) := by
  classical
  let M := ∑ s, L s • properHalf F (packet x) s
  let V := PacketSupport.splitSupport x 1 (by decide)
  have cols (b : W d) : (fun a => Mᴴ a b) ∈ V := by
    have he : (fun a => Mᴴ a b) = ∑ s, star (L s) • (fun a => (properHalf F (packet x) s)ᴴ a b) := by
      funext a
      simp [M,Matrix.conjTranspose_apply,Matrix.sum_apply]
    rw [he]
    exact V.sum_mem (fun s _ => V.smul_mem _ (partial_cols F x s b))
  have h := ThreeSupport.trace_of_adjoint_columns V M cols
  have htrace : M.trace = ∑ s, L s * complete F (packet x) s := by
    simp [M, Matrix.trace_sum, Matrix.trace_smul,partial_trace F _ (Bridges.packet_symmetric _ _ _)]
  rw [htrace] at h
  have hdim : (Module.finrank ℂ V : ℝ) ≤ 2 := by
    exact_mod_cast PacketSupport.splitSupport_dimension x 1 (by decide)
  refine h.trans ?_
  simp only [M, Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hdim (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- The complementary contribution in (5D) is nonnegative. Its variables
are the actual U₁ and u cut matrices obtained by bending the marked packet. -/
theorem spectator_cancellation {d : ℕ} (F : Triple d 2 → ℂ) (x : Fin 2 → Fin d → ℂ)
    (P : Matrix (S d) (S d) ℂ) :
    0 ≤ 24 * (∑ t, ∑ i, ∑ j, Complex.normSq
      (∑ s, (1-P) t s * properHalf F (packet x) s i j)) -
      12 * (∑ t, Complex.normSq (∑ s, (1-P) t s * complete F (packet x) s)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => spectator_row F x ((1-P) t))
  rw [← Finset.mul_sum] at h
  linarith only [h]

end
end BlockPermanents.FourComplement
