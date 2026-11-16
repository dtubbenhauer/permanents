import BlockPermanents.FiveProjection
import BlockPermanents.FiveFreeCoefficient
import BlockPermanents.PairResidualSquares
import BlockPermanents.BalancedCubicExterior

/-! Orthogonal trace-cup complements on each partial (2k,k) cut and the
remaining unit-vector test of its free k-cable. -/
namespace BlockPermanents.FiveFreeResidual
open Bend Closures PairBound ThreeSupport FiveProjection SchurNormalization
open scoped Matrix
noncomputable section

/-- The same cut order in the shorter square cable. -/
def pairedIndex {p k : ℕ} (r : CutIndex p k) : CutIndex k k :=
  ⟨r.val, by simpa only [min_self] using
    (Nat.lt_succ_of_le ((Nat.le_of_lt_succ r.isLt).trans (min_le_right ..)))⟩

/-- Project off the trace cup on the surviving marked letters, at a fixed free word. -/
def residual {d p k : ℕ} (h : k ≤ p) (P : Word d p → ℂ) (x : Fin k → Fin d → ℂ)
    (r : CutIndex p k) (t : Word d (p-k)) :=
  let W := PairResidual.space x (pairedIndex r)
  (SupportCup.J W).mulVec (SupportCup.coords W (longSlice h P (packet x) r t)ᴴ)

theorem long_resolution {d p k : ℕ} (h : k ≤ p) {P : Word d p → ℂ} (hP : Symmetric P)
    (x : Fin k → Fin d → ℂ) (hx : packet x ≠ 0) (r : CutIndex p k) :
    energy (longCut P (packet x) r) =
      (∑ t, energy (residual h P x r t)) +
      energy (longCut P (packet x) (longFull h)) / PairResidual.rank x (pairedIndex r) := by
  let G := packet x
  have hG : Symmetric G := Bridges.packet_symmetric _ _ x
  let W := PairResidual.space x (pairedIndex r)
  let A := longSlice h P G r
  have full : energy (longCut P G (longFull h)) =
      ∑ t, Complex.normSq (A t).trace := by
    unfold energy
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    change (∑ b : Word d (k-k), Complex.normSq (longCut P G (longFull h) (t,b))) = _
    dsimp only [A]
    simp_rw [longFull_entry hP hG h, longSlice_trace hP hG]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.sub_self,
      pow_zero, one_smul]
  have cut : energy (longCut P G r) = ∑ t, ∑ i, ∑ j, Complex.normSq ((A t) i j) := by
    unfold energy
    rw [Fintype.sum_prod_type, ← (freeSlots d h r).sum_comp, Fintype.sum_prod_type]
    rfl
  change energy (longCut P G r) = _ + energy (longCut P G (longFull h)) / _
  rw [cut, full, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have he := SupportCup.resolution W (PairResidual.rank_pos x hx (pairedIndex r)) (A t)ᴴ
    (longSlice_columns hP x h r t)
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj,
    Matrix.trace_conjTranspose] at he
  rw [Finset.sum_comm] at he
  exact he

/-- The excess full-cap coefficient on the actual span of the surviving subpackets. -/
def surplus {d p k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex p k) : ℝ :=
  (k.choose r : ℝ) / PairResidual.rank x (pairedIndex r) - 1

theorem surplus_nonneg {d p k : ℕ} (x : Fin k → Fin d → ℂ) (hx : packet x ≠ 0)
    (r : CutIndex p k) : 0 ≤ surplus x r := by
  apply sub_nonneg.mpr
  apply (le_div_iff₀ (by exact_mod_cast PairResidual.rank_pos x hx (pairedIndex r))).mpr
  rw [one_mul]
  exact_mod_cast PairResidual.rank_le x (pairedIndex r)

/-- Explicit squares discarded when retaining just one copy of the full
cut after multiplying its partial-cut energy by choose(k,r). -/
def cutRemainder {d p k : ℕ} (h : k ≤ p) (P : Word d p → ℂ) (x : Fin k → Fin d → ℂ)
    (r : CutIndex p k) : ℝ :=
  (k.choose r : ℝ) * (∑ t, energy (residual h P x r t)) +
    surplus x r * energy (longCut P (packet x) (longFull h))

theorem cut_squares {d p k : ℕ} (h : k ≤ p) {P : Word d p → ℂ} (hP : Symmetric P)
    (x : Fin k → Fin d → ℂ) (hx : packet x ≠ 0) (r : CutIndex p k) :
    (k.choose r : ℝ) * energy (longCut P (packet x) r) =
      energy (longCut P (packet x) (longFull h)) + cutRemainder h P x r := by
  rw [long_resolution h hP x hx r, cutRemainder,surplus]
  ring

theorem cutRemainder_nonneg {d p k : ℕ} (h : k ≤ p) (P : Word d p → ℂ)
    (x : Fin k → Fin d → ℂ) (hx : packet x ≠ 0) (r : CutIndex p k) :
    0 ≤ cutRemainder h P x r :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
    (mul_nonneg (surplus_nonneg x hx r) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))

/-- Projecting the full output onto the unit packet H leaves its exterior
square with H. This expands into squares of two-by-two coordinate minors. -/
theorem full_test_squares {d k : ℕ} (H F G : Word d k → ℂ) (hG : Symmetric G)
    (hu : energy H = 1) :
    let a := ((k+k).choose k : ℝ)
    let P := (symmetricProductMatrix H).mulVec F
    a^2 * energy (longCut P G (fiveFull k)) =
      Complex.normSq (pairGram H G F) +
        a^2 * BalancedCubicExterior.wedgeEnergy H (freeOutput P G) := by
  dsimp only
  let P := (symmetricProductMatrix H).mulVec F
  have hP := product_symmetric H F
  have he := BalancedCubicExterior.gram_determinant H (freeOutput P G)
  rw [hu, one_mul, free_energy hP hG, ← bracket_free H G hP] at he
  rw [pairGram, Complex.normSq_mul]
  have hc : Complex.normSq ((k+k).choose k : ℂ) = ((k+k).choose k : ℝ)^2 := by
    simp [Complex.normSq_apply, sq]
  rw [hc]
  change _ = _ * Complex.normSq (bracket _ P) + _ * _
  linear_combination (((k+k).choose k : ℝ)^2) * he

/-- Reindex the (2k,k) opening by the shorter length. -/
def index (k : ℕ) : Fin (k+1) ≃ CutIndex (k+k) k :=
  finCongr (by simp [min_eq_right (show k ≤ k+k by omega)])

def properRemainder {d k : ℕ} (P : Word d (k+k) → ℂ) (x : Fin k → Fin d → ℂ) : ℝ :=
  ∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ) * cutRemainder (by omega) P x (index k i.succ)

/-- All positive cuts of the triple separate into a multiple of the
full contraction and the weighted rank and perpendicular remainders. -/
theorem triple_opening {d k : ℕ} (F H : Word d k → ℂ) (x : Fin k → Fin d → ℂ)
    (hx : energy (packet x) = 1) :
    let a := ((k+k).choose k : ℝ)
    let P := (symmetricProductMatrix H).mulVec F
    tripleFine F H (packet x) = (pairGram H F F).re +
      FiveFreeCoefficient.coefficient k * (a^2 * energy (longCut P (packet x) (fiveFull k))) +
      a * properRemainder P x := by
  dsimp only
  let G := packet x
  let P := (symmetricProductMatrix H).mulVec F
  let a := ((k+k).choose k : ℝ)
  let ef := energy (longCut P G (fiveFull k))
  have hP : Symmetric P := product_symmetric H F
  have hG : Symmetric G := Bridges.packet_symmetric _ _ x
  have hn : packet x ≠ 0 := by intro e; simp [e,Bend.energy] at hx
  let E (i : Fin (k+1)) := energy (longCut P G (index k i))
  let Q (i : Fin k) := ((k+k).choose (i.val+1) : ℝ)
  have hz : E 0 = energy P := by
    have hzero := StraightCut.straight_energy hP hG
    change E 0 = energy P * energy G at hzero
    simpa only [show energy G = 1 from hx, mul_one] using hzero
  have hs (i : Fin k) :
      ((k.choose (i.val+1) : ℝ) * E i.succ) = ef + cutRemainder (by omega) P x (index k i.succ) :=
    cut_squares (by omega) hP x hn (index k i.succ)
  have heq : tripleFine F H G = a * (energy P + ∑ i : Fin k, Q i * ((k.choose (i.val+1):ℝ) * E i.succ)) := by
    rw [tripleFine, closed_bent_schur _ _ _ (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d (k+k) k)),
      Complex.re_sum, ← (index k).sum_comp, Fin.sum_univ_succ]
    change a * (_ + _) = _
    congr 1
    congr 1
    · change (((weight (k+k) k 0 : ℂ) * (E 0 : ℂ))).re = _
      simp [weight,hz]
    · apply Finset.sum_congr rfl
      intro i _
      change (((weight (k+k) k i.succ : ℂ) * (E i.succ : ℂ))).re = _
      simp [weight,Q, Complex.mul_re, mul_assoc]
  change tripleFine F H G = _ + _ * (a^2 * ef) + a * properRemainder P x
  rw [heq, pairGram_self_re]
  simp_rw [hs, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hsum : (∑ i, Q i) = FiveFreeCoefficient.coefficient k * a :=
    (FiveFreeCoefficient.coefficient_mul k).symm
  rw [hsum]
  dsimp only [properRemainder, P, Q, a]
  ring

/-- The residual after testing every positive cut with its exact coefficient. -/
def exactRemainder {d k : ℕ} (F H : Word d k → ℂ) (x : Fin k → Fin d → ℂ) : ℝ :=
  let P := (symmetricProductMatrix H).mulVec F
  let a := ((k+k).choose k : ℝ)
  FiveFreeCoefficient.coefficient k * a^2 *
    BalancedCubicExterior.wedgeEnergy H (freeOutput P (packet x)) +
    a * properRemainder P x

theorem testing_exact {d k : ℕ} (F H : Word d k → ℂ) (x : Fin k → Fin d → ℂ)
    (hu : energy H = 1) (hx : energy (packet x) = 1) :
    tripleFine F H (packet x) = (pairGram H F F).re +
      FiveFreeCoefficient.coefficient k * Complex.normSq (pairGram H (packet x) F) + exactRemainder F H x := by
  rw [triple_opening F H x hx, full_test_squares H F _ (Bridges.packet_symmetric _ _ x) hu]
  unfold exactRemainder
  ring

/-- The universal 41/20 estimate retains the two cut remainders and the
excess coefficient of the tested full-cap square. -/
def tripleRemainder {d k : ℕ} (F H : Word d k → ℂ) (x : Fin k → Fin d → ℂ) : ℝ :=
  exactRemainder F H x + (FiveFreeCoefficient.coefficient k - 41/20) * Complex.normSq (pairGram H (packet x) F)

theorem tripleRemainder_nonneg {d k : ℕ} (hk : 3 ≤ k) (F H : Word d k → ℂ)
    (x : Fin k → Fin d → ℂ) (hx : energy (packet x) = 1) : 0 ≤ tripleRemainder F H x := by
  have hn : packet x ≠ 0 := by intro e; simp [e,Bend.energy] at hx
  have hb := FiveFreeCoefficient.uniform hk
  have ha : 0 ≤ ((k+k).choose k : ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ properRemainder ((symmetricProductMatrix H).mulVec F) x := by
    apply Finset.sum_nonneg
    exact fun i _ => mul_nonneg (Nat.cast_nonneg _) (cutRemainder_nonneg (by omega) _ x hn _)
  unfold tripleRemainder exactRemainder
  apply add_nonneg _ (mul_nonneg (sub_nonneg.mpr hb) (Complex.normSq_nonneg _))
  apply add_nonneg _ (mul_nonneg ha hp)
  apply mul_nonneg (mul_nonneg (by linarith : 0 ≤ FiveFreeCoefficient.coefficient k) (sq_nonneg _))
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num)

theorem testing_free_cable_squares {d k : ℕ} (_hk : 3 ≤ k) (F H : Word d k → ℂ)
    (x : Fin k → Fin d → ℂ) (hu : energy H = 1) (hx : energy (packet x) = 1) :
    tripleFine F H (packet x) = (pairGram H F F).re +
      41/20 * Complex.normSq (pairGram H (packet x) F) + tripleRemainder F H x := by
  rw [testing_exact F H x hu hx]
  unfold tripleRemainder
  ring

end
end BlockPermanents.FiveFreeResidual
