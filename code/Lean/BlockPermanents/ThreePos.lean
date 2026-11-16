import BlockPermanents.ThreeWire
import BlockPermanents.ThreeSupport

/-! # Positive closures in the six-wire quadratic certificate

On the upright side the two packets can carry an arbitrary joint tensor.
Exchanging a subset of the marked packet with the upright side then gives
the square of the corresponding partial contraction. No independence of
the upright packets is used in this assertion.
-/
namespace BlockPermanents.ThreePos
open ThreeWire Bend Closures PairBound
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

abbrev W (d : ℕ) := Word d 2

/-- Put three two-letter words into their contiguous positions. -/
def tripleWords (d : ℕ) : W d × W d × W d ≃ Word d 6 where
  toFun u := ![u.1 0,u.1 1,u.2.1 0,u.2.1 1,u.2.2 0,u.2.2 1]
  invFun w := (![w 0,w 1], ![w 2,w 3], ![w 4,w 5])
  left_inv := by
    rintro ⟨u,v,h⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv w := by funext i; fin_cases i <;> rfl

/-- One contraction across the mark leaves a spectator and two through words. -/
abbrev CutCoordinates (d : ℕ) (r : CutIndex 2 2) :=
  ((W d × Word d (2-r)) × Word d (2-r)) × (Word d r × Word d r)

def cutWords (d : ℕ) (r : CutIndex 2 2) : CutCoordinates d r ≃ Word d 6 where
  toFun q := tripleWords d
    (q.1.1.1, splitWords d 2 r (q.1.1.2,q.2.1), splitWords d 2 r (q.1.2,q.2.2))
  invFun w :=
    let u := (tripleWords d).symm w
    let a := (splitWords d 2 r).symm u.2.1
    let b := (splitWords d 2 r).symm u.2.2
    (((u.1,a.1),b.1),(a.2,b.2))
  left_inv q := by simp
  right_inv w := by simp

/-- Lift an arbitrary upright two-packet tensor across a product with the mark. -/
def markedProduct {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ) (w : Word d 6) :=
  let u := (tripleWords d).symm w
  U u.1 u.2.1 * H u.2.2

def contracted {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ)
    (r : CutIndex 2 2) (t : W d) (a b : Word d (2-r)) : ℂ :=
  ∑ j : Word d r, U t (splitWords d 2 r (a,j)) * star (H (splitWords d 2 r (b,j)))

private theorem marked_at {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ)
    (r : CutIndex 2 2) (q : CutCoordinates d r) :
    markedProduct U H (cutWords d r q) =
      U q.1.1.1 (splitWords d 2 r (q.1.1.2,q.2.1)) * H (splitWords d 2 r (q.1.2,q.2.2)) := by
  simp [markedProduct, cutWords]

/-- Closing an exchange of r ordinary slots against the marked packet. -/
theorem exchange_square {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ)
    (r : CutIndex 2 2) (s : Wire)
    (hs : ∀ q : CutCoordinates d r, (cutWords d r q) ∘ s = cutWords d r (q.1,q.2.swap)) :
    evaluateWord (markedProduct U H) s =
      ∑ t, ∑ a, ∑ b, (Complex.normSq (contracted U H r t a b) : ℂ) := by
  unfold evaluateWord bracket
  rw [← (cutWords d r).sum_comp (fun w => (starRingEnd ℂ) (markedProduct U H w) *
    markedProduct U H (w ∘ s))]
  simp only [hs, marked_at, Fintype.sum_prod_type, Prod.swap_prod_mk]
  simp only [contracted, Complex.normSq_eq_conj_mul_self, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum, Complex.star_def, Complex.conj_conj]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  ring

abbrev half : CutIndex 2 2 := ⟨1, by decide⟩
abbrev full : CutIndex 2 2 := ⟨2, by decide⟩

theorem thin_action (d : ℕ) (q : CutCoordinates d half) :
    (cutWords d half q) ∘ thinSwap = cutWords d half (q.1,q.2.swap) := by
  funext i; fin_cases i <;> rfl

theorem full_action (d : ℕ) (q : CutCoordinates d full) :
    (cutWords d full q) ∘ fullSwap = cutWords d full (q.1,q.2.swap) := by
  funext i; fin_cases i <;> rfl

theorem exchange_nonneg {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ)
    (r : CutIndex 2 2) (s : Wire) (hs : ∀ q : CutCoordinates d r,
      (cutWords d r q) ∘ s = cutWords d r (q.1,q.2.swap)) :
    0 ≤ (evaluateWord (markedProduct U H) s).re := by
  rw [exchange_square U H r s hs]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)))

/-- Sum of the two possible orders of the upright packets, without dividing by two. -/
def pairTensor {d : ℕ} (F G : W d → ℂ) (t v : W d) := F t * G v + G t * F v

private theorem half_twolines {d : ℕ} (F G H : W d → ℂ)
    (hF : Bend.Symmetric F) (hG : Bend.Symmetric G) (hH : Bend.Symmetric H)
    (t : W d) (a b : Word d (2 - (half : ℕ))) :
    contracted (pairTensor F G) H half t a b = 2 * ThreeSupport.partialThree F G H half t a b := by
  simp only [contracted, pairTensor, ThreeSupport.partialThree, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, cutMatrix_entry hG hH, cutMatrix_entry hF hH, Finset.mul_sum, add_mul,
    Finset.sum_add_distrib]
  rw [← mul_assoc, show (2:ℂ)*(1/2) = 1 by norm_num, one_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem join_full {d : ℕ} (a : Word d (2-(full:ℕ))) (t : Word d full) :
    splitWords d 2 full (a,t) = t := by funext i; fin_cases i <;> rfl

private theorem full_twolines {d : ℕ} (F G H : W d → ℂ) (t : W d) (a b : Word d (2-(full:ℕ))) :
    contracted (pairTensor F G) H full t a b = 2 * ThreeSupport.fullThree F G H t := by
  simp only [contracted, pairTensor, join_full, ThreeSupport.fullThree, bracket, Finset.mul_sum,
    add_mul, Finset.sum_add_distrib]
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℂ) ≠ 0)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;> rw [join_full a r, join_full b r] <;> simp [Complex.star_def] <;> ring

private theorem ofReal_exchange_square {d : ℕ} (U : W d → W d → ℂ) (H : W d → ℂ)
    (r : CutIndex 2 2) (s : Wire)
    (hs : ∀ q : CutCoordinates d r, (cutWords d r q) ∘ s = cutWords d r (q.1,q.2.swap)) :
    (evaluateWord (markedProduct U H) s).re =
      ∑ t, ∑ a, ∑ b, Complex.normSq (contracted U H r t a b) := by
  rw [exchange_square _ _ _ _ hs]
  simp only [Complex.re_sum, Complex.ofReal_re]

/-- The coefficient 8 from the proper single cap absorbs the 9/4 full-cap defect. -/
theorem pair_absorbs_full {d : ℕ} (F G : W d → ℂ) (x : Fin 2 → Fin d → ℂ)
    (hF : Bend.Symmetric F) (hG : Bend.Symmetric G) :
    0 ≤ 8 * (evaluateWord (markedProduct (pairTensor F G) (packet x)) thinSwap).re -
      (9/4 : ℝ) * (evaluateWord (markedProduct (pairTensor F G) (packet x)) fullSwap).re := by
  rw [ofReal_exchange_square _ _ half _ (thin_action d), ofReal_exchange_square _ _ full _ (full_action d)]
  simp only [half_twolines _ _ _ hF hG (Bridges.packet_symmetric _ _ _), full_twolines,
    Complex.normSq_mul]
  have hn : Complex.normSq (2:ℂ) = 4 := by norm_num
  rw [hn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  norm_num only [show 2 - (full:ℕ) = 0 from rfl, pow_zero, one_smul]
  simp only [← Finset.mul_sum]
  have h := ThreeSupport.last_weight_nonnegative (d := d) (k := 2) (by decide) hF hG x
  change 0 ≤ 2*(2:ℝ)^2 * (∑ t, ∑ a, ∑ b, Complex.normSq (ThreeSupport.partialThree F G (packet x) half t a b)) -
    9/4 * (∑ t, Complex.normSq (ThreeSupport.fullThree F G (packet x) t)) at h
  linarith only [h]

end
end BlockPermanents.ThreePos
