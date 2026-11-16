import BlockPermanents.FiveSupport
import BlockPermanents.FiveNumbers
import BlockPermanents.PairSquares
import BlockPermanents.StraightCut

/-! # Testing the free cable of a triple against its shared packet

All products, brackets and caps act on finite word coordinates. -/

namespace BlockPermanents.FiveProjection
open Bend Closures PairBound ThreeSupport
open scoped BigOperators Matrix ComplexOrder
noncomputable section

def pairGram {d k : ℕ} (H G F : Word d k → ℂ) : ℂ :=
  ((k+k).choose k : ℂ) * bracket ((symmetricProductMatrix H).mulVec G)
    ((symmetricProductMatrix H).mulVec F)

/-- The fine closure with the two successive symmetric merges grouped as (H,F),G. -/
def tripleFine {d k : ℕ} (F H G : Word d k → ℂ) : ℝ :=
  ((k+k).choose k : ℝ) * ((((k+k)+k).choose (k+k) : ℂ) *
    quadratic (totalClasp d (k+k) k) (product ((symmetricProductMatrix H).mulVec F) G)).re

/-- The k free ordinary slots after completing all marked pairs. -/
def freeOutput {d k : ℕ} (P : Word d (k+k) → ℂ) (G : Word d k → ℂ) (t : Word d k) : ℂ :=
  ∑ w, P (Fin.append t w) * star (G w)

theorem bracket_free {d k : ℕ} (H G : Word d k → ℂ) {P : Word d (k+k) → ℂ} (hP : Symmetric P) :
    bracket ((symmetricProductMatrix H).mulVec G) P = bracket H (freeOutput P G) := by
  rw [symmetricProductMatrix_action]
  have he : clasp P = P := (Bridges.symClasp_action _ _ P).symm.trans hP
  let z := fun w : Word d (k+k) => H (fun t => w (Fin.castAdd k t)) * G (fun t => w (Fin.natAdd k t))
  change bracket (clasp z) P = _
  calc
    _ = bracket z P := by rw [← he, bracket_clasp]
    _ = _ := by
      unfold bracket
      rw [← (Fin.appendEquiv k k).sum_comp (fun u => (starRingEnd ℂ) (z u) * P u),
        Fintype.sum_prod_type]
      simp only [z, Fin.appendEquiv_apply, Fin.append_left, Fin.append_right, freeOutput,
        map_mul, Finset.mul_sum, mul_assoc, mul_comm (P _)]
      rfl

theorem free_energy {d k : ℕ} {P : Word d (k+k) → ℂ} {G : Word d k → ℂ}
    (hP : Symmetric P) (hG : Symmetric G) :
    energy (freeOutput P G) = energy (longCut P G (fiveFull k)) := by
  let h : k+k-k=k := Nat.add_sub_cancel k k
  let e : Word d (k+k-k) ≃ Word d k := (finCongr h).arrowCongr (Equiv.refl _)
  unfold energy
  rw [Fintype.sum_prod_type, ← e.sum_comp (fun t => Complex.normSq (freeOutput P G t))]
  apply Finset.sum_congr rfl
  intro t _
  change _ = ∑ b : Word d (k-k), Complex.normSq (longCut P G (longFull _) (t,b))
  simp_rw [longFull_entry hP hG]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.sub_self,
    pow_zero, one_smul]
  congr 1
  unfold freeOutput
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  change Fin.append (t ∘ Fin.cast h.symm) w = Fin.append t w ∘ Fin.cast _
  rw [Fin.append_cast_left]

theorem bracket_bound {I : Type*} [Fintype I] (H V : I → ℂ) :
    Complex.normSq (bracket H V) ≤ energy H * energy V := by
  let x : EuclideanSpace ℂ I := (WithLp.equiv 2 _).symm H
  let y : EuclideanSpace ℂ I := (WithLp.equiv 2 _).symm V
  have he : @inner ℂ _ _ x y = bracket H V := by
    simp [x, y, EuclideanSpace.inner_piLp_equiv_symm, dotProduct, bracket, mul_comm]
  have hv := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_inner_le_norm (𝕜 := ℂ) x y)
  rw [he, mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at hv
  simpa only [energy, Complex.normSq_eq_norm_sq] using hv

theorem product_symmetric {d k : ℕ} (H F : Word d k → ℂ) :
    Symmetric ((symmetricProductMatrix H).mulVec F) := by
  rw [symmetricProductMatrix, ← Matrix.mulVec_mulVec]
  apply projected_symmetric

/-- Test the last positive cable on a unit packet. The right side is the
squared norm of the concrete full cap with its spectator slots retained. -/
theorem full_test {d k : ℕ} (H F G : Word d k → ℂ) (hG : Symmetric G) (hu : energy H = 1) :
    Complex.normSq (pairGram H G F) ≤ ((k+k).choose k : ℝ)^2 *
      energy (longCut ((symmetricProductMatrix H).mulVec F) G (fiveFull k)) := by
  let P := (symmetricProductMatrix H).mulVec F
  have hP : Symmetric P := product_symmetric H F
  have hb := bracket_bound H (freeOutput P G)
  rw [hu, one_mul, free_energy hP hG, ← bracket_free H G hP] at hb
  unfold pairGram
  rw [Complex.normSq_mul]
  have hc : Complex.normSq ((k+k).choose k : ℂ) = ((k+k).choose k : ℝ)^2 := by
    simp [Complex.normSq_apply, sq]
  rw [hc]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

theorem pairGram_self_re {d k : ℕ} (H F : Word d k → ℂ) :
    (pairGram H F F).re = ((k+k).choose k : ℝ) * energy ((symmetricProductMatrix H).mulVec F) := by
  simp [pairGram, Coarse.bracket_self, Complex.mul_re]

/-- Sum all fine cuts on the triple, testing the last free cable against H.
The bound only requires the positive packet H to have norm one. F can be
any word tensor, and the marked G is a unit matrix packet. -/
theorem testing_free_cable {d k : ℕ} (hk : 3 ≤ k)
    (schur : SchurNormalization.HomogeneousSchur d (k+k) k)
    (F H : Word d k → ℂ) (x : Fin k → Fin d → ℂ) (hu : energy H = 1)
    (hx : energy (packet x) = 1) :
    (pairGram H F F).re + 41/20 * Complex.normSq (pairGram H (packet x) F) ≤
      tripleFine F H (packet x) := by
  let G := packet x
  let P := (symmetricProductMatrix H).mulVec F
  let a := ((k+k).choose k : ℝ)
  have hP : Symmetric P := product_symmetric H F
  have hG : Symmetric G := Bridges.packet_symmetric _ _ x
  let idx : Fin (k+1) ≃ CutIndex (k+k) k := finCongr (by simp [min_eq_right (show k ≤ k+k by omega)])
  let E (j : Fin (k+1)) := energy (longCut P G (idx j))
  let EF := energy (longCut P G (fiveFull k))
  let W (j : Fin (k+1)) := ((k+k).choose j : ℝ) * (k.choose j : ℝ)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hfull : 0 ≤ EF := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have htest : Complex.normSq (pairGram H G F) ≤ a^2 * EF := full_test H F G hG hu
  have each (i : Fin k) : ((k+k).choose (i.val+1) : ℝ) * EF ≤ W i.succ * E i.succ := by
    have he := five_cap_energy hP x (idx i.succ)
    change EF ≤ (k.choose (i.val+1) : ℝ) * E i.succ at he
    exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans_eq (mul_assoc ..).symm
  have hz : E 0 = energy P := by
    have hzero := StraightCut.straight_energy hP hG
    change E 0 = energy P * energy G at hzero
    simpa only [show energy G = 1 from hx, mul_one] using hzero
  have heq : tripleFine F H G = a * (energy P + ∑ j : Fin k, W j.succ * E j.succ) := by
    rw [tripleFine, closed_bent_schur _ _ _ (SchurNormalization.homogeneousSchur_implies_unbent _ _ _ schur),
      Complex.re_sum, ← idx.sum_comp, Fin.sum_univ_succ]
    change a * (_ + _) = _
    congr 1
    congr 1
    · change (((weight (k+k) k 0 : ℂ) * (E 0 : ℂ))).re = _
      simp [weight, hz]
    · apply Finset.sum_congr rfl
      intro i _
      change (((weight (k+k) k i.succ : ℂ) * (E i.succ : ℂ))).re = _
      simp [weight, W, Complex.mul_re, mul_assoc]
  have hc : (41/20 : ℝ) * a ≤ ∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ) :=
    FiveNumbers.coefficient_lower hk
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  rw [← Finset.sum_mul] at hsum
  have gain : (41/20 : ℝ) * Complex.normSq (pairGram H G F) ≤
      a * ∑ i : Fin k, W i.succ * E i.succ := by
    calc
      _ ≤ (41/20 : ℝ) * (a^2 * EF) := mul_le_mul_of_nonneg_left htest (by norm_num)
      _ = a * (((41/20 : ℝ) * a) * EF) := by ring
      _ ≤ a * ((∑ i : Fin k, ((k+k).choose (i.val+1) : ℝ)) * EF) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hfull) ha
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum ha
  change _ + _ * Complex.normSq (pairGram H G F) ≤ tripleFine F H G
  rw [pairGram_self_re, heq, mul_add]
  exact add_le_add_left gain _

section Forms

variable {I : Type*} [Fintype I] {d k : ℕ}

/-- The paper's T-matrix on any finite list of second inputs. -/
def remainderForm (H : Word d k → ℂ) (y : I → Word d k → ℂ) : Matrix I I ℂ :=
  fun i j => pairGram H (y i) (y j) - bracket (y i) (y j) -
    7 * bracket (y i) H * bracket H (y j)

/-- Test matrix of the two mixed gluings. -/
def testForm (l m : ℝ) (H : Word d k → ℂ) (y : I → Word d k → ℂ) : Matrix I I ℂ :=
  fun i j => (l : ℂ)*bracket (y i) (y j) + (m : ℂ)*bracket (y i) H*bracket H (y j)

private def columns (y : I → Word d k → ℂ) : Matrix (Word d k) I ℂ := fun w i => y i w

omit [Fintype I] in
private theorem gram_cols (y : I → Word d k → ℂ) (i j : I) :
    ((columns y)ᴴ * columns y) i j = bracket (y i) (y j) := rfl

private theorem pairStar {I' : Type*} [Fintype I'] (F G : I' → ℂ) :
    star (bracket F G) = bracket G F := by
  simp [bracket, star_sum, star_mul', Complex.star_def, mul_comm]

omit [Fintype I] in
private theorem tested_gram (H : Word d k → ℂ) (y : I → Word d k → ℂ) (i j : I) :
    let T := PairSquares.pairingRow H * columns y
    (Tᴴ * T) i j = bracket (y i) H * bracket H (y j) := by
  dsimp only
  change (∑ t : Unit, star (bracket H (y i)) * bracket H (y j)) = _
  simp [pairStar]

omit [Fintype I] in
private theorem product_gram (H : Word d k → ℂ) (y : I → Word d k → ℂ) (i j : I) :
    let T := symmetricProductMatrix H * columns y
    (Tᴴ * T) i j = bracket ((symmetricProductMatrix H).mulVec (y i))
      ((symmetricProductMatrix H).mulVec (y j)) := rfl

/-- Positivity of the sesquilinear remainder holds on the whole symmetric
space, so every finite matrix of its pairings is positive semidefinite. -/
theorem remainder_posSemidef (hk : 3 ≤ k)
    (schur : SchurNormalization.HomogeneousSchur d k k)
    (H : Word d k → ℂ) (hH : ∃ (a : ℂ) (x : Fin k → Fin d → ℂ), H = fun i => a * packet x i)
    (hu : energy H = 1) (y : I → Word d k → ℂ) (hy : ∀ i, Symmetric (y i)) :
    (remainderForm H y).PosSemidef := by
  let C := columns y
  let A := symmetricProductMatrix H * C
  let T := PairSquares.pairingRow H * C
  let a := ((k+k).choose k : ℝ)
  have hfix : symClasp d k * C = C := by
    ext i j
    exact congrFun (hy j) i
  have h (v : I → ℂ) : energy (C.mulVec v) + 7 * energy (T.mulVec v) ≤ a * energy (A.mulVec v) := by
    have hs : Symmetric (C.mulVec v) := by rw [Bend.Symmetric, Matrix.mulVec_mulVec, hfix]
    have hp := full_caps_normalized schur hH hu hs
    have hpow : (2:ℝ)^3 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    have h7 : (7:ℝ) ≤ 2^k-1 := by linarith
    have hl := mul_le_mul_of_nonneg_right h7 (Complex.normSq_nonneg (bracket H (C.mulVec v)))
    unfold T A
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, PairSquares.pairingEnergy]
    exact (add_le_add_left hl _).trans hp
  have hp := PairSquares.difference_posSemidef A C T a 7 h
  have heq : remainderForm H y = (a : ℂ) • (Aᴴ * A) - Cᴴ * C - ((7:ℝ):ℂ) • (Tᴴ * T) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [product_gram H y, gram_cols y, tested_gram H y]
    simp [a, pairGram, remainderForm, mul_assoc]
  rw [heq]
  exact hp

private theorem scaled_gram_pos {J : Type*} [Fintype J] (C : Matrix J I ℂ) (a : ℝ)
    (ha : 0 ≤ a) : ((a : ℂ) • (Cᴴ * C)).PosSemidef := by
  constructor
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  · intro v
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, PairSquares.gram_eval]
    change 0 ≤ (a : ℂ) * (energy (C.mulVec v) : ℂ)
    rw [← Complex.ofReal_mul, Complex.zero_le_real]
    exact mul_nonneg ha (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- Positivity of the mixed test for nonnegative weights. -/
theorem test_posSemidef (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (H : Word d k → ℂ) (y : I → Word d k → ℂ) : (testForm l m H y).PosSemidef := by
  let C := columns y
  let T := PairSquares.pairingRow H * C
  have hp := (scaled_gram_pos C l hl).add (scaled_gram_pos T m hm)
  have heq : testForm l m H y = (l:ℂ) • (Cᴴ * C) + (m:ℂ) • (Tᴴ * T) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [gram_cols y, tested_gram H y]
    simp [testForm, mul_assoc]
  rw [heq]
  exact hp

private theorem diagonalPair (F H : Word d k → ℂ) :
    bracket F H * bracket H F = (Complex.normSq (bracket F H) : ℂ) := by
  rw [← pairStar F H]
  exact Complex.mul_conj _

omit [Fintype I] in
theorem remainder_diagonal (H : Word d k → ℂ) (y : I → Word d k → ℂ) (hy : ∀ i, energy (y i) = 1) (i : I) :
    (remainderForm H y i i).re = (pairGram H (y i) (y i)).re - 1 - 7*Complex.normSq (bracket (y i) H) := by
  simp [remainderForm, Coarse.bracket_self, hy, mul_assoc, diagonalPair, Complex.mul_re]

omit [Fintype I] in
theorem test_diagonal (l m : ℝ) (H : Word d k → ℂ) (y : I → Word d k → ℂ)
    (hy : ∀ i, energy (y i) = 1) (i : I) :
    testForm l m H y i i = ((l + m * Complex.normSq (bracket (y i) H) : ℝ) : ℂ) := by
  simp [testForm, Coarse.bracket_self, hy, mul_assoc, diagonalPair]

omit [Fintype I] in
theorem test_diagonal_le (l m : ℝ) (hm : 0 ≤ m) (H : Word d k → ℂ) (hu : energy H = 1)
    (y : I → Word d k → ℂ) (hy : ∀ i, energy (y i) = 1) (i : I) :
    (testForm l m H y i i).re ≤ l+m := by
  rw [test_diagonal l m H y hy, Complex.ofReal_re]
  have h := bracket_bound (y i) H
  rw [hy, hu, mul_one] at h
  simpa using add_le_add_left (mul_le_mul_of_nonneg_left h hm) l

end Forms
end
end BlockPermanents.FiveProjection
