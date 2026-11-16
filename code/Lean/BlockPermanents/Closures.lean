import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Section 2E. Matrix packets and symmetric closures

An index of the product basis of a tensor power is a word `I → D`.
The coordinate pairing is conjugate-linear on its first input. All slot and
basis sets below are finite, with no dimension or independence condition.
-/

namespace BlockPermanents.Closures
open scoped BigOperators
open Fintype

noncomputable section

variable {D I : Type*} [Fintype D] [Fintype I] [DecidableEq I]

/-- Hermitian pairing in the indicated orthonormal coordinate basis. -/
def bracket {A : Type*} [Fintype A] (u v : A → ℂ) : ℂ :=
  ∑ a, (starRingEnd ℂ) (u a) * v a

/-- Coordinates of a pure tensor. -/
def pureWord (x : I → D → ℂ) (w : I → D) : ℂ := ∏ i, x i (w i)

/-- The matrix of pairings between two families of column vectors. -/
def crossGram (x y : I → D → ℂ) : Matrix I I ℂ := fun i j => bracket (x i) (y j)

theorem bracket_pureWord (x y : I → D → ℂ) :
    bracket (pureWord x) (pureWord y) = ∏ i, bracket (x i) (y i) := by
  classical
  simp only [bracket, pureWord, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : I) (d : D) => (starRingEnd ℂ) (x i d) * y i d)).symm

theorem bracket_sum_left {A B : Type*} [Fintype A] [Fintype B]
    (u : B → A → ℂ) (v : A → ℂ) :
    bracket (fun a => ∑ b, u b a) v = ∑ b, bracket (u b) v := by
  simp only [bracket, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem bracket_sum_right {A B : Type*} [Fintype A] [Fintype B]
    (u : A → ℂ) (v : B → A → ℂ) :
    bracket u (fun a => ∑ b, v b a) = ∑ b, bracket u (v b) := by
  simp only [bracket, Finset.mul_sum]
  exact Finset.sum_comm

theorem bracket_scale {A : Type*} [Fintype A] (a b : ℂ) (u v : A → ℂ) :
    bracket (fun j => a * u j) (fun j => b * v j) =
      (starRingEnd ℂ) a * b * bracket u v := by
  simp only [bracket, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

/-- Sum of all orders of a pure tensor, before division by the order of the group. -/
def orderSum (x : I → D → ℂ) (w : I → D) : ℂ :=
  ∑ σ : Equiv.Perm I, pureWord (x ∘ σ) w

/-- One clasp against a product tensor, in the unnormalized sum convention. -/
theorem bracket_orderSum_pureWord (x y : I → D → ℂ) :
    bracket (orderSum x) (pureWord y) = (crossGram x y).permanent := by
  unfold orderSum
  rw [bracket_sum_left]
  simp only [bracket_pureWord, crossGram, Matrix.permanent, Function.comp_apply]

/-- Two unnormalized clasps contribute one factor of the group order. -/
theorem bracket_orderSum (x y : I → D → ℂ) :
    bracket (orderSum x) (orderSum y) =
      ((Fintype.card I).factorial : ℂ) * (crossGram x y).permanent := by
  conv_lhs => arg 2; unfold orderSum
  rw [bracket_sum_right]
  simp_rw [bracket_orderSum_pureWord]
  have h (τ : Equiv.Perm I) :
      (crossGram x (y ∘ τ)).permanent = (crossGram x y).permanent :=
    Matrix.permanent_permute_rows τ (crossGram x y)
  simp [h, Fintype.card_perm]

/-- Real normalization of the permutation sum in a matrix packet. -/
def packetScale (I : Type*) [Fintype I] : ℂ :=
  ((Real.sqrt ((Fintype.card I).factorial : ℝ) : ℝ) : ℂ)⁻¹

omit [DecidableEq I] in
theorem scale_cancel :
    (starRingEnd ℂ) (packetScale I) * packetScale I * ((Fintype.card I).factorial : ℂ) = 1 := by
  let n := (Fintype.card I).factorial
  have hn : n ≠ 0 := Nat.factorial_ne_zero _
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hs : (Real.sqrt (n : ℝ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  change (starRingEnd ℂ) (Real.sqrt (n : ℝ) : ℂ)⁻¹ * _ * _ = _
  rw [map_inv₀, Complex.conj_ofReal]
  change (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (Real.sqrt (n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1
  rw [← mul_inv, hs, inv_mul_cancel₀ hn']

/-- The manuscript's matrix packet, equivalently the sum of the orders
divided by the square root of the number of orders. -/
def packet (x : I → D → ℂ) (w : I → D) : ℂ := packetScale I * orderSum x w

/-- Pairing two matrix packets gives the permanent of their cross Gram matrix. -/
theorem packet_gram (x y : I → D → ℂ) :
    bracket (packet x) (packet y) = (crossGram x y).permanent := by
  unfold packet
  rw [bracket_scale, bracket_orderSum, ← mul_assoc, scale_cancel, one_mul]

/-- Unnormalized full symmetrization on an arbitrary tensor. -/
def sumSlots (z : (I → D) → ℂ) (w : I → D) : ℂ :=
  ∑ σ : Equiv.Perm I, z (w ∘ σ.symm)

/-- The operator averaging permutations of all slots. -/
def clasp (z : (I → D) → ℂ) (w : I → D) : ℂ :=
  ((Fintype.card I).factorial : ℂ)⁻¹ * sumSlots z w

omit [Fintype D] [DecidableEq I] in
theorem pure_reindex (x : I → D → ℂ) (σ : Equiv.Perm I) (w : I → D) :
    pureWord x (w ∘ σ.symm) = pureWord (x ∘ σ) w := by
  unfold pureWord
  apply Fintype.prod_equiv σ.symm
  intro i
  simp

omit [Fintype D] in
theorem sumSlots_pure (x : I → D → ℂ) : sumSlots (pureWord x) = orderSum x := by
  funext w
  unfold sumSlots orderSum
  exact Finset.sum_congr rfl (fun σ _ => pure_reindex x σ w)

/-- For two product inputs, their clasp images pair to the permanent
divided by the order of the symmetric group. -/
theorem clasp_pure_closure (x y : I → D → ℂ) :
    ((Fintype.card I).factorial : ℂ) *
      bracket (clasp (pureWord x)) (clasp (pureWord y)) = (crossGram x y).permanent := by
  unfold clasp
  rw [sumSlots_pure, sumSlots_pure, bracket_scale, bracket_orderSum]
  have hn : ((Fintype.card I).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
  simp only [map_inv₀, map_natCast]
  field_simp
  ring

variable {M K : Type*} [Fintype M] [Fintype K] [DecidableEq M] [DecidableEq K]

/-- The packet closure in the manuscript's two-closure lemma (in mixed form). -/
theorem packet_closure (x y : M → K → D → ℂ) :
    ((Fintype.card M).factorial : ℂ) *
      bracket (clasp (pureWord (fun i => packet (x i))))
        (clasp (pureWord (fun i => packet (y i)))) =
      Matrix.permanent (fun i j => (crossGram (x i) (y j)).permanent) := by
  rw [clasp_pure_closure]
  congr 1
  funext i j
  exact packet_gram _ _

/-- A simultaneous choice of an internal permutation for each packet acts
as a single permutation of the flat array of slots. -/
def withinPackets (p : M → Equiv.Perm K) : Equiv.Perm (M × K) where
  toFun a := (a.1, p a.1 a.2)
  invFun a := (a.1, (p a.1).symm a.2)
  left_inv a := by simp
  right_inv a := by simp

omit [Fintype D] in
theorem sumSlots_absorb (p : Equiv.Perm I) (z : (I → D) → ℂ) :
    sumSlots (fun w => z (w ∘ p.symm)) = sumSlots z := by
  funext w
  exact (Group.mulLeft_bijective p).sum_comp
    (fun τ : Equiv.Perm I => z (w ∘ τ.symm))

/-- The common input in a single array of thin-slot coordinates. -/
def flatPackets (x : M → K → D → ℂ) (w : M × K → D) : ℂ :=
  ∏ i, packet (x i) (fun t => w (i,t))

omit [Fintype D] in
theorem flatPackets_expand (x : M → K → D → ℂ) (w : M × K → D) :
    flatPackets x w =
      packetScale K ^ Fintype.card M * ∑ p : M → Equiv.Perm K,
        pureWord (Function.uncurry x) (w ∘ (withinPackets p).symm) := by
  classical
  unfold flatPackets packet
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, orderSum]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [pure_reindex]
  unfold pureWord
  rw [Fintype.prod_prod_type]
  rfl

omit [Fintype D] in
theorem sumSlots_sum {A : Type*} [Fintype A] (z : A → (I → D) → ℂ) :
    sumSlots (fun w => ∑ a, z a w) = fun w => ∑ a, sumSlots (z a) w := by
  funext w
  unfold sumSlots
  exact Finset.sum_comm

omit [Fintype D] in
theorem sumSlots_scale (c : ℂ) (z : (I → D) → ℂ) :
    sumSlots (fun w => c * z w) = fun w => c * sumSlots z w := by
  funext w
  exact (Finset.mul_sum _ _ _).symm

/-- The factor remaining when the fine clasp absorbs the internal clasps. -/
def absorptionScale (M K : Type*) [Fintype M] [Fintype K] : ℂ :=
  packetScale K ^ Fintype.card M * (((Fintype.card K).factorial : ℂ) ^ Fintype.card M)

omit [Fintype D] in
theorem clasp_flatPackets (x : M → K → D → ℂ) :
    clasp (flatPackets x) =
      fun w => absorptionScale M K * clasp (pureWord (Function.uncurry x)) w := by
  classical
  have h := funext (flatPackets_expand x)
  unfold clasp
  rw [h, sumSlots_scale, sumSlots_sum]
  simp_rw [sumSlots_absorb]
  funext w
  simp [absorptionScale, Fintype.card_fun, Fintype.card_perm, mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq M] [DecidableEq K] in
private theorem absorptionScale_square :
    (starRingEnd ℂ) (absorptionScale M K) * absorptionScale M K =
      ((Fintype.card K).factorial : ℂ) ^ Fintype.card M := by
  let n : ℂ := (Fintype.card K).factorial
  let c := packetScale K
  let m := Fintype.card M
  change (starRingEnd ℂ) (c^m * n^m) * (c^m * n^m) = n^m
  calc
    _ = (((starRingEnd ℂ) c * c * n) * n)^m := by
      simp only [map_mul, map_pow, mul_pow]
      have hn : (starRingEnd ℂ) n = n := map_natCast _ _
      rw [hn]
      ring
    _ = n^m := by
      have h : (starRingEnd ℂ) c * c * n = 1 := scale_cancel (I := K)
      rw [h, one_mul]

/-- The fine closure in the two-closure lemma, for arbitrary block counts,
block thicknesses, and complex input families. -/
theorem fine_closure (x y : M → K → D → ℂ) :
    (((Fintype.card M * Fintype.card K).factorial : ℂ) /
      (Fintype.card K).factorial ^ Fintype.card M) *
      bracket (clasp (flatPackets x)) (clasp (flatPackets y)) =
      (crossGram (Function.uncurry x) (Function.uncurry y)).permanent := by
  rw [clasp_flatPackets, clasp_flatPackets, bracket_scale, absorptionScale_square]
  have h := clasp_pure_closure (Function.uncurry x) (Function.uncurry y)
  rw [Fintype.card_prod] at h
  rw [← h, ← mul_assoc]
  have hn : ((Fintype.card K).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card K)
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hn)]

omit [Fintype D] [DecidableEq M] in
/-- The input to both closures agrees after currying the word coordinates. -/
theorem common_input (x : M → K → D → ℂ) (w : M × K → D) :
    flatPackets x w = pureWord (fun i => packet (x i)) (Function.curry w) := rfl

omit [Fintype D] in
theorem clasp_invariant (v : (I → D) → ℂ) (p : Equiv.Perm I) (w : I → D) :
    clasp v (w ∘ p.symm) = clasp v w := by
  unfold clasp
  congr 1
  exact (Group.mulRight_bijective p).sum_comp
    (fun τ : Equiv.Perm I => v (w ∘ τ.symm))

private theorem bracket_reindex_clasp (u v : (I → D) → ℂ) (p : Equiv.Perm I) :
    bracket (fun w => u (w ∘ p.symm)) (clasp v) = bracket u (clasp v) := by
  unfold bracket
  apply Fintype.sum_equiv (p.arrowCongr (Equiv.refl D))
  intro w
  change _ = _ * clasp v (w ∘ p.symm)
  rw [clasp_invariant]
  rfl

/-- An additional clasp on the reflected side of a clasp does not change the pairing. -/
theorem bracket_clasp (u v : (I → D) → ℂ) :
    bracket (clasp u) (clasp v) = bracket u (clasp v) := by
  let c : ℂ := ((Fintype.card I).factorial : ℂ)⁻¹
  calc
    _ = bracket (fun w => c * sumSlots u w) (fun w => 1 * clasp v w) := by simp only [one_mul]; rfl
    _ = (starRingEnd ℂ) c * 1 * bracket (sumSlots u) (clasp v) := bracket_scale ..
    _ = _ := by
      unfold sumSlots
      rw [bracket_sum_left]
      simp_rw [bracket_reindex_clasp]
      have hn : ((Fintype.card I).factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
      simp [c, Fintype.card_perm, ← mul_assoc, hn]

/-- Whole-packet symmetrization written on the same flat array as the fine clasp. -/
def packetClasp (z : (M × K → D) → ℂ) (w : M × K → D) : ℂ :=
  clasp (fun u : M → K → D => z (Function.uncurry u)) (Function.curry w)

/-- The scalar multiplying the fine clasp in the defect operator. -/
def fineWeight (M K : Type*) [Fintype M] [Fintype K] : ℂ :=
  ((Fintype.card M * Fintype.card K).factorial : ℂ) / (Fintype.card K).factorial ^ Fintype.card M

/-- The actual difference of the two weighted clasp operators on thin-slot coordinates. -/
def defect (z : (M × K → D) → ℂ) (w : M × K → D) : ℂ :=
  fineWeight M K * clasp z w - ((Fintype.card M).factorial : ℂ) * packetClasp z w

private theorem bracket_packetClasp (x y : M → K → D → ℂ) :
    bracket (flatPackets x) (packetClasp (flatPackets y)) =
      bracket (pureWord (fun i => packet (x i))) (clasp (pureWord (fun i => packet (y i)))) := by
  unfold bracket
  exact Fintype.sum_equiv (Equiv.curry M K D) _ _ (fun _ => rfl)

theorem bracket_scaled_sub {A : Type*} [Fintype A] (a b : ℂ) (u v v' : A → ℂ) :
    bracket u (fun w => a * v w - b * v' w) = a * bracket u v - b * bracket u v' := by
  simp only [bracket, Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

/-- Lemma 2E.3, equations (2E.4)–(2E.5), polarized between two families of columns.
Taking `y = x` identifies the manuscript's matrix gap with the closure of `defect`. -/
theorem defect_closure (x y : M → K → D → ℂ) :
    bracket (flatPackets x) (defect (flatPackets y)) =
      (crossGram (Function.uncurry x) (Function.uncurry y)).permanent -
        Matrix.permanent (fun i j => (crossGram (x i) (y j)).permanent) := by
  unfold defect
  rw [bracket_scaled_sub, bracket_packetClasp]
  rw [← bracket_clasp (flatPackets x) (flatPackets y),
      ← bracket_clasp (pureWord (fun i => packet (x i))) (pureWord (fun i => packet (y i)))]
  rw [fineWeight, fine_closure, packet_closure]

end
end BlockPermanents.Closures
