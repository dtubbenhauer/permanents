import BlockPermanents.Negative
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Binary occupation words

A subset of `Fin d` specifies the slots occupied by e₁ in a length-d word
in e₀ and e₁. We use the ordinary dot product on this orthonormal basis.
The packet coordinates in the negative witness are real, so rational
bilinear pairings suffice here.
-/
namespace BlockPermanents.Occupation

open Finset
open Negative Polynomial

/-- Distribute each occupation coefficient equally among its distinct words. -/
def expand {d : ℕ} (coeff : ℕ → ℚ) (word : Finset (Fin d)) : ℚ :=
  coeff word.card / (d.choose word.card : ℚ)

def wordPair {d : ℕ} (x y : Finset (Fin d) → ℚ) : ℚ :=
  ∑ w ∈ (Finset.univ : Finset (Fin d)).powerset, x w * y w

/-- Sum of a word vector over all permutations of its slots. -/
def permSum {d : ℕ} (x : Finset (Fin d) → ℚ) (w : Finset (Fin d)) : ℚ :=
  ∑ σ : Equiv.Perm (Fin d), x (w.map σ.toEmbedding)

private theorem permSum_map {d : ℕ} (x : Finset (Fin d) → ℚ)
    (w : Finset (Fin d)) (τ : Equiv.Perm (Fin d)) :
    permSum x (w.map τ.toEmbedding) = permSum x w := by
  unfold permSum
  simp only [map_map]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm (Fin d) => x (w.map σ.toEmbedding))

private theorem word_perm_of_card {d : ℕ} {u v : Finset (Fin d)} (h : u.card = v.card) :
    ∃ σ : Equiv.Perm (Fin d), u.map σ.toEmbedding = v := by
  let e := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, eq_of_subset_of_card_le ?_ ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hz
    exact e.extendSubtype_mem y hy
  · simpa using h.ge

private theorem sum_map_words {d : ℕ} (x : Finset (Fin d) → ℚ) (j : ℕ)
    (σ : Equiv.Perm (Fin d)) :
    ∑ v ∈ powersetCard j (univ : Finset (Fin d)), x (v.map σ.toEmbedding) =
    ∑ v ∈ powersetCard j (univ : Finset (Fin d)), x v := by
  calc
    _ = ∑ v ∈ (powersetCard j (univ : Finset (Fin d))).map
        (mapEmbedding σ.toEmbedding).toEmbedding, x v := (sum_map _ _ _).symm
    _ = _ := by rw [← powersetCard_map, map_univ_equiv]

/-- Averaging over all d! slot permutations equals averaging over all
distinct words having the given occupation. -/
theorem symmetrizer_word {d : ℕ} (x : Finset (Fin d) → ℚ) (w : Finset (Fin d)) :
    permSum x w / (d.factorial : ℚ) =
    (∑ v ∈ powersetCard w.card (univ : Finset (Fin d)), x v) / (d.choose w.card : ℚ) := by
  have hfac : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hchoose : (d.choose w.card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by simpa using w.card_le_univ)).ne'
  apply (div_eq_div_iff hfac hchoose).mpr
  let words := powersetCard w.card (univ : Finset (Fin d))
  calc
    permSum x w * (d.choose w.card : ℚ) =
      ∑ _v ∈ words, permSum x w := by
        simp [words, card_powersetCard, mul_comm]
    _ = ∑ v ∈ words, permSum x v := by
      apply sum_congr rfl
      intro v hv
      have hcard := (mem_powersetCard.mp hv).2
      obtain ⟨σ, rfl⟩ := word_perm_of_card hcard.symm
      exact (permSum_map x w σ).symm
    _ = ∑ σ : Equiv.Perm (Fin d), ∑ v ∈ words, x (v.map σ.toEmbedding) := sum_comm
    _ = ∑ _σ : Equiv.Perm (Fin d), ∑ v ∈ words, x v := by
      apply sum_congr rfl
      intro σ _
      exact sum_map_words x _ σ
    _ = (∑ v ∈ words, x v) * (d.factorial : ℚ) := by
      simp [Fintype.card_perm, mul_comm]

/-- Direct identification with the occupation-vector expansion. -/
theorem symmetrizer_eq_expand {d : ℕ} (x : Finset (Fin d) → ℚ) :
    (fun w => permSum x w / (d.factorial : ℚ)) =
    expand (fun j => ∑ v ∈ powersetCard j (univ : Finset (Fin d)), x v) := by
  funext w
  exact symmetrizer_word x w

/-- Counting the words in each occupation fiber leaves one reciprocal
binomial coefficient in a mixed inner product. -/
theorem occupation_pair (d : ℕ) (a b : ℕ → ℚ) :
    wordPair (expand (d := d) a) (expand b) =
    ∑ j ∈ range (d+1), a j * b j / (d.choose j : ℚ) := by
  rw [wordPair, Finset.sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro j hj
  change (∑ w ∈ powersetCard j (univ : Finset (Fin d)),
    (fun k => a k / (d.choose k : ℚ) * (b k / (d.choose k : ℚ))) w.card) = _
  rw [Finset.sum_powersetCard j (univ : Finset (Fin d)) (fun k => a k / (d.choose k : ℚ) * (b k / (d.choose k : ℚ)))]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (d.choose j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.mp hj))).ne'
  field_simp
  ring

/-- The three occupation coefficients of a quadratic packet. -/
def quadCoeff (p : Quad) : ℕ → ℚ
  | 0 => p.a
  | 1 => p.b
  | 2 => p.c
  | _ => 0

/-- The Gram entries used at all spectator exits are the genuine word
pairings of arbitrary rational quadratic packets. -/
theorem gram_eq_wordPair (p q : Quad) :
    gram p q = wordPair (expand (d := 2) (quadCoeff p)) (expand (quadCoeff q)) := by
  rw [occupation_pair]
  norm_num [sum_range_succ, quadCoeff, Nat.choose, gram]

private theorem range_map_sum (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, sum_range_succ]

/-- Any two binary occupation vectors, normalized by the order of the
symmetric group, have the factorial-weighted occupation pairing. -/
theorem factorial_pair (d : ℕ) (a b : ℕ → ℚ) :
    (d.factorial : ℚ) * wordPair (expand (d := d) a) (expand b) =
    ∑ j ∈ range (d+1), a j * b j * j.factorial * (d-j).factorial := by
  rw [occupation_pair, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d := Nat.le_of_lt_succ (mem_range.mp hj)
  have hpos : (d.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  have hf : (d.choose j : ℚ) * (j.factorial : ℚ) * ((d-j).factorial : ℚ) =
      (d.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  rw [← hf]
  field_simp
  ring

/-- Expand the actual polynomial product used in the marked evaluation
as a vector in the thin word basis at a specified degree. -/
def mergedWord (d : ℕ) (xs : List Quad) : Finset (Fin d) → ℚ :=
  expand (fun j => (productCoeffs xs)[j]?.getD 0)

/-- For any two lists of n rational quadratic packets the fine-closure
evaluator equals the word pairing with the prefactor (2n)!/2ⁿ. -/
theorem fine_eq_wordPair (xs ys : List Quad) (_h : xs.length = ys.length) :
    fine xs ys = ((2*xs.length).factorial : ℚ) *
      wordPair (mergedWord (2*xs.length) xs) (mergedWord (2*xs.length) ys) / 2^xs.length := by
  unfold mergedWord fine
  dsimp only
  rw [factorial_pair, range_map_sum]

private noncomputable def horner : List ℚ → Polynomial ℚ
  | [] => 0
  | a :: xs => C a + X * horner xs

private theorem horner_add : ∀ xs ys, horner (addCoeffs xs ys) = horner xs + horner ys
  | [], ys => by simp [addCoeffs, horner]
  | a::xs, [] => by simp [addCoeffs, horner]
  | a::xs, b::ys => by
    simp only [addCoeffs, horner, map_add, horner_add xs ys]
    ring

private theorem horner_scale (r : ℚ) (xs : List ℚ) :
    horner (xs.map (r * ·)) = C r * horner xs := by
  induction xs with
  | nil => simp [horner]
  | cons x xs ih => simp [horner, ih]; ring

private noncomputable def quadPoly (q : Quad) : Polynomial ℚ := C q.a + X * C q.b + X^2 * C q.c

private theorem horner_timesQuad (q : Quad) (xs : List ℚ) :
    horner (timesQuad q xs) = quadPoly q * horner xs := by
  unfold timesQuad
  split
  · rename_i h
    simp [quadPoly, h.1, h.2, horner_scale]
  · simp only [horner_add, horner_scale, horner, quadPoly, map_zero, zero_add]
    ring

private theorem coeff_horner (xs : List ℚ) (j : ℕ) :
    (horner xs).coeff j = xs[j]?.getD 0 := by
  induction xs generalizing j with
  | nil => simp [horner]
  | cons a xs ih =>
    cases j with
    | zero => simp [horner]
    | succ j => simp [horner, coeff_C, coeff_X_mul, ih]

/-- Prepend the four actual two-letter words and multiply the raw
tensor entries, including both orders of the mixed occupation. -/
private def prependPacket (q : Quad) (tail : List Bool × ℚ) : List (List Bool × ℚ) :=
  [(false :: false :: tail.1, q.a * tail.2), (false :: true :: tail.1, q.b / 2 * tail.2),
   (true :: false :: tail.1, q.b / 2 * tail.2), (true :: true :: tail.1, q.c * tail.2)]

/-- All 2^(2n) words and their amplitudes in the unsymmetrized tensor
product of the n quadratic packets. -/
def rawWords : List Quad → List (List Bool × ℚ)
  | [] => [([], 1)]
  | q::xs => (rawWords xs).flatMap (prependPacket q)

private noncomputable def wordMonomial (t : List Bool × ℚ) : Polynomial ℚ := C t.2 * X^(t.1.count true)

private theorem prepend_poly (q : Quad) (w : List Bool × ℚ) :
    ((prependPacket q w).map wordMonomial).sum = quadPoly q * wordMonomial w := by
  have hm : C q.b = (C (q.b / 2) + C (q.b / 2) : Polynomial ℚ) := by
    rw [← map_add]
    congr 1
    ring
  simp [prependPacket, wordMonomial, quadPoly, List.count_cons, pow_succ, add_assoc]
  rw [hm]
  ring

private theorem raw_poly (q : Quad) (ts : List (List Bool × ℚ)) :
    ((ts.flatMap (prependPacket q)).map wordMonomial).sum =
      quadPoly q * (ts.map wordMonomial).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [List.map_append, List.sum_append, prepend_poly, ih, mul_add]

private theorem horner_eq_words (xs : List Quad) :
    horner (productCoeffs xs) = ((rawWords xs).map wordMonomial).sum := by
  induction xs with
  | nil => simp [productCoeffs, rawWords, horner, wordMonomial]
  | cons p xs ih =>
    change horner (timesQuad p (productCoeffs xs)) =
      (((rawWords xs).flatMap (prependPacket p)).map wordMonomial).sum
    rw [horner_timesQuad, raw_poly, ih]

private theorem monomial_sum_coeff (ts : List (List Bool × ℚ)) (j : ℕ) :
    ((ts.map wordMonomial).sum).coeff j =
    (ts.map (fun t => if t.1.count true = j then t.2 else 0)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [wordMonomial, coeff_C_mul, coeff_X_pow, ih, eq_comm]

/-- The coefficient computed in the marked witness is the sum of all
raw tensor amplitudes with precisely j copies of the second basis vector. -/
theorem productCoeffs_eq_word_sum (xs : List Quad) (j : ℕ) :
    (productCoeffs xs)[j]?.getD 0 =
    ((rawWords xs).map (fun t => if t.1.count true = j then t.2 else 0)).sum := by
  rw [← coeff_horner, horner_eq_words, monomial_sum_coeff]

/-- Convert a binary word to its occupied slots, with the first letter at slot zero. -/
private def slots : (d : ℕ) → List Bool → Finset (Fin d)
  | 0, _ => ∅
  | _+1, [] => ∅
  | n+1, b::bs =>
      let tail := (slots n bs).map (Fin.succEmb n)
      if b then insert 0 tail else tail

private theorem card_slots (bs : List Bool) : (slots bs.length bs).card = bs.count true := by
  induction bs with
  | nil => simp [slots]
  | cons b bs ih =>
    have h : (0 : Fin (bs.length+1)) ∉ (slots bs.length bs).map (Fin.succEmb _) := by simp
    cases b <;> simp [slots, List.count_cons, h, ih]

private theorem rawWords_length (xs : List Quad) (t : List Bool × ℚ) (ht : t ∈ rawWords xs) :
    t.1.length = 2 * xs.length := by
  induction xs generalizing t with
  | nil => simp [rawWords] at ht; simp [ht]
  | cons p xs ih =>
    obtain ⟨v, hv, ht⟩ := List.mem_flatMap.mp ht
    have h := ih v hv
    simp [prependPacket] at ht
    rcases ht with h' | h' | h' | h' <;> subst t <;> simp [h] <;> omega

/-- Accumulate the amplitudes in the basis indexed by subsets of slots. -/
private def wordVector (d : ℕ) : List (List Bool × ℚ) → Finset (Fin d) → ℚ
  | [], _ => 0
  | t::ts, w => (if w = slots d t.1 then t.2 else 0) + wordVector d ts w

private theorem fiber_wordVector (d j : ℕ) (ts : List (List Bool × ℚ))
    (H : ∀ t ∈ ts, t.1.length = d) :
    ∑ w ∈ powersetCard j (univ : Finset (Fin d)), wordVector d ts w =
    (ts.map (fun t => if t.1.count true = j then t.2 else 0)).sum := by
  induction ts with
  | nil => simp [wordVector]
  | cons t ts ih =>
    have h : (slots d t.1).card = t.1.count true := by
      rw [← H t List.mem_cons_self]
      exact card_slots _
    have H' := ih (fun v hv => H v (List.mem_cons_of_mem _ hv))
    simp [wordVector, sum_add_distrib, H', mem_powersetCard, h]

/-- The unsymmetrized tensor product as a vector on d binary slots.
Here d = 2 * xs.length when every packet contributes two slots. -/
def packetWordVector (d : ℕ) (xs : List Quad) : Finset (Fin d) → ℚ :=
  wordVector d (rawWords xs)

/-- For any list of quadratic packets, actually applying the permutation
average to its unsymmetrized word vector gives the computed merged word. -/
theorem symmetrizer_packets (d : ℕ) (xs : List Quad) (hd : 2*xs.length = d) :
    (fun w => permSum (packetWordVector d xs) w / (d.factorial : ℚ)) = mergedWord d xs := by
  rw [symmetrizer_eq_expand]
  unfold mergedWord packetWordVector
  apply congrArg (expand (d := d))
  funext j
  rw [productCoeffs_eq_word_sum, fiber_wordVector d j _ (fun t ht => (rawWords_length xs t ht).trans hd)]

/-- The fine evaluator agrees with the word inner product after applying
the full thin-slot permutation clasp to both original packet products. -/
theorem fine_eq_symmetrized_tensor (xs ys : List Quad) (h : xs.length = ys.length) :
    let d := 2*xs.length
    fine xs ys = (d.factorial : ℚ) * wordPair
      (fun w => permSum (packetWordVector d xs) w / (d.factorial : ℚ))
      (fun w => permSum (packetWordVector d ys) w / (d.factorial : ℚ)) / 2^xs.length := by
  dsimp only
  rw [symmetrizer_packets _ xs rfl, symmetrizer_packets _ ys (by rw [h])]
  exact fine_eq_wordPair xs ys h

/-- Reordering the quadratic factors preserves every occupation coefficient. -/
theorem productCoeffs_perm {xs ys : List Quad} (h : xs.Perm ys) (j : ℕ) :
    (productCoeffs xs)[j]?.getD 0 = (productCoeffs ys)[j]?.getD 0 := by
  have value (zs : List Quad) : horner (productCoeffs zs) = (zs.map quadPoly).prod := by
    induction zs with
    | nil => simp [productCoeffs, horner]
    | cons p zs ih =>
      change horner (timesQuad p (productCoeffs zs)) = _
      rw [horner_timesQuad, ih]
      rfl
  rw [← coeff_horner, ← coeff_horner, value, value, (h.map quadPoly).prod_eq]

end BlockPermanents.Occupation
