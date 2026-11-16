import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Occupation sectors and last caps

The arguments use the paper's expansion of a clasp into permutations.
A supported basis word is recorded by the set of output slots whose letter
belongs to the support. The first result evaluates the projection on any
number of marked output slots after averaging their placement. The one-strand
calculation averages actual cable and output permutations, distinguishing a
return to the original slot (a closed loop) from an open supported path.
-/

namespace BlockPermanents.Routings

open scoped BigOperators
open Finset

/-- Weight of a single opened diagram with `loops` closed supported components
and `q` open supported paths, averaged over all placements of those paths.
The sum is in the rational numbers before extending scalars. -/
noncomputable def placementAverage {N : ℕ} (supported : Finset (Fin N))
    (q loops supportDim : ℕ) : ℚ :=
  (∑ marks ∈ (univ : Finset (Fin N)).powersetCard q,
    if marks ⊆ supported then (supportDim : ℚ) ^ loops else 0) /
    ((univ : Finset (Fin N)).powersetCard q).card

/-- The surviving placements in the proof of the routed-cap intersection
formula are precisely the `q`-subsets of the supported positions. -/
theorem survivingPlacements {N : ℕ} (supported : Finset (Fin N)) (q : ℕ) :
    ((univ : Finset (Fin N)).powersetCard q).filter (· ⊆ supported) =
      supported.powersetCard q := by
  ext marks
  simp [Finset.mem_powersetCard, and_comm]

/-- The scalar contributed by any fixed number of loops and marked open paths
in the sector of a basis word. For `q ≤ N` its denominator is nonzero. -/
theorem placementAverage_eq {N : ℕ} (supported : Finset (Fin N))
    (q loops supportDim : ℕ) :
    placementAverage supported q loops supportDim =
      (supportDim : ℚ) ^ loops * (supported.card.choose q : ℚ) / (N.choose q : ℚ) := by
  classical
  unfold placementAverage
  rw [← Finset.sum_filter, survivingPlacements]
  simp [Finset.card_powersetCard, mul_comm]

/-- Average over all permutations of an `n+1`-cable, reading the destination
of its distinguished slot zero. -/
noncomputable def cableAverage (n : ℕ) (f : Fin (n + 1) → ℚ) : ℚ :=
  (∑ σ : Equiv.Perm (Fin (n+1)), f (σ 0)) / ((n+1).factorial : ℚ)

/-- The distinguished slot is uniform even though the clasp runs over
permutations. Each destination has `n!` possible residual permutations. -/
theorem cableAverage_eq (n : ℕ) (f : Fin (n+1) → ℚ) :
    cableAverage n f = (∑ i, f i) / (n+1 : ℚ) := by
  unfold cableAverage
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product,
    Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

/-- A single open supported path tests the output slot reached by the clasp. -/
noncomputable def openPath {n : ℕ} (supported : Finset (Fin (n+1))) : ℚ :=
  cableAverage n (fun i => if i ∈ supported then 1 else 0)

theorem openPath_eq {n : ℕ} (supported : Finset (Fin (n+1))) :
    openPath supported = (supported.card : ℚ) / (n+1 : ℚ) := by
  classical
  unfold openPath
  rw [cableAverage_eq, ← Finset.sum_filter]
  simp

/-- Entry obtained by following the dual from its cup on cable `j` to its
cap on cable `i`, then opening the two relevant clasps. Cable `i` has
`d+1` slots. The other cable permutations disappear by absorption.
A closed loop sums its supported basis colors. -/
noncomputable def lastCapEntry {ι : Type*} [DecidableEq ι] {n : ℕ}
    (supported : Finset (Fin (n+1))) (supportDim d : ℕ) (i j : ι) : ℚ :=
  cableAverage d (fun slot =>
    if i = j ∧ slot = 0 then ∑ _color : Fin supportDim, (1 : ℚ)
    else openPath supported)

/-- The overlap of any two last-cap routes, evaluated as the permutation
sum above, gives the diagonal correction in the paper's Gram matrix. -/
theorem lastCapEntry_eq {ι : Type*} [DecidableEq ι] {n : ℕ}
    (supported : Finset (Fin (n+1))) (supportDim d : ℕ) (i j : ι) :
    let ρ : ℚ := (supported.card : ℚ) / (n+1 : ℚ)
    lastCapEntry supported supportDim d i j =
      ρ + (if i = j then (supportDim : ℚ) - ρ else 0) / (d+1 : ℚ) := by
  classical
  dsimp only
  set ρ : ℚ := (supported.card : ℚ) / (n+1 : ℚ)
  unfold lastCapEntry
  rw [cableAverage_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, openPath_eq]
  change (∑ slot : Fin (d+1), if i = j ∧ slot = 0 then (supportDim : ℚ) else ρ) /
    (d+1 : ℚ) = _
  have hd : (d : ℚ) + 1 ≠ 0 := by positivity
  by_cases h : i = j
  · simp [h, Fin.sum_univ_succ]
    field_simp
    ring
  · simp [h]
    field_simp


section ThinCaps

open scoped Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The concrete tensor basis is indexed by a supported dual color followed
by the left and right ordinary colors. The left contraction pairs the dual
with the left input and outputs the right input. -/
def thinLeft (S : Finset α) : Matrix α (S × (α × α)) ℂ :=
  fun o p => if p.2.1 = p.1.val then (if p.2.2 = o then 1 else 0) else 0

/-- The right contraction pairs the dual with the right input. -/
def thinRight (S : Finset α) : Matrix α (S × (α × α)) ℂ :=
  fun o p => if p.2.2 = p.1.val then (if p.2.1 = o then 1 else 0) else 0

/-- Gluing a thin cap to its own Hilbert adjoint gives a supported loop.
This is the actual matrix product in the tensor basis. -/
theorem thinLeft_self (S : Finset α) :
    thinLeft S * (thinLeft S)ᴴ = (S.card : ℂ) • (1 : Matrix α α ℂ) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, thinLeft,
    Fintype.sum_prod_type, apply_ite star, star_zero, star_one, ite_mul,
    zero_mul, one_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij]

/-- The crossed gluing is exactly the coordinate orthogonal projector onto
the supported colors. This covers every finite support and ambient dimension. -/
theorem thinLeft_right (S : Finset α) :
    thinLeft S * (thinRight S)ᴴ = Matrix.diagonal (fun i ↦ if i ∈ S then 1 else 0) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, thinLeft, thinRight,
    Fintype.sum_prod_type, apply_ite star, star_zero, star_one, ite_mul,
    zero_mul, one_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
    change (∑ a ∈ S.attach, (fun x : α => if i = x then (if x = i then (1 : ℂ) else 0) else 0) a.val) = _
    rw [Finset.sum_attach S (fun x : α => if i = x then (if x = i then (1 : ℂ) else 0) else 0)]
    by_cases hi : i ∈ S <;> simp [hi]
  · simp [hij]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hi : i = a.val
    · subst i
      simp [hij]
    · simp [hi]

end ThinCaps

section WordCaps

variable {α : Type*} [DecidableEq α] {N : ℕ}

/-- Fill the cap slot with a supported color, retaining all output letters. -/
def insertColor (w : Fin N → α) (c : α) : Option (Fin N) → α
  | none => c
  | some i => w i

/-- Delete the cup slot and identify the remaining ordered slots with the
output. Swapping first records the strand that replaces the removed slot. -/
def deleteColor (p : Option (Fin N)) (x : Option (Fin N) → α) (i : Fin N) : α :=
  x (Equiv.swap none p (some i))

/-- Concrete reflected cap on an arbitrary ordered word coefficient function:
insert the cup tensor, with its two indices required to agree. -/
def reflectedCap (p : Option (Fin N)) (f : (Fin N → α) → ℂ)
    (x : Option (Fin N) → α) (color : α) : ℂ :=
  if x p = color then f (deleteColor p x) else 0

/-- Contract the cap against its reflected partner along all dual colors. -/
noncomputable def gluedWord (S : Finset α) (p : Option (Fin N))
    (f : (Fin N → α) → ℂ) (w : Fin N → α) : ℂ :=
  ∑ c ∈ S, reflectedCap p f (insertColor w c) c

theorem gluedWord_closed (S : Finset α) (f : (Fin N → α) → ℂ) (w : Fin N → α) :
    gluedWord S none f w = (S.card : ℂ) * f w := by
  have hdel (x : α) : deleteColor none (insertColor w x) = w := by
    funext t
    simp [deleteColor, insertColor]
  simp [gluedWord, reflectedCap, insertColor, hdel]

theorem gluedWord_open (S : Finset α) (i : Fin N)
    (f : (Fin N → α) → ℂ) (w : Fin N → α) :
    gluedWord S (some i) f w = if w i ∈ S then f w else 0 := by
  classical
  have hdel : deleteColor (some i) (insertColor w (w i)) = w := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [deleteColor, insertColor]
    · simp [deleteColor, insertColor, Equiv.swap_apply_def, hj]
  simp [gluedWord, reflectedCap, insertColor, hdel]

/-- The complex clasp average used on word coefficients. -/
noncomputable def complexCableAverage (d : ℕ) (f : Fin (d+1) → ℂ) : ℂ :=
  (∑ σ : Equiv.Perm (Fin (d+1)), f (σ 0)) / ((d+1).factorial : ℂ)

private theorem complexCableAverage_scale (d : ℕ) (wt : Fin (d+1) → ℚ) (v : ℂ) :
    complexCableAverage d (fun i => (wt i : ℂ) * v) = (cableAverage d wt : ℂ) * v := by
  unfold complexCableAverage cableAverage
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- The opened one-strand gluing acts on complex word coefficient functions.
The cable permutation tests whether the cup meets its own input slot; the
output permutation gives the slot visited by any other path. -/
noncomputable def lastCapOnWords {ι : Type*} [DecidableEq ι] {n : ℕ}
    (S : Finset α) (d : ℕ) (i j : ι) (f : (Fin (n+1) → α) → ℂ)
    (w : Fin (n+1) → α) : ℂ :=
  complexCableAverage d (fun slot => if i = j ∧ slot = 0 then gluedWord S none f w
    else complexCableAverage n (fun out => gluedWord S (some out) f w))

/-- Derive the Gram scalar on arbitrary word coefficients by summing
concrete insertions and contractions. The support occupancy is computed
from the letters of `w`. -/
theorem lastCapOnWords_eq {ι : Type*} [DecidableEq ι] {n : ℕ}
    (S : Finset α) (d : ℕ) (i j : ι) (f : (Fin (n+1) → α) → ℂ)
    (w : Fin (n+1) → α) :
    let slots := univ.filter (fun t => w t ∈ S)
    let ρ : ℚ := (slots.card : ℚ) / (n+1 : ℚ)
    lastCapOnWords S d i j f w =
      ((ρ + (if i = j then (S.card : ℚ) - ρ else 0) / (d+1 : ℚ) : ℚ) : ℂ) * f w := by
  classical
  let slots : Finset (Fin (n+1)) := univ.filter (fun t => w t ∈ S)
  change _ = (( _ + _ / _ : ℚ) : ℂ) * _
  rw [← lastCapEntry_eq slots S.card d i j]
  unfold lastCapOnWords lastCapEntry
  rw [← complexCableAverage_scale]
  congr 1
  funext slot
  split
  next h => simp [h, gluedWord_closed]
  next h =>
    simp only [h, if_false, openPath]
    rw [← complexCableAverage_scale]
    congr 1
    funext out
    by_cases ho : w out ∈ S <;> simp [gluedWord_open, slots, ho]

end WordCaps

section Projection

open scoped ComplexOrder Matrix

variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν]

/-- Gram matrix from the scalar one-strand calculation. Cable `i` has
`d i + 1` slots. The sector density and support dimension are real scalars
embedded into the field of the tensor coefficients. -/
noncomputable def capGram (d : ι → ℕ) (s ρ : ℝ) : Matrix ι ι ℂ :=
  fun i j => ((ρ + (if i = j then s - ρ else 0) / (d i + 1 : ℝ) : ℝ) : ℂ)

/-- The last-cap Gram matrix is positive definite in every sector with
`s > ρ`. The constant component is pulled back from a one-dimensional
positive semidefinite diagonal matrix. -/
theorem capGram_posDef (d : ι → ℕ) (s ρ : ℝ) (hρ : 0 ≤ ρ) (hs : ρ < s) :
    (capGram d s ρ).PosDef := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (((s-ρ)/(d i+1 : ℝ) : ℝ) : ℂ))
  let B : Matrix Unit Unit ℂ := Matrix.diagonal (fun _ => (ρ : ℂ))
  have hd : D.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    exact div_pos (sub_pos.mpr hs) (by positivity)
  have hb : B.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro _
    exact Complex.zero_le_real.mpr hρ
  have heq : capGram d s ρ = D + B.submatrix (fun _ => ()) (fun _ => ()) := by
    ext i j
    by_cases hij : i = j <;> simp [capGram, D, B, Matrix.diagonal_apply,
      Matrix.submatrix, hij, add_comm]
  rw [heq]
  exact hd.add_posSemidef (hb.submatrix _)

/-- The projection obtained by gluing a column of cap maps with the inverse
of its Gram matrix. -/
noncomputable def gramProjection (C : Matrix ι ν ℂ) : Matrix ν ν ℂ :=
  Cᴴ * (C * Cᴴ)⁻¹ * C

/-- In a nonsingular sector the Gram construction is an orthogonal
projection: self-adjoint, idempotent, and with image precisely the image
of the reflected column of caps. -/
theorem gramProjection_spec (C : Matrix ι ν ℂ) (hG : (C * Cᴴ).PosDef) :
    (gramProjection C).IsHermitian ∧
    gramProjection C * gramProjection C = gramProjection C ∧
    Set.range (gramProjection C).mulVec = Set.range Cᴴ.mulVec := by
  classical
  have hu : IsUnit (C * Cᴴ).det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hfix : gramProjection C * Cᴴ = Cᴴ := by
    calc
      _ = Cᴴ * ((C * Cᴴ)⁻¹ * (C * Cᴴ)) := by simp [gramProjection, Matrix.mul_assoc]
      _ = Cᴴ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul C hG.inv.isHermitian, ?_, ?_⟩
  · change gramProjection C * ((Cᴴ * (C * Cᴴ)⁻¹) * C) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]
    rfl
  · apply Set.Subset.antisymm
    · rintro _ ⟨v, rfl⟩
      refine ⟨((C * Cᴴ)⁻¹ * C).mulVec v, ?_⟩
      simp [gramProjection, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rintro _ ⟨v, rfl⟩
      exact ⟨Cᴴ.mulVec v, by rw [Matrix.mulVec_mulVec, hfix]⟩

end Projection

/-! ## The combinatorics of the marked spectator -/

/-- A routing table between two rows of `m` clasps of thickness `k`. -/
structure Routing (m k : ℕ) where
  entries : Fin m → Fin m → ℕ
  rowSum : ∀ i, ∑ j, entries i j = k
  colSum : ∀ j, ∑ i, entries i j = k

namespace Routing

variable {m k : ℕ}

/-- A whole edge consumes all strands of its row and column. -/
def whole (M : Routing m k) : Finset (Fin m × Fin m) :=
  univ.filter (fun e => M.entries e.1 e.2 = k)

private theorem uniqueFull {n : ℕ} (f : Fin n → ℕ) (hs : ∑ x, f x = k)
    (hk : 0 < k) {x y : Fin n} (hx : f x = k) (hy : f y = k) : x = y := by
  by_contra hxy
  have h := Finset.sum_le_sum_of_subset (f := f) (Finset.subset_univ ({x, y} : Finset (Fin n)))
  simp [hxy, hs, hx, hy] at h
  omega

theorem whole_inputs_injective (M : Routing m k) (hk : 0 < k) :
    Set.InjOn Prod.fst (M.whole : Set (Fin m × Fin m)) := by
  rintro ⟨i,j⟩ hx ⟨i',j'⟩ hy hi
  change i = i' at hi
  subst i'
  congr 1
  apply uniqueFull _ (M.rowSum i) hk
  · exact (Finset.mem_filter.mp hx).2
  · exact (Finset.mem_filter.mp hy).2

theorem whole_outputs_injective (M : Routing m k) (hk : 0 < k) :
    Set.InjOn Prod.snd (M.whole : Set (Fin m × Fin m)) := by
  rintro ⟨i,j⟩ hx ⟨i',j'⟩ hy hj
  change j = j' at hj
  subst j'
  congr 1
  apply uniqueFull _ (M.colSum j) hk
  · exact (Finset.mem_filter.mp hx).2
  · exact (Finset.mem_filter.mp hy).2

def splitInputs (M : Routing m k) : Finset (Fin m) := univ \ M.whole.image Prod.fst

def splitOutputs (M : Routing m k) : Finset (Fin m) := univ \ M.whole.image Prod.snd

theorem splitInputs_add_whole (M : Routing m k) (hk : 0 < k) :
    M.splitInputs.card + M.whole.card = m := by
  rw [← Finset.card_image_of_injOn (M.whole_inputs_injective hk)]
  simpa [splitInputs] using (Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (M.whole.image Prod.fst)))

theorem splitOutputs_add_whole (M : Routing m k) (hk : 0 < k) :
    M.splitOutputs.card + M.whole.card = m := by
  rw [← Finset.card_image_of_injOn (M.whole_outputs_injective hk)]
  simpa [splitOutputs] using (Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (M.whole.image Prod.snd)))

theorem equal_split_counts (M : Routing m k) (hk : 0 < k) :
    M.splitInputs.card = M.splitOutputs.card := by
  have h₁ := M.splitInputs_add_whole hk
  have h₂ := M.splitOutputs_add_whole hk
  omega

/-- The four placements of a spectator whole edge relative to the marked
input and output. These weights are the moved, stationary and two crossed
terms, with the common factor `1/b` omitted. -/
def exitWeight (a : Fin m) (e : Fin m × Fin m) : ℚ :=
  if e.1 = a then
    if e.2 = a then -((m : ℚ) - 1) else -((m : ℚ) - 2)/2
  else
    if e.2 = a then -((m : ℚ) - 2)/2 else 1

/-- Relative coefficient in the transferred element after expanding the four
spectator exits, in units of the routing weight `w(M)`. -/
def transferred (M : Routing m k) (a : Fin m) : ℚ :=
  if M.splitInputs.card = 0 then 0 else
    1 + (∑ e ∈ M.whole, exitWeight a e) / (M.splitInputs.card : ℚ)

private theorem endpointSum {α β : Type*} [DecidableEq β]
    {s : Finset α} {f : α → β} (hf : Set.InjOn f ↑s) (a : β) :
    (∑ e ∈ s, if f e = a then (1 : ℚ) else 0) =
      if a ∈ s.image f then 1 else 0 := by
  rw [← Finset.sum_image (f := fun x => if x = a then (1 : ℚ) else 0)
    (fun _ hx _ hy h => hf hx hy h)]
  simp

/-- Which marked ends split? The signed sum over actual whole edges of a
routing table depends only on the splitting status of its marked ends.
The `b=0` case is included by the definition of the transfer. -/
theorem transferred_eq (M : Routing m k) (hk : 0 < k) (a : Fin m) :
    M.transferred a =
      (m : ℚ) / (2 * M.splitInputs.card) *
        ((if a ∈ M.splitInputs then 1 else 0) +
         (if a ∈ M.splitOutputs then 1 else 0)) := by
  classical
  have weight (e : Fin m × Fin m) :
      exitWeight a e = 1 - (m : ℚ)/2 *
        ((if e.1 = a then 1 else 0) + (if e.2 = a then 1 else 0)) := by
    unfold exitWeight
    by_cases hi : e.1 = a <;> by_cases hj : e.2 = a <;> simp [hi,hj] <;> ring
  have hi := endpointSum (M.whole_inputs_injective hk) a
  have ho := endpointSum (M.whole_outputs_injective hk) a
  have hb : (M.splitInputs.card : ℚ) + M.whole.card = m := by
    exact_mod_cast M.splitInputs_add_whole hk
  unfold transferred
  split
  next h => simp [h]
  next h =>
    simp_rw [weight]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hi, ho]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hb' : (M.splitInputs.card : ℚ) ≠ 0 := by exact_mod_cast h
    have hw : (M.whole.card : ℚ) = m - M.splitInputs.card := eq_sub_of_add_eq' hb
    rw [hw]
    have hsI : a ∈ M.splitInputs ↔ a ∉ M.whole.image Prod.fst := by
      simp only [splitInputs, Finset.mem_sdiff, Finset.mem_univ, true_and]
    have hsO : a ∈ M.splitOutputs ↔ a ∉ M.whole.image Prod.snd := by
      simp only [splitOutputs, Finset.mem_sdiff, Finset.mem_univ, true_and]
    simp only [hsI, hsO]
    by_cases ha : a ∈ M.whole.image Prod.fst <;> by_cases hc : a ∈ M.whole.image Prod.snd <;>
      simp only [ha, hc, if_true, if_false, not_true_eq_false, not_false_eq_true] <;>
      field_simp [hb'] <;> ring

/-- Relabeling the mark gives mean relative coefficient one on a split
routing; stated without division, the sum of its marked coefficients is m. -/
theorem transferred_sum (M : Routing m k) (hk : 0 < k) (hb : M.splitInputs.card ≠ 0) :
    (∑ a, M.transferred a) = (m : ℚ) := by
  classical
  have sumIndicator (s : Finset (Fin m)) :
      (∑ a, if a ∈ s then (1 : ℚ) else 0) = (s.card : ℚ) := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [M.transferred_eq hk]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sumIndicator, sumIndicator,
    ← M.equal_split_counts hk]
  have hb' : (M.splitInputs.card : ℚ) ≠ 0 := by exact_mod_cast hb
  field_simp [hb']
  ring_nf
  simp

/-- The normalized A coefficient as a function of the number of split inputs
and the number of whole edges. Each of the whole edges is an eligible
spectator deletion. At one step its denominator is the old packet count.
A whole table contributes zero at every step. -/
def relativeA (split : ℕ) : ℕ → ℚ
  | 0 => if split = 0 then 0 else 1
  | t+1 => if split = 0 then 0 else
      1 + ((t : ℚ)+1) / ((split : ℚ) + t) * relativeA split t

/-- Solves the scalar recurrence underlying the iterated packet transfer,
including the nonsplit case according to the totalized rational division. -/
theorem relativeA_eq (b t : ℕ) : relativeA b t = ((b : ℚ) + t) / b := by
  by_cases hb : b = 0
  · subst b
    cases t <;> simp [relativeA]
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  induction t with
  | zero => simp [relativeA, hb, hb']
  | succ t ih =>
    have hbt : (b : ℚ) + t ≠ 0 := by
      exact_mod_cast (show b+t ≠ 0 by omega)
    simp only [relativeA, hb, if_false, ih, Nat.cast_succ]
    field_simp [hb', hbt]

/-- The relative A coefficient of every actual routing table in terms of its
split rows. The table hypotheses supply the whole-edge count. -/
theorem relativeA_table (M : Routing m k) (hk : 0 < k) :
    relativeA M.splitInputs.card M.whole.card = (m : ℚ) / M.splitInputs.card := by
  have h : (M.splitInputs.card : ℚ) + M.whole.card = m := by
    exact_mod_cast M.splitInputs_add_whole hk
  rw [relativeA_eq, h]


end Routing

end BlockPermanents.Routings
