import BlockPermanents.ThreePlaneTheorem

/-! # Example 3D.4, all entries one

On a one-dimensional ambient space there is just one word at every
thickness. We evaluate the actual marked routes, their trace complement and
both terminal halves, then read the gap of the six-by-six all-ones Gram.
-/

namespace BlockPermanents.ThreeOnesExample
open Bend Closures ThreeGeneralOpen ThreeLastRouted SchurNormalization Support
open scoped Matrix BigOperators ComplexOrder
noncomputable section

/-- The unique mixed boundary word represents three copies of the unit tensor. -/
def boundary (k : ℕ) : ThreeWords 1 k := ((fun _ => 0, fun _ => 0), fun _ => 0)

private theorem clasp_one (k : ℕ) (w v : Word 1 k) : symClasp 1 k w v = 1 := by
  have e (σ : Equiv.Perm (Fin k)) : w = v ∘ σ := Subsingleton.elim _ _
  unfold symClasp
  simp_rw [if_pos (e _)]
  simp [Fintype.card_perm, Nat.factorial_ne_zero]

private theorem m_one {k : ℕ} (s w : Word 1 k) (i : Word 1 k × Word 1 k) :
    M 1 k s w i = 1 := by norm_num [M, clasp_one]

private theorem p_one {k : ℕ} (w : Word 1 (k+k)) (i : Word 1 k × Word 1 k) :
    P 1 k w i = 1 := clasp_one _ _ _

/-- The merged and unmerged routed halfwebs each have entry one at every cut. -/
theorem routes_one {k : ℕ} (r : CutIndex k k) (s : Word 1 k) (a b : Word 1 (k-r))
    (i : ThreeWords 1 k) :
    routed (M 1 k) (symClasp 1 k) r s (a,b) i = 1 := by
  rw [routed_entry _ _ (pair_symmetric 1 k) (column_symmetric 1 k)]
  simp [m_one, clasp_one, Word, Fintype.card_fun]

theorem fine_routes_one {k : ℕ} (r : CutIndex (k+k) k)
    (a : Word 1 (k+k-r)) (b : Word 1 (k-r)) (i : ThreeWords 1 k) :
    routed (fun _ : Unit => P 1 k) (symClasp 1 k) r () (a,b) i = 1 := by
  have hs (_s : Unit) (j : Word 1 k × Word 1 k) : Symmetric (fun w => P 1 k w j) :=
    column_symmetric 1 (k+k) (Fin.append j.1 j.2)
  rw [routed_entry (fun _ : Unit => P 1 k) (symClasp 1 k) hs (column_symmetric 1 k)]
  simp [p_one, clasp_one, Word, Fintype.card_fun]

/-- Both completed caps have the unique coefficient one. -/
theorem terminal_ones (k : ℕ) (s : Word 1 k) (i : ThreeWords 1 k) :
    terminal (stack (M 1 k)) (symClasp 1 k) s i = 1 ∧
      terminal (stackedFine (P 1 k)) (symClasp 1 k) s i = 1 := by
  simp [terminal, stack, stackedFine, m_one, p_one, clasp_one, Word, Fintype.card_fun]

/-- The final trace projection is the identity in dimension one. -/
theorem perpendicular_zero (k : ℕ) (hk : 1 ≤ k) :
    ThreePlane.perpendicular (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (stackLast hk (M 1 k) (symClasp 1 k)) = 0 := by
  have hcap : (ThreePlane.planeCap (T := Word 1 k) (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ *
      ThreePlane.planeCap (T := Word 1 k) (1 : Matrix (Fin 1) (Fin 1) ℂ) =
        (1 : Matrix (Word 1 k × ThreeLastCap.Pair 1) _ ℂ) := by
    ext i j
    simp [ThreePlane.planeCap, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Subsingleton.elim i j, Subsingleton.elim i.1 j.1, Subsingleton.elim (i.2.2 0) (i.2.1 0),
      Subsingleton.elim (j.2.2 0) (j.2.1 0), Fintype.card_fun, Word]
    simp [Subsingleton.elim j.1 (fun _ => 0), Subsingleton.elim (j.2.1 0) 0]
  simp [ThreePlane.perpendicular, hcap]

private theorem reflected_fine_one {k : ℕ} (r : CutIndex (k+k) k) (i : ThreeWords 1 k) :
    reflected (routed (fun _ : Unit => P 1 k) (symClasp 1 k) r ()) i i = 1 := by
  have h (q : Word 1 (k+k-r) × Word 1 (k-r)) := fine_routes_one r q.1 q.2 i
  simp [reflected, Matrix.mul_apply, Matrix.conjTranspose_apply, h, Fintype.card_prod,
    Word, Fintype.card_fun]

/-- The first families of proper cuts at k=2 contribute zero and 48. -/
theorem proper_terms (i : ThreeWords 1 2) :
    earlySquares (M 1 2) (symClasp 1 2) i i = 0 ∧
      (6:ℂ) * properSquares (k := 2) (p := 4) (by decide)
        (fun _ : Unit => P 1 2) (symClasp 1 2) i i = 48 := by
  have he : (middle 2 2 le_rfl).erase (ThreeSupport.lastProper 2) = ∅ := by decide
  have hp : middle 4 2 (by decide) = {1} := by decide
  simp [earlySquares, properSquares, he, hp, Matrix.smul_apply, reflected_fine_one,
    weight, Nat.choose]
  rw [reflected_fine_one (k := 2)]
  norm_num

/-- At thickness three the surviving earlier U route has weight 18. -/
theorem cubic_early_term (i : ThreeWords 1 3) :
    (2 : ℂ) * earlySquares (M 1 3) (symClasp 1 3) i i = 18 := by
  have he : (middle 3 3 le_rfl).erase (ThreeSupport.lastProper 3) = {1} := by decide
  have hr (s : Word 1 3) : reflected (routed (M 1 3) (symClasp 1 3) 1 s) i i = 1 := by
    have h (q : Word 1 (3-(1 : CutIndex 3 3).val) × Word 1 (3-(1 : CutIndex 3 3).val)) :
        routed (M 1 3) (symClasp 1 3) 1 s q i = 1 := routes_one (k := 3) 1 s q.1 q.2 i
    simp [reflected, Matrix.mul_apply, Matrix.conjTranspose_apply, h, Fintype.card_prod,
      Word, Fintype.card_fun]
  norm_num [earlySquares, he, Matrix.smul_apply, Matrix.sum_apply, hr,
    weight, Nat.choose, Word, Fintype.card_fun]

private theorem internal_one (k : ℕ) : internal 1 k = 1 := by
  ext i j
  simp [internal, legs, clasp_one, Matrix.one_apply, Subsingleton.elim i j]

/-- The diagonal entry of the original bent operator at the physical unit
packet boundary, with the nonvanishing terms of (3D.3) displayed. -/
theorem physical_terms :
    partialTranspose (original 1 2) (boundary 2) (boundary 2) =
      (48 : ℂ) + (6-1/2)^2 + (8-9/4) := by
  let C := symClasp 1 2
  let i := boundary 2
  have cut := ThreePlane.routed_resolution
    (1 : Matrix (Fin 1) (Fin 1) ℂ) (by simp) (by decide) (by decide : 1 ≤ 2)
    (M 1 2) C C (by rw [TensorCoordinates.power_one, Matrix.one_mul])
    (pair_symmetric 1 2) (column_symmetric 1 2)
  have eq := resolve_raw (by decide : 2 ≤ 2) (homogeneousSchur 1 2 2)
    (homogeneousSchur 1 4 2) (M 1 2) (P 1 2) C (pair_symmetric 1 2)
    (fun j => column_symmetric 1 4 (Fin.append j.1 j.2)) (column_symmetric 1 2) _ cut
  rw [← original_corrected, internal_one] at eq
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at eq
  have he := congrArg (fun A : Matrix (ThreeWords 1 2) (ThreeWords 1 2) ℂ => A i i) eq
  have u (s : Word 1 2) := (terminal_ones 2 s i).1
  have v (s : Word 1 2) := (terminal_ones 2 s i).2
  dsimp only [C] at he
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, perpendicular_zero,
    (proper_terms i).1, mul_zero, zero_add] at he
  norm_num [Nat.choose, (proper_terms i).2, reflected, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, u, v, Word, Fintype.card_fun] at he ⊢
  exact he

theorem normalized_gap : partialTranspose (original 1 2) (boundary 2) (boundary 2) = 84 := by
  rw [physical_terms]
  norm_num

/-- Six raw scalar atoms of unit value realize the all-ones Gram. -/
def atoms : Fin 3 → Fin 2 → Fin 1 → ℂ := fun _ _ _ => 1

def gram := crossGram (Function.uncurry atoms) (Function.uncurry atoms)

theorem gram_entries (i j : Fin 3 × Fin 2) : gram i j = 1 := by
  simp [gram, crossGram, bracket, atoms, Function.uncurry]

theorem gram_psd : gram.PosSemidef := ThreeFine.gram_psd (Function.uncurry atoms)

theorem raw_packet (i : Fin 3) (w : Word 1 2) :
    packet (atoms i) w = (Real.sqrt 2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  norm_num [packet, packetScale, orderSum, pureWord, atoms, Fintype.card_perm, Nat.factorial]
  field_simp
  linear_combination -h

/-- The actual three matrix packets evaluated in the original quadratic
form account for the factor eight on the normalized unit-tensor gap. -/
theorem raw_expectation :
    quadratic (original 1 2) (product (product (packet (atoms 0)) (packet (atoms 1)))
      (packet (atoms 2))) = 8 * partialTranspose (original 1 2) (boundary 2) (boundary 2) := by
  let t : ℂ := Real.sqrt 2
  have he (i j : ThreeWords 1 2) : original 1 2 i j =
      partialTranspose (original 1 2) (boundary 2) (boundary 2) := by
    rw [Subsingleton.elim i (boundary 2), Subsingleton.elim j (boundary 2)]
    rfl
  have ht : t^2 = 2 := by dsimp [t]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs : star t = t := Complex.conj_ofReal _
  have hc : Fintype.card (ThreeWords 1 2) = 1 := by simp [ThreeWords, K, Word, Fintype.card_prod, Fintype.card_fun]
  unfold quadratic
  simp only [product, raw_packet, he, Finset.sum_const, Finset.card_univ, hc,
    one_smul]
  change star (t*t*t) * _ * (t*t*t) = _
  simp only [star_mul', hs]
  linear_combination (partialTranspose (original 1 2) (boundary 2) (boundary 2)) * (t^4+2*t^2+4) * ht

theorem raw_permanents : gram.permanent = 720 ∧ (blockPermanentMatrix gram).permanent = 48 := by
  have hb (i j : Fin 3) : blockPermanentMatrix gram i j = 2 := by
    norm_num [blockPermanentMatrix, Matrix.permanent, Matrix.submatrix_apply, gram_entries,
      Fintype.card_perm, Nat.factorial]
  constructor
  · norm_num [Matrix.permanent, gram_entries, Fintype.card_perm, Fintype.card_prod, Nat.factorial]
  · norm_num [Matrix.permanent, hb, Fintype.card_perm, Finset.prod_const, Nat.factorial]

theorem raw_gap :
    gram.permanent - (blockPermanentMatrix gram).permanent =
      8 * partialTranspose (original 1 2) (boundary 2) (boundary 2) := by
  rw [raw_permanents.1, raw_permanents.2, normalized_gap]
  norm_num

end
end BlockPermanents.ThreeOnesExample
