import BlockPermanents.ThreeMarkedAverage

/-! # Fixed-boundary transfer and its packet average, Example 3B.4 -/
namespace BlockPermanents.MarkedBoundaryExample
open Bend ThreeGeneralOpen ThreeMarkedAverage TransferBlocks
open scoped Matrix
noncomputable section

abbrev Index := ThreeWords 2 2
abbrev Operator := Matrix Index Index ℂ
def mono (a : Fin 2) : Word 2 2 := fun _ => a
def basis (a b c : Fin 2) : Index := ((mono a,mono b),mono c)
abbrev w := basis 0 0 1
abbrev B := firstFine 2 2
abbrev B' := secondFine 2 2
abbrev u := swapFront 2 2
abbrev t : Operator := ThreeTransfer.cross
abbrev f := pair u

private theorem pair_value (a b : Fin 2) :
    totalClasp 2 2 2 (mono a,mono b) (mono a,mono b) = if a=b then 1 else 1/6 := by
  let v := Fin.append (mono a) (mono b)
  have h : (Finset.univ.filter (fun p : Equiv.Perm (Fin 4) => v = v ∘ p)).card =
      if a=b then 24 else 4 := by
    dsimp [v]; fin_cases a <;> fin_cases b <;> decide +kernel
  simp only [totalClasp,symClasp,Finset.sum_boole]
  change ((4).factorial:ℂ)⁻¹ * ((Finset.univ.filter (fun p : Equiv.Perm (Fin 4) => v = v ∘ p)).card : ℂ) = _
  rw [h]
  split_ifs <;> norm_num [Nat.factorial]

private theorem first_value (a b c : Fin 2) :
    B (basis a b c) (basis a b c) = if a=b then 1 else 1/6 := by
  simpa [B, firstFine, ThreeTransfer.upright, basis] using pair_value a b

private theorem second_value (a b c : Fin 2) :
    B' (basis a b c) (basis a b c) = if b=c then 1 else 1/6 := by
  simpa [B', secondFine, basis] using pair_value b c

private theorem front_left (A : Operator) (j : Index) : (f*A) w j = A w j := by
  simp only [f,pair,smul_mul_assoc,add_mul,one_mul, Matrix.smul_apply, Matrix.add_apply, front_mul]
  change (1/2:ℚ) • (A w j+A w j) = _
  norm_num [Rat.smul_def]; ring

private theorem front_right (A : Operator) (i : Index) : (A*f) i w = A i w := by
  simp only [f,pair,mul_smul_comm,mul_add,mul_one,Matrix.smul_apply,Matrix.add_apply,
    u,← ThreeMarkedAverage.front, rep_right]
  change (1/2:ℚ) • (A i w+A i w) = _
  norm_num [Rat.smul_def]; ring

private theorem different : mono 0 ≠ mono 1 := by
  intro h; have he := congrFun h 0; contradiction

/-- The four diagrams on x² ⊗ x² ⊗ y² have values 1, 1/6, 0, 0. -/
theorem drawings : B w w = 1 ∧ (f*B'*f) w w = 1/6 ∧
    (B*t*f) w w = 0 ∧ (f*t*B) w w = 0 := by
  refine ⟨by simpa using first_value 0 0 1, ?_, ?_, ?_⟩
  · rw [front_right, front_left]
    simpa using second_value 0 0 1
  · rw [front_right, show t = rep _ lastSwap from (back _ _).symm, rep_right]
    change firstFine 2 2 w (basis 0 1 0) = 0
    simp only [firstFine, ThreeTransfer.upright, basis, if_neg (Ne.symm different)]
  · rw [Matrix.mul_assoc, front_left, show t = rep _ lastSwap from (back _ _).symm, rep_left]
    change firstFine 2 2 (basis 0 1 0) w = 0
    simp only [firstFine, ThreeTransfer.upright, basis, if_neg different]

def moved : Operator := (2:ℚ) • (f*B'*f) - (1/2:ℚ) • (B*t*f + f*t*B)

theorem fixed_boundary : B w w = 1 ∧ moved w w = 1/3 := by
  refine ⟨drawings.1, ?_⟩
  simp only [moved, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, drawings.2.1,
    drawings.2.2.1, drawings.2.2.2]
  norm_num [Rat.smul_def]

private theorem average_eq : Transfer.bracket (rep (Word 2 2)) moved = Transfer.bracket (rep _) B := by
  have h := average_correction 2 2
  have he : movedDifference u t B = moved-B := by
    have shift := shifted 2 2
    change (u*t*u)*B*(u*t*u)=B' at shift
    simp only [movedDifference, moved]
    rw [show f * (u*t*u)*B*(u*t*u)*f = f*((u*t*u)*B*(u*t*u))*f by simp only [Matrix.mul_assoc],
      shift]
    have ht : pair t = (1/2 : ℚ) • (1+t) := rfl
    simp only [ht, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
      one_mul, mul_one, smul_add, pair_first, first_pair]
    module
  change Transfer.bracket _ (movedDifference u t B) = 0 at h
  rwa [he, map_sub, sub_eq_zero] at h

/-- Relabelling both ends makes the two values equal to four ninths. -/
theorem averaged :
    Transfer.bracket (rep (Word 2 2)) B w w = 4/9 ∧
    Transfer.bracket (rep (Word 2 2)) moved w w = 4/9 := by
  rw [average_eq, and_self]
  change ((Fintype.card G : ℚ)⁻¹ • ∑ p : G, rep (Word 2 2) p * B * rep (Word 2 2) p⁻¹ : Operator) w w = _
  simp only [Matrix.smul_apply, Matrix.sum_apply, six, rep_right, rep_left]
  change (Fintype.card G : ℚ)⁻¹ • (B (basis 0 0 1) (basis 0 0 1) +
      B (basis 0 0 1) (basis 0 0 1) + B (basis 0 1 0) (basis 0 1 0) +
      B (basis 0 1 0) (basis 0 1 0) + B (basis 1 0 0) (basis 1 0 0) +
      B (basis 1 0 0) (basis 1 0 0)) = _
  simp only [first_value]
  norm_num [Rat.smul_def, G, Fintype.card_perm, Nat.factorial]

end
end BlockPermanents.MarkedBoundaryExample
