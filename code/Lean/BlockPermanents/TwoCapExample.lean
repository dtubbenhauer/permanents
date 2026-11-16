import BlockPermanents.SupportCoordinates

/-! # Two reflected one-strand caps sharing one word, Example 5A.2 -/
namespace BlockPermanents.TwoCapExample
open scoped InnerProductSpace
noncomputable section

abbrev Word := Fin 2 × Fin 2 × Fin 2
abbrev Space := EuclideanSpace ℂ Word

/-- Ordinary slots are the first two coordinates, the dual slot is last. -/
def route (i s t : Fin 2) : Word := if i = 0 then (t,s,t) else (s,t,t)

/-- Contract ordinary slot i with the dual slot, leaving the letter s. -/
def cap (i : Fin 2) (v : Space) (s : Fin 2) : ℂ := ∑ t, v (route i s t)

def word (w : Word) : Space := EuclideanSpace.single w 1

/-- Reflect the cap with the output basis letter a (index zero). -/
def row (i : Fin 2) : Space := ∑ t, word (route i 0 t)

def shared : Space := word (0,0,0)

/-- The two reflected cap rows act by the prescribed partial contractions. -/
theorem cap_row (i : Fin 2) (v : Space) : @inner ℂ _ _ (row i) v = cap i v 0 := by
  simp only [row, cap, sum_inner, word, EuclideanSpace.inner_single_left, map_one, one_mul]

theorem rows : row 0 = shared + word (1,0,1) ∧ row 1 = shared + word (0,1,1) := by
  simp [row, route, shared, Fin.sum_univ_two]

/-- The concrete Gram entries include the single word kept by both caps. -/
theorem gram (i j : Fin 2) : @inner ℂ _ _ (row i) (row j) = if i=j then 2 else 1 := by
  rw [cap_row]
  fin_cases i <;> fin_cases j <;> norm_num [cap, row, route, word, Fin.sum_univ_two]

theorem shared_pair (i : Fin 2) : @inner ℂ _ _ (row i) shared = 1 := by
  rw [cap_row]
  fin_cases i <;> norm_num [cap, word, shared, route, Fin.sum_univ_two]

def line (i : Fin 2) : Submodule ℂ Space := ℂ ∙ row i

def both : Submodule ℂ Space := line 0 ⊔ line 1

theorem single_projection (i : Fin 2) :
    ((line i).orthogonalProjection shared : Space) = (1/2 : ℂ) • row i := by
  apply Submodule.eq_orthogonalProjection_of_mem_orthogonal
  · exact (line i).smul_mem _ (Submodule.mem_span_singleton_self _)
  · rw [line, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      shared_pair, gram]
    norm_num

theorem joint_projection :
    (both.orthogonalProjection shared : Space) = (1/3 : ℂ) • (row 0 + row 1) := by
  apply Submodule.eq_orthogonalProjection_of_mem_orthogonal
  · apply both.smul_mem
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
  · rw [both, ← Submodule.inf_orthogonal, Submodule.mem_inf]
    constructor <;> rw [line, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      shared_pair, inner_smul_right, inner_add_right, gram, gram] <;> norm_num

/-- Each separate projection has squared norm one half. -/
theorem separate_energy (i : Fin 2) : ‖(line i).orthogonalProjection shared‖^2 = 1/2 := by
  change ‖((line i).orthogonalProjection shared : Space)‖^2 = _
  rw [single_projection, norm_sq_eq_re_inner (𝕜 := ℂ), inner_smul_left, inner_smul_right, gram]
  norm_num

/-- Joint orthogonal projection of the shared word has squared norm two thirds. -/
theorem joint_energy : ‖both.orthogonalProjection shared‖^2 = 2/3 := by
  change ‖(both.orthogonalProjection shared : Space)‖^2 = _
  rw [joint_projection, norm_sq_eq_re_inner (𝕜 := ℂ), inner_smul_left, inner_smul_right]
  simp only [inner_add_left, inner_add_right, gram]
  norm_num

end
end BlockPermanents.TwoCapExample
