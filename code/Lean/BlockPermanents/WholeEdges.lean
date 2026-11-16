import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Appendix B, “Counting whole edges at a mark”. Each routing has a finite
set of whole edges and an exact scalar weight. The marked input and output
can lie on the same edge, which then contributes two ends. -/
namespace BlockPermanents.WholeEdges
open scoped BigOperators Polynomial
open Polynomial Finset
noncomputable section

variable {E Ω : Type*} [DecidableEq E]

omit [DecidableEq E] in
private theorem all_subsets (s : Finset E) :
    ∑ D ∈ s.powerset, (X-1 : ℚ[X])^D.card = X^s.card := by
  have h := Finset.prod_one_add (f := fun _ : E => (X-1 : ℚ[X])) s
  simpa [add_comm (1 : ℚ[X])] using h.symm

private theorem subsets_at (s : Finset E) (e : E) (he : e ∈ s) :
    ∑ D ∈ s.powerset, (if e ∈ D then X*(X-1 : ℚ[X])^(D.card-1) else 0) = X^s.card := by
  classical
  conv_lhs => rw [← s.insert_erase he]
  rw [Finset.sum_powerset_insert (Finset.not_mem_erase _ _) ]
  have hne (D : Finset E) (hD : D ∈ (s.erase e).powerset) : e ∉ D :=
    Finset.not_mem_mono (Finset.mem_powerset.mp hD) (Finset.not_mem_erase _ _)
  rw [Finset.sum_eq_zero (fun D hD => if_neg (hne D hD)), zero_add]
  have hsum : (∑ D ∈ (s.erase e).powerset, (if e ∈ insert e D then X*(X-1 : ℚ[X])^((insert e D).card-1) else 0)) =
      X * ∑ D ∈ (s.erase e).powerset, (X-1 : ℚ[X])^D.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    simp [Finset.card_insert_of_not_mem (hne D hD)]
  rw [hsum, all_subsets, ← pow_succ', Finset.card_erase_add_one he]

/-- ν(e) counts marked ends on a forced edge, independently of the other
forced edges. The d=0 term in the second summand vanishes automatically. -/
def localPolynomial (ν : E → ℚ) (D : Finset E) : ℚ[X] :=
  2*(X-1)^D.card - (∑ e ∈ D, C (ν e)) * (X*(X-1)^(D.card-1))

theorem counting_subsets (s : Finset E) (ν : E → ℚ) :
    ∑ D ∈ s.powerset, localPolynomial ν D =
      C (2 - ∑ e ∈ s, ν e) * X^s.card := by
  classical
  have hmark (D : Finset E) (hD : D ∈ s.powerset) :
      (∑ e ∈ D, C (ν e)) * (X*(X-1)^(D.card-1)) =
      ∑ e ∈ s, C (ν e) * (if e ∈ D then X*(X-1)^(D.card-1) else 0) := by
    rw [Finset.sum_mul]
    have hh := Finset.sum_subset (Finset.mem_powerset.mp hD)
      (f := fun e => C (ν e) * (if e ∈ D then X*(X-1)^(D.card-1) else 0))
      (fun e _ he => by simp [he])
    rw [← hh]
    exact Finset.sum_congr rfl fun e he => by simp only [if_pos he]
  unfold localPolynomial
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, all_subsets,
    Finset.sum_congr rfl hmark, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have ht : (∑ e ∈ s, C (ν e) *
      ∑ D ∈ s.powerset, (if e ∈ D then X*(X-1 : ℚ[X])^(D.card-1) else 0)) =
      (∑ e ∈ s, C (ν e)) * X^s.card := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun e he => by rw [subsets_at s e he])
  rw [ht, map_sub, map_sum, sub_mul]
  norm_num [map_ofNat]

variable [Fintype E] [Fintype Ω]

/-- Total weight of routings that contain all of the prescribed edges. -/
def forced (whole : Ω → Finset E) (w : Ω → ℚ) (D : Finset E) : ℚ :=
  ∑ ω, if D ⊆ whole ω then w ω else 0

/-- Polynomial B_t from all forced-edge contributions. Incompatible edge
sets have forced weight zero and may be included in the sum. -/
def certificate (whole : Ω → Finset E) (w : Ω → ℚ) (ν : E → ℚ) : ℚ[X] :=
  ∑ D : Finset E, C (forced whole w D) * localPolynomial ν D

/-- After inclusion–exclusion the coefficient of one routing is its
weight times the number of split marked ends, at its own whole-edge degree. -/
theorem certificate_routes (whole : Ω → Finset E) (w : Ω → ℚ) (ν : E → ℚ) :
    certificate whole w ν = ∑ ω, C (w ω * (2-∑ e ∈ whole ω, ν e)) * X^(whole ω).card := by
  classical
  simp only [certificate, forced, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  have h : (∑ D : Finset E, C (if D ⊆ whole ω then w ω else 0) * localPolynomial ν D) =
      C (w ω) * ∑ D ∈ (whole ω).powerset, localPolynomial ν D := by
    rw [Finset.mul_sum]
    simp only [apply_ite C, map_zero, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext D
    simp
  rw [h, counting_subsets, map_mul, mul_assoc]

/-- Extract the h-th coefficient of the forced-edge polynomial. -/
theorem coefficient (whole : Ω → Finset E) (w : Ω → ℚ) (ν : E → ℚ) (h : ℕ) :
    (certificate whole w ν).coeff h =
    ∑ ω, if (whole ω).card = h then w ω * (2-∑ e ∈ whole ω, ν e) else 0 := by
  rw [certificate_routes, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro ω _
  change (C _ * X^_).coeff h = _
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp_all

/-- Appendix B's marked transfer readout, for any number of packet slots.
The h=m term is omitted because every end of every packet is whole. -/
theorem marked_readout (m : ℕ) (whole : Ω → Finset E) (w : Ω → ℚ) (ν : E → ℚ) :
    ∑ h ∈ Finset.range m, (m : ℚ)/(2*(m-h : ℕ)) * (certificate whole w ν).coeff h =
    ∑ ω, if (whole ω).card < m then
      ((m : ℚ)/(2*(m-(whole ω).card : ℕ))) * w ω * (2-∑ e ∈ whole ω, ν e) else 0 := by
  simp only [coefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [mul_ite, ← mul_assoc]

end
end BlockPermanents.WholeEdges
