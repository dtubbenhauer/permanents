import BlockPermanents.CyclePlans
import Mathlib.GroupTheory.Perm.Centralizer

/-! # Ten-label cycle estimate of Appendix A -/
namespace BlockPermanents.CycleTen
open CycleMatching CycleComposition CyclePolynomial CyclePlans CycleCoefficients
noncomputable section

def label {m : ℕ} (τ : S m) : List ℕ := τ.partition.parts.sort (· ≤ ·)
def nontriv (l : List ℕ) : Multiset ℕ := l.filter (· > 1)

theorem label_mem {m} (τ : S m) : label τ ∈ partitions m := by
  apply mem_partitions
  · intro a ha
    exact τ.partition.parts_pos ((Multiset.mem_sort _).mp ha)
  · have hi := τ.partition.parts_sum
    rw [← Multiset.sort_eq (· ≤ ·) τ.partition.parts, Multiset.sum_coe] at hi
    simpa using hi
  · exact Multiset.sort_sorted _ _

theorem label_type {m} (τ : S m) : nontriv (label τ) = τ.cycleType := by
  have h := Equiv.Perm.filter_parts_partition_eq_cycleType (σ := τ)
  rw [← Multiset.sort_eq (· ≤ ·) τ.partition.parts] at h
  exact h

def classCard (m : ℕ) (l : List ℕ) : ℕ :=
  let s := nontriv l
  if s.sum ≤ m ∧ ∀ a ∈ s, 2 ≤ a then
    m.factorial / ((m-s.sum).factorial * s.prod * ∏ n ∈ s.toFinset, (s.count n).factorial)
  else 0

private theorem fiber_card {m} (l : List ℕ) (hc : classCard m l = classSize m l) :
    (Finset.univ.filter (fun τ : S m => label τ = l)).card ≤ classSize m l := by
  calc
    _ ≤ (Finset.univ.filter (fun τ : S m => τ.cycleType = nontriv l)).card := by
      apply Finset.card_le_card
      intro τ ht
      obtain ⟨_,ht⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht ▸ (label_type τ).symm⟩
    _ = _ := by
      rw [Equiv.Perm.card_of_cycleType, Fintype.card_fin, ← hc]
      rfl

/-- Summing the bounds for actual representatives yields the bound for the
permanent. Class multiplicities use the centralizer formula. -/
theorem partition_bound {m} (g : Gram m) (hg : UnitGram g)
    (hplans : ∀ l ∈ partitions m, Realizes m (l.filter (· > 1)) (planPolynomial (plan l)))
    (hclasses : ∀ l ∈ partitions m, classCard m l = classSize m l) (hn : (partitions m).Nodup) :
    (Matrix.permanent g).re ≤ ((partitions m).map (fun l =>
      (classSize m l : ℝ) * evaluate g (planPolynomial (plan l)))).sum := by
  let T := (partitions m).toFinset
  have cover (τ : S m) (_ : τ ∈ Finset.univ) : label τ ∈ T := List.mem_toFinset.mpr (label_mem τ)
  rw [permanent_sum, ← Finset.sum_fiberwise_of_maps_to cover]
  rw [← List.sum_toFinset _ hn]
  apply Finset.sum_le_sum
  intro l hl
  have hl' := List.mem_toFinset.mp hl
  obtain ⟨π,hπ,hp⟩ := hplans l hl'
  have hb := hp.2 g hg
  let F := Finset.univ.filter (fun τ : S m => label τ = l)
  calc
    _ ≤ ∑ _τ ∈ F, evaluate g (planPolynomial (plan l)) := by
      apply Finset.sum_le_sum
      intro τ ht
      have he := (Finset.mem_filter.mp ht).2
      have ht' : τ.cycleType = π.cycleType := by rw [← label_type τ,he,hπ]; rfl
      rw [mean_conjugate g (Equiv.Perm.isConj_iff_cycleType_eq.mpr ht')]
      exact (le_abs_self _).trans hb
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_card l (hclasses l hl')) ((abs_nonneg _).trans hb)

def scale (a : ℚ) (p : Polynomial) : Polynomial := p.map (fun t => (t.1,a*t.2))
def matchedPolynomial (m : ℕ) : Polynomial :=
  (partitions m).flatMap (fun l => scale (classSize m l) (planPolynomial (plan l)))

abbrev fullPolynomial := matchedPolynomial 10

private theorem evaluate_scale {m} (g : Gram m) (a : ℚ) (p : Polynomial) :
    evaluate g (scale a p) = (a:ℝ)*evaluate g p := by
  induction p with
  | nil => simp [scale,evaluate]
  | cons t p ih =>
    simp only [scale, List.map_cons, evaluate, List.sum_cons] at ih ⊢
    rw [ih,Rat.cast_mul,mul_add,mul_assoc]

private theorem evaluate_groups {m} (g : Gram m) (L : List (List ℕ)) :
    evaluate g (L.flatMap (fun l => scale (classSize m l) (planPolynomial (plan l)))) =
      (L.map (fun l => (classSize m l : ℝ)*evaluate g (planPolynomial (plan l)))).sum := by
  induction L with
  | nil => simp [evaluate]
  | cons l L ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [show ∀ x y, evaluate g (x++y) = evaluate g x + evaluate g y by simp [evaluate],
      evaluate_scale, ih, Rat.cast_natCast]

def coeff (p : Polynomial) (j : ℕ) : ℚ := (p.map (fun t => if t.1 = j then t.2 else 0)).sum

private theorem evaluate_dense {m n} (g : Gram m) (p : Polynomial)
    (h : ∀ t ∈ p, t.1<n ∨ t.2=0) :
    evaluate g p = ∑ j ∈ Finset.range n, (coeff p j : ℝ) * Z g j := by
  induction p with
  | nil => simp [evaluate,coeff]
  | cons t p ih =>
    have ht := h t (by simp)
    have he := ih (fun x hx => h x (by simp [hx]))
    simp only [coeff, List.map_cons, List.sum_cons, Rat.cast_add, add_mul, Finset.sum_add_distrib] at he ⊢
    change (t.2 : ℝ)*Z g t.1 + evaluate g p = _
    rw [he]
    congr 1
    simp only [apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_range]
    rcases ht with hlt | hz
    · simp [hlt]
    · simp [hz]

set_option maxRecDepth 100000 in
private theorem class_check_ten : ∀ l ∈ partitions 10, classCard 10 l = classSize 10 l := by decide +kernel

set_option maxRecDepth 100000 in
private theorem class_check_six : ∀ l ∈ partitions 6, classCard 6 l = classSize 6 l := by decide +kernel

set_option maxRecDepth 100000 in
theorem ten_partition_bound (g : Gram 10) (hg : UnitGram g) :
    (Matrix.permanent g).re ≤ ((partitions 10).map (fun l =>
      (classSize 10 l : ℝ) * evaluate g (planPolynomial (plan l)))).sum :=
  partition_bound g hg (fun _ => ten_realizes) class_check_ten (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem ten_data : (List.range 6).map (coeff fullPolynomial) =
    [1,130,143339/15,555911/2,2126771,1349585] := by decide +kernel

set_option maxRecDepth 100000 in
private theorem ten_support : ∀ t ∈ fullPolynomial, t.1 < 6 ∨ t.2 = 0 := by decide +kernel

/-- The numerical matching polynomial in the ten-packet example bounds
the permanent of every unit Gram matrix. -/
theorem ten_cycle_bound (g : Gram 10) (hg : UnitGram g) :
    (Matrix.permanent g).re ≤ ∑ j ∈ Finset.range 6, (coeff fullPolynomial j : ℝ)*Z g j := by
  rw [← evaluate_dense g _ ten_support]
  exact (ten_partition_bound g hg).trans_eq (evaluate_groups g _).symm

set_option maxRecDepth 100000 in
theorem six_data : (List.range 4).map (coeff (matchedPolynomial 6)) = [1,35,392,313] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The six-label polynomial obtained by evenly distributing fixed labels. -/
theorem six_cycle_bound (g : Gram 6) (hg : UnitGram g) :
    (Matrix.permanent g).re ≤ ∑ j ∈ Finset.range 4, (coeff (matchedPolynomial 6) j : ℝ)*Z g j := by
  have hs : ∀ t ∈ matchedPolynomial 6, t.1 < 4 ∨ t.2 = 0 := by decide +kernel
  rw [← evaluate_dense g _ hs]
  exact (partition_bound g hg (fun _ => six_realizes) class_check_six (by decide +kernel)).trans_eq
    (evaluate_groups g _).symm

end
end BlockPermanents.CycleTen
