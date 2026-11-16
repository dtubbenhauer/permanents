import BlockPermanents.CycleUnbounded
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Independent positive real parameters in the disjoint-cycle formula -/
namespace BlockPermanents.CycleParameters
open CycleMatching CycleComposition CyclePolynomial CyclePlans CycleUnbounded Filter
open scoped Topology
noncomputable section

/-- Apply the product of the cycle factors to a sequence of moments,
starting at degree j. In particular, a factor z^a shifts the index by a. -/
def score : List Piece → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
  | [],_,F,j => F j
  | .fixed _ :: t,u,F,j => score t (fun i => u (i+1)) F j
  | .even r :: t,u,F,j => score t (fun i => u (i+1)) F (j+(r+1))
  | .odd r s :: t,u,F,j =>
    ((u 0/(s+1) + 1/u 0)/2) * score t (fun i => u (i+1)) F (j+(r+1)) +
      (s/(2*u 0)) * score t (fun i => u (i+1)) F (j+(r+2))

private def shifted (p : CyclePolynomial.Polynomial) (F : ℕ → ℝ) (j : ℕ) :=
  (p.map (fun x => (x.2:ℝ)*F (j+x.1))).sum

private theorem shifted_combine (a : ℕ × ℚ) (p q : CyclePolynomial.Polynomial) (F : ℕ → ℝ) (j : ℕ) :
    shifted (combine (a::p) q) F j = (a.2:ℝ)*shifted q F (j+a.1) + shifted (combine p q) F j := by
  simp only [combine,List.flatMap_cons,shifted,List.map_append,List.sum_append,List.map_map,
    Function.comp_apply,Rat.cast_mul,← mul_assoc,← Nat.add_assoc]
  rw [←List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp [Function.comp_def,Rat.cast_mul,Nat.add_assoc,mul_assoc]

private theorem rational (p : List Piece) (u : ℕ → ℚ) (F : ℕ→ℝ) (j : ℕ) :
    shifted (selectedPolynomial p u) F j = score p (fun i => (u i:ℝ)) F j := by
  induction p generalizing u j with
  | nil => simp [shifted,selectedPolynomial,score]
  | cons a p ih =>
    cases a <;> simp [selectedPolynomial,piecePolynomial,CycleCuts.oddPolynomial,score,shifted_combine,
      show ∀ z F j, shifted (combine [] z) F j=0 by simp [shifted,combine], ih,Nat.add_assoc]

private theorem limit (p : List Piece) (F : ℕ → ℝ) (j : ℕ) (v : ℕ → ℕ → ℝ) (u : ℕ → ℝ)
    (h : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (u i))) (hu : ∀ i, 0<u i) :
    Tendsto (fun n => score p (v n) F j) atTop (𝓝 (score p u F j)) := by
  induction p generalizing j v u with
  | nil => exact tendsto_const_nhds
  | cons a p ih =>
    have tail (j) := ih j (fun n i => v n (i+1)) (fun i => u (i+1)) (fun i => h (i+1)) (fun i => hu (i+1))
    cases a with
    | fixed => exact tail j
    | even r => exact tail (j+(r+1))
    | odd r s =>
      have h₁ := (h 0).div_const ((s:ℝ)+1)
      have h₂ := (tendsto_const_nhds (x:=(1:ℝ))).div (h 0) (ne_of_gt (hu 0))
      have h₃ := (tendsto_const_nhds (x:=(s:ℝ))).div
        ((tendsto_const_nhds (x:=(2:ℝ))).mul (h 0)) (mul_ne_zero (by norm_num) (ne_of_gt (hu 0)))
      exact (((h₁.add h₂).div_const 2).mul (tail _)).add (h₃.mul (tail _))

/-- The signed class-mean estimate for any assignment of fixed points,
any independent positive real u_i, and any representative of its cycle type. -/
theorem class_bound (p : List Piece) (u : ℕ → ℝ) (hu : ∀ i, 0<u i)
    (τ : S (planSize p)) (hτ : τ.cycleType = (planParts p : Multiset ℕ))
    (g : Gram (planSize p)) (hg : UnitGram g) : |(mean g τ).re| ≤ score p u (Z g) 0 := by
  choose v _ above hv using fun i => Real.exists_seq_rat_strictAnti_tendsto (u i)
  apply ge_of_tendsto' (limit p (Z g) 0 (fun n i => (v i n : ℝ)) u hv hu)
  intro n
  have plus (i) : 0<v i n := by exact_mod_cast (hu i).trans (above i n)
  obtain ⟨π,hπ,hb⟩ := selected_realizes p (fun i => v i n) plus
  rw [mean_conjugate g (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hτ.trans hπ.symm)),
    ← rational p (fun i => v i n)]
  simpa only [evaluate,shifted,zero_add] using hb.2 g hg

/-- The coefficient of z^j in the product of the local factors, obtained by
applying the same product to the j-th coordinate functional. -/
def pcoeff (p : List Piece) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  score p u (fun a => if a=j then 1 else 0) 0

private theorem score_smul (p : List Piece) (u : ℕ → ℝ) (F : ℕ→ℝ) (j : ℕ) (a : ℝ) :
    score p u (fun t => a*F t) j = a * score p u F j := by
  induction p generalizing j u with
  | nil => rfl
  | cons x p ih =>
    cases x <;> simp only [score,ih]
    ring

private theorem score_sum {I : Type} (p : List Piece) (u : ℕ→ℝ) (F : I→ℕ→ℝ)
    (s : Finset I) (j : ℕ) : score p u (fun t => ∑ i ∈ s, F i t) j = ∑ i ∈ s, score p u (F i) j := by
  induction p generalizing j u with
  | nil => rfl
  | cons x p ih =>
    cases x <;> simp only [score,ih,Finset.mul_sum,Finset.sum_add_distrib]

theorem class_bound_sum (p : List Piece) (u : ℕ → ℝ) (hu : ∀ i, 0<u i)
    (τ : S (planSize p)) (hτ : τ.cycleType = (planParts p : Multiset ℕ))
    (g : Gram (planSize p)) (hg : UnitGram g) :
    |(mean g τ).re| ≤ ∑ j ∈ Finset.range (planSize p/2+1), pcoeff p u j * Z g j := by
  have he : Z g = fun t => ∑ j ∈ Finset.range (planSize p/2+1),
      Z g j * (if t=j then 1 else 0) := by
    funext t
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_range]
    split_ifs with h
    · rfl
    · exact Z_outside g (by omega)
  apply (class_bound p u hu τ hτ g hg).trans_eq
  conv_lhs => rw [he]
  rw [score_sum]
  apply Finset.sum_congr rfl;intro t _
  exact (score_smul p u (fun a => if a=t then 1 else 0) 0 (Z g t)).trans (mul_comm ..)

end
end BlockPermanents.CycleParameters
