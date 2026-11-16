import BlockPermanents.TraceBound
import BlockPermanents.Bend
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Positivity

/-! # Last-cap multiplicities of the balanced bend

The symmetric powers of the chosen k-plane are indexed by occupations.
The support can be embedded into any ambient word space; the columns of
the embedding need not be coordinate axes of that space. -/
namespace BlockPermanents.BalancedSupport
open Bend
noncomputable section

def occupation {k t : ℕ} (f : Fin t → Fin k) : Sym (Fin k) t :=
  ⟨∑ i, {f i},by simp⟩

def joinedOccupation {k a b : ℕ} (o : Sym (Fin k) a) (p : Sym (Fin k) b) : Sym (Fin k) (a+b) :=
  ⟨o.val+p.val,by simp⟩

private theorem occupation_append {k a b : ℕ} (p : Fin a → Fin k) (q : Fin b → Fin k) :
    occupation (Fin.append p q) = joinedOccupation (occupation p) (occupation q) := by
  apply Subtype.ext
  simp only [occupation,joinedOccupation,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

/-- The expansion of an occupation in a chosen plane basis into ambient
word coordinates, with U giving the basis vectors as columns. -/
def expand {d k t : ℕ} (U : Fin d → Fin k → ℂ) (o : Sym (Fin k) t)
    (w : Fin t → Fin d) : ℂ :=
  ∑ f : Fin t → Fin k, if occupation f = o then
    ∏ i, U (w i) (f i) else 0

def space {d k : ℕ} (t : ℕ) (U : Fin d → Fin k → ℂ) :=
  Submodule.span ℂ (Set.range (expand (t := t) U))

private theorem expand_append {d k a b : ℕ} (U : Fin d → Fin k → ℂ) (o : Sym (Fin k) (a+b))
    (w : Word d a) (v : Word d b) :
    expand U o (Fin.append w v) =
    ∑ g : Fin b → Fin k, ∑ p : Sym (Fin k) a,
      (if joinedOccupation p (occupation g)=o then ∏ i, U (v i) (g i) else 0) * expand U p w := by
  classical
  unfold expand
  rw [← (Fin.appendEquiv a b).sum_comp (fun f : Fin (a+b) → Fin k =>
    if occupation f = o then ∏ i, U (Fin.append w v i) (f i) else 0)]
  simp only [Fin.appendEquiv_apply, Fintype.sum_prod_type, occupation_append,Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [show (Fin.appendEquiv a b) (f,g) = Fin.append f g from rfl,occupation_append]
  split <;> simp_all [mul_comm]

/-- Freezing any trailing letters of a supported symmetric packet keeps
its remaining letters in the symmetric power of the same plane. -/
theorem slice_mem {d k a b : ℕ} (U : Fin d → Fin k → ℂ) {F : Word d (a+b) → ℂ}
    (hF : F ∈ space (a+b) U) (v : Word d b) :
    (fun w => F (Fin.append w v)) ∈ space a U := by
  classical
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨o,rfl⟩ := hf
    have he : (fun w => expand U o (Fin.append w v)) =
        ∑ g : Fin b → Fin k, ∑ p : Sym (Fin k) a,
          (if joinedOccupation p (occupation g)=o then ∏ i, U (v i) (g i) else 0) • expand U p := by
      funext w
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using expand_append U o w v
    rw [he]
    exact Submodule.sum_mem _ (fun _ _ => Submodule.sum_mem _ (fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p,rfl⟩)))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

theorem dimension {d k : ℕ} (t : ℕ) (U : Fin d → Fin k → ℂ) :
    Module.finrank ℂ (space t U) ≤ (k+t-1).choose t := by
  have h := finrank_range_le_card (R := ℂ) (expand (t := t) U)
  rw [Sym.card_sym_eq_choose, Fintype.card_fin] at h
  exact h

/-- Complete an arbitrary family of supported partial cap matrices.
Spectator indices are unrestricted. -/
theorem complete_trace {d k t : ℕ} {I : Type*} [Fintype I] (U : Fin d → Fin k → ℂ)
    (A : I → Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ)
    (supported : ∀ i j, (fun w => A i w j) ∈ space t U) :
    (∑ i, Complex.normSq (A i).trace) ≤
      ((k+t-1).choose t : ℝ) * ∑ i, ∑ w, ∑ v, Complex.normSq (A i w v) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (TraceBound.trace_normSq_le _ _ (supported i)).trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast dimension t U) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))

def weight (k r : ℕ) : ℝ :=
  (k.choose r : ℝ)^2 / ((k+(k-r)-1).choose (k-r) : ℝ)

def lastWeight (k : ℕ) : ℝ := ∑ r ∈ Finset.Ico 1 k, weight k r

theorem cubic_weight : lastWeight 3 = 9/2 := by
  norm_num [lastWeight, weight, show Finset.Ico 1 3 = ({1,2} : Finset ℕ) by decide, Nat.choose]

theorem fourth_weight : lastWeight 4 = 42/5 := by
  norm_num [lastWeight, weight, show Finset.Ico 1 4 = ({1,2,3} : Finset ℕ) by decide, Nat.choose]

private theorem final_two {k} (hk : 5 ≤ k) :
    weight k (k-1) + weight k (k-2) =
      (k:ℝ) + k*((k:ℝ)-1)^2/(2*((k:ℝ)+1)) := by
  have hk' : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  simp only [weight, Nat.choose_symm (by omega : 1 ≤ k), Nat.choose_symm (by omega : 2 ≤ k),
    show k-(k-1)=1 by omega, show k-(k-2)=2 by omega, show k+1-1=k by omega,
    show k+2-1=k+1 by omega, Nat.choose_one_right, Nat.cast_choose_two, Nat.cast_add,Nat.cast_one]
  field_simp
  ring

/-- The coefficient can absorb the four one-cap routes starting at k=4. -/
theorem eight_le {k : ℕ} (hk : 4 ≤ k) : 8 ≤ lastWeight k := by
  rcases hk.eq_or_lt with rfl | hk
  · rw [fourth_weight]; norm_num
  have hh : ({k-1,k-2} : Finset ℕ) ⊆ Finset.Ico 1 k := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rw [Finset.mem_Ico]; omega
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := weight k) hh
    (fun i _ _ => by unfold weight; positivity)
  rw [Finset.sum_pair (by omega : k-1 ≠ k-2), final_two (by omega)] at h
  apply le_trans _ h
  have hk' : 5 ≤ (k:ℝ) := by exact_mod_cast hk
  have hp : 0 < 2*((k:ℝ)+1) := by positivity
  rw [← sub_le_iff_le_add', le_div_iff₀ hp]
  nlinarith only [hk',mul_nonneg (sub_nonneg.mpr hk') (sq_nonneg ((k:ℝ)-1)),sq_nonneg ((k:ℝ)-5)]

end
end BlockPermanents.BalancedSupport
