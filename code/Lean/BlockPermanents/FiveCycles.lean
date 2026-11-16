import BlockPermanents.Closures
import BlockPermanents.Statement
import BlockPermanents.FiveConjugacy
import BlockPermanents.FiveMean
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # The seven permutation types on five labeled packets (Section 8C)
Slots 0,1,2,3,4 carry G,F,H,I,J respectively. All averages range over
all 120 assignments, including assignments of equal-valued packets.
-/
namespace BlockPermanents.FiveCycles
open scoped ComplexConjugate
abbrev Gram := Matrix (Fin 5) (Fin 5) ℂ

noncomputable section
def edge (g : Gram) (σ : S) (i j : Fin 5) : ℂ := g (σ i) (σ j)
def viaH (g : Gram) (σ : S) : ℂ := edge g σ 0 2 * edge g σ 2 1
def P (g : Gram) : ℝ := avg (fun σ => Complex.normSq (edge g σ 0 1))
def U (g : Gram) : ℝ := avg (fun σ => Complex.normSq (edge g σ 3 4) * Complex.normSq (edge g σ 0 1))
def V (g : Gram) : ℝ := avg (fun σ => Complex.normSq (edge g σ 3 4) * Complex.normSq (viaH g σ))
def theta (g : Gram) : ℝ := avg (fun σ => (conj (edge g σ 0 1) * viaH g σ).re)
def thetaPair (g : Gram) : ℝ := avg (fun σ => Complex.normSq (edge g σ 3 4) *
  (conj (edge g σ 0 1) * viaH g σ).re)

private def straight (g : Gram) (σ : S) := edge g σ 0 1 * edge g σ 3 4
private def fourExit (g : Gram) (σ : S) := edge g σ 0 4 * edge g σ 3 1
private def fiveExit (g : Gram) (σ : S) := edge g σ 0 2 * edge g σ 3 1 * edge g σ 2 4
def C4 (g : Gram) := avg fun σ => (conj (straight g σ) * fourExit g σ).re
def C5 (g : Gram) := avg fun σ => (conj (straight g σ) * fiveExit g σ).re

private def term (g : Gram) (σ τ : S) : ℝ := (∏ i, edge g σ (τ i) i).re
private def meanTerm (g : Gram) (τ : S) : ℝ := avg fun σ => term g σ τ

private theorem mean_representative (g : Gram) (τ : S) :
    meanTerm g τ = meanTerm g (Conjugacy.rep (Conjugacy.kind τ)) := by
  obtain ⟨π,h⟩ := Conjugacy.classifies τ
  let r := Conjugacy.rep (Conjugacy.kind τ)
  have hh (σ : S) : term g (σ*π) r = term g σ τ := by
    unfold term
    apply congrArg Complex.re
    apply Fintype.prod_equiv π
    intro i
    simp only [edge, Equiv.Perm.mul_apply, r, h]
  unfold meanTerm
  simpa only [hh] using avg_relabel π (fun σ => term g σ r)

private theorem permanent_classes (g : Gram) :
    g.permanent.re = ∑ k, (Conjugacy.size k : ℝ) * meanTerm g (Conjugacy.rep k) := by
  have rel (σ : S) : ∑ τ, term g σ τ = g.permanent.re := by
    change (∑ τ : S, (∏ i, (g.submatrix σ σ) (τ i) i).re) = _
    rw [← Complex.re_sum]
    exact congrArg Complex.re (permanent_reindex σ g)
  calc
    _ = avg (fun _ => g.permanent.re) := (avg_const _).symm
    _ = avg (fun σ => ∑ τ, term g σ τ) := by simp only [rel]
    _ = ∑ τ, meanTerm g τ := avg_sum _
    _ = ∑ k, ∑ τ ∈ Finset.univ.filter (fun τ => Conjugacy.kind τ = k), meanTerm g τ :=
      (Finset.sum_fiberwise Finset.univ Conjugacy.kind _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = ∑ _τ ∈ Finset.univ.filter (fun τ => Conjugacy.kind τ = k), meanTerm g (Conjugacy.rep k) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          rw [mean_representative g τ, (Finset.mem_filter.mp hτ).2]
        _ = _ := by simp [Conjugacy.counts, nsmul_eq_mul]

private def representativeProduct (g : Gram) (σ : S) : Fin 7 → ℂ := ![
  1, Complex.normSq (edge g σ 0 1),
  ↑(Complex.normSq (edge g σ 3 4) * Complex.normSq (edge g σ 0 1)),
  conj (edge g σ 0 1) * viaH g σ,
  (Complex.normSq (edge g σ 3 4) : ℂ) * (conj (edge g σ 0 1) * viaH g σ),
  conj (straight g σ) * fourExit g σ, conj (straight g σ) * fiveExit g σ]

private theorem rep_product (g : Gram) (hd : ∀ i, g i i = 1)
    (hc : ∀ i j, conj (g i j) = g j i) (σ : S) (k : Fin 7) :
    term g σ (Conjugacy.rep k) = (representativeProduct g σ k).re := by
  unfold term
  apply congrArg Complex.re
  let e := edge g σ
  simp only [Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  fin_cases k
  case' «0» => change e 0 0 * (e 1 1 * (e 2 2 * (e 3 3 * (e 4 4)))) = 1
  case' «1» => change e 1 0 * (e 0 1 * (e 2 2 * (e 3 3 * (e 4 4)))) = (Complex.normSq (e 0 1) : ℂ)
  case' «2» => change e 1 0 * (e 0 1 * (e 2 2 * (e 4 3 * (e 3 4)))) = ((Complex.normSq (e 3 4) * Complex.normSq (e 0 1) : ℝ) : ℂ)
  case' «3» => change e 1 0 * (e 2 1 * (e 0 2 * (e 3 3 * (e 4 4)))) = conj (e 0 1) * (e 0 2 * e 2 1)
  case' «4» => change e 1 0 * (e 2 1 * (e 0 2 * (e 4 3 * (e 3 4)))) = (Complex.normSq (e 3 4) : ℂ) * (conj (e 0 1) * (e 0 2 * e 2 1))
  case' «5» => change e 1 0 * (e 3 1 * (e 2 2 * (e 4 3 * (e 0 4)))) = conj (e 0 1 * e 3 4) * (e 0 4 * e 3 1)
  case' «6» => change e 1 0 * (e 3 1 * (e 0 2 * (e 4 3 * (e 2 4)))) = conj (e 0 1 * e 3 4) * (e 0 2 * e 3 1 * e 2 4)
  all_goals simp only [e, edge, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self,
    map_mul, hc, hd, one_mul, mul_one] <;> ring
private theorem mean_rep (g : Gram) (hd : ∀ i, g i i = 1)
    (hc : ∀ i j, conj (g i j) = g j i) (k : Fin 7) :
    meanTerm g (Conjugacy.rep k) = ![1, P g, U g, theta g, thetaPair g, C4 g, C5 g] k := by
  unfold meanTerm
  simp_rw [rep_product g hd hc]
  fin_cases k
  · exact avg_const 1
  · rfl
  · rfl
  · rfl
  · change avg (fun σ => ((Complex.normSq (edge g σ 3 4) : ℂ) *
      (conj (edge g σ 0 1) * viaH g σ)).re) = _
    simp [thetaPair, Complex.mul_re]
  · rfl
  · rfl

/-- The normalized five-packet permanent, with one contribution for each
of the seven cycle types. -/
theorem permanent_cycles (g : Gram) (hd : ∀ i, g i i = 1)
    (hc : ∀ i j, conj (g i j) = g j i) :
    g.permanent.re = 1 + 10*P g + 15*U g + 20*theta g + 20*thetaPair g + 30*C4 g + 24*C5 g := by
  rw [permanent_classes]
  simp_rw [mean_rep g hd hc]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change ((1:ℕ):ℝ)*1 + (((10:ℕ):ℝ)*P g + (((15:ℕ):ℝ)*U g + (((20:ℕ):ℝ)*theta g +
    (((20:ℕ):ℝ)*thetaPair g + (((30:ℕ):ℝ)*C4 g + ((24:ℕ):ℝ)*C5 g))))) = _
  norm_num
  ring

/-- Specialization to the actual Gram matrix of five unit packets in any
finite complex coordinate space. -/
theorem gram_permanent_cycles {D : Type*} [Fintype D] (x : Fin 5 → D → ℂ)
    (unit : ∀ i, Closures.bracket (x i) (x i) = 1) :
    let g := Closures.crossGram x x
    g.permanent.re = 1 + 10*P g + 15*U g + 20*theta g + 20*thetaPair g +
      30*C4 g + 24*C5 g := by
  apply permanent_cycles _ unit
  intro i j
  simp [Closures.crossGram, Closures.bracket, map_sum, mul_comm]

private theorem straight_norm (g : Gram) : avg (fun σ => Complex.normSq (straight g σ)) = U g := by
  unfold U
  congr 1
  funext σ
  rw [straight, Complex.normSq_mul, mul_comm]

private theorem four_norm (g : Gram) : avg (fun σ => Complex.normSq (fourExit g σ)) = U g := by
  let f := fun σ => Complex.normSq (edge g σ 3 4) * Complex.normSq (edge g σ 0 1)
  have h (σ : S) : Complex.normSq (fourExit g σ) = f (σ * Equiv.swap 1 4) := by
    change Complex.normSq (edge g σ 0 4 * edge g σ 3 1) =
      Complex.normSq (edge g σ 3 1) * Complex.normSq (edge g σ 0 4)
    rw [Complex.normSq_mul, mul_comm]
  simp only [h]
  exact avg_relabel _ f

private theorem five_norm (g : Gram) : avg (fun σ => Complex.normSq (fiveExit g σ)) = V g := by
  let f := fun σ => Complex.normSq (edge g σ 3 4) * Complex.normSq (viaH g σ)
  have h (σ : S) : Complex.normSq (fiveExit g σ) = f (σ * Equiv.swap 1 4) := by
    change Complex.normSq (edge g σ 0 2 * edge g σ 3 1 * edge g σ 2 4) =
      Complex.normSq (edge g σ 3 1) * Complex.normSq (edge g σ 0 2 * edge g σ 2 4)
    simp only [Complex.normSq_mul]
    ring
  simp only [h]
  exact avg_relabel _ f

private theorem mixed_le (a b : ℂ) :
    2*(conj a*b).re ≤ Complex.normSq a + Complex.normSq b := by
  have h := Complex.normSq_nonneg (b-a)
  rw [Complex.normSq_sub, mul_comm b _] at h
  linarith

private theorem mixed_scaled (a b : ℂ) :
    24*(conj a*b).re ≤ 6*Complex.normSq a + 24*Complex.normSq b := by
  have h := mixed_le a (2*b)
  rw [Complex.normSq_mul] at h
  have hr : (conj a*(2*b)).re = 2*(conj a*b).re := by
    rw [show conj a*(2*b) = (2:ℂ)*(conj a*b) by ring]; simp
  rw [hr] at h
  rw [show Complex.normSq (2 : ℂ) = 4 by norm_num] at h
  linarith

/-- The long-cycle bounds come from actual squared differences of the two
exits. The second row may be scaled as 6 times |straight − 2·exit|². -/
theorem long_cycles (g : Gram) : C4 g ≤ U g ∧ 24*C5 g ≤ 6*U g + 24*V g := by
  have h4 := avg_mono (fun σ => mixed_le (straight g σ) (fourExit g σ))
  have h5 := avg_mono (fun σ => mixed_scaled (straight g σ) (fiveExit g σ))
  rw [avg_mul_left, avg_add, straight_norm, four_norm] at h4
  rw [avg_mul_left, avg_add, avg_mul_left, avg_mul_left, straight_norm, five_norm] at h5
  exact ⟨by unfold C4; linarith, h5⟩

end
end BlockPermanents.FiveCycles
