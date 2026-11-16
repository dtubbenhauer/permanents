import BlockPermanents.FourRoutePositive
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The quadratic cut form on arbitrary supported tensors

The proper and full cap matrices are applied to a single vector on the
entire marked boundary. The subspace is the span of products of an ordinary
symmetric-packet triple and a marked symmetric two-strand tensor on the plane.
-/
namespace BlockPermanents.FourSupportedTensor
open Bend Closures FourLastCaps FourRoutes FourCapOrbit FourCapValues FourFullValues FourQuadratic
open scoped BigOperators Matrix
noncomputable section

abbrev Boundary (d : ℕ) := (Triple d 2 × Word d 2) → ℂ

def proper {d : ℕ} (r : Fin 3) (z : Boundary d) : Raw (Fin d) := fun u b =>
  (capHalf d 2 (r.val+1) (by have := r.isLt;omega) ⟨1,by have := r.isLt;omega⟩ (fun i j => u (spectatorPort r (i,j)))).mulVec
    z (fun i => u (activePort r i),fun _ => b)

def complete {d : ℕ} (r : Fin 3) (z : Boundary d) (w : Word d 4) : ℂ :=
  (capHalf d 2 (r.val+1) (by have := r.isLt;omega) ⟨2,by have := r.isLt;omega⟩
    (fun i j => retained w (spectatorPort r (i,j)))).mulVec z (fun i => retained w (through r i),Fin.elim0)

def form {d : ℕ} (z : Boundary d) : ℝ :=
  24*rawEnergy Finset.univ (proper 0 z) + 144*rawEnergy Finset.univ (proper 1 z) + 1080*rawEnergy Finset.univ (proper 2 z) +
    1350*energy (fun w => complete 2 z w - clasp (complete 0 z) w/15) +
      108*energy (complete 1 z) - 12*energy (complete 0 z) - 24*energy (clasp (complete 0 z))

def simple {d : ℕ} (S : Finset (Fin d)) := {z : Boundary d |
  ∃ (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ), Inner F ∧ Bend.Symmetric H ∧ Supported S H ∧
    product F (fun v => star (H v)) = z}

private lemma eval_sum {I A B : Type*} [Fintype I] [Fintype A] (M : Matrix B A ℂ)
    (z : I → A → ℂ) (b : B) : M.mulVec (∑ i, z i) b = ∑ i, M.mulVec (z i) b := by
  simp only [Matrix.mulVec,dotProduct,Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_comm

private lemma clasp_sum {d : ℕ} {I : Type*} [Fintype I] (v : I → Word d 4 → ℂ) (w : Word d 4) :
    clasp (fun t => ∑ i, v i t) w = ∑ i, clasp (v i) w := by
  unfold clasp sumSlots
  rw [Finset.sum_comm,Finset.mul_sum]

private theorem sum_bound {d : ℕ} (S : Finset (Fin d)) (hc : S.card = 2)
    {I : Type*} [Fintype I] (F : I → Triple d 2 → ℂ) (H : I → Word d 2 → ℂ)
    (hF : ∀ i, Inner (F i)) (hH : ∀ i, Bend.Symmetric (H i)) (hS : ∀ i, Supported S (H i)) :
    0 ≤ form (∑ i, product (F i) (fun t => star (H i t))) := by
  classical
  let z := ∑ i, product (F i) (fun t => star (H i t))
  let a i := value S (F i) (H i) sameChart
  let b i := value S (F i) (H i) mixedChart
  let x (w : Word d 4) := ∑ i, a i w
  let y (w : Word d 4) := ∑ i, b i w
  have pr (r : Fin 3) : proper r z = fun w c => ∑ i, raw r (F i) (H i) w c := by
    funext w c; apply eval_sum
  have fr (r : Fin 3) : complete r z = fun w => ∑ i, full r (F i) (H i) w := by
    funext w; apply eval_sum
  have vals i t := five_values S (hF i) (H i) (hH i) t
  have finals i t := full_values S (hF i) (H i) (hH i) (hS i) t
  have hp (r : Fin 3) (P : Finset Slots) (w : Word d 4) :
      portCap S P (proper r z) w = ∑ i, portCap S P (raw r (F i) (H i)) w := by
    rw [pr,cap_sum]
  have hpair (n : ℂ) (q : ℂ) (w) :
      (∑ i, (a i w+n*b i w)/q) = (x w+n*y w)/q := by
    simp only [x,y,div_eq_mul_inv,← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  have ha : activeSet 0 = {anchor} := by decide
  have h₀ t : portCap S ({anchor} : Finset Slots)ᶜ (proper 0 z) t = y t := by
    rw [←ha,hp]; exact Finset.sum_congr rfl (fun i _ => (vals i t).1)
  have h₁ t : portCap S {anchor} (proper 0 z) t = x t := by
    rw [←ha,hp]; exact Finset.sum_congr rfl (fun i _ => (vals i t).2.1)
  have hw (i : Fin 2) (w) : portCap S (PW i) (proper 1 z) w =
      ![y w, fullCapMean 2 (x w) (y w)] i := by
    rw [hp]; fin_cases i
    · exact Finset.sum_congr rfl (fun i _ => (vals i w).2.2.1)
    · exact (Finset.sum_congr rfl (fun i _ => (vals i w).2.2.2.1)).trans
        ((hpair 2 3 w).trans (fullCapMeans _ _).1.symm)
  have hv (i : Fin 1) (w) : portCap S (PV i) (proper 2 z) w = fullCapMean 3 (x w) (y w) := by
    rw [hp]
    exact (Finset.sum_congr rfl (fun k _ => (vals k w).2.2.2.2)).trans
      ((hpair 4 5 w).trans (fullCapMeans _ _).2.symm)
  have hx : clasp (complete 0 z) = x := by
    rw [fr]; funext w; rw [clasp_sum]
    exact Finset.sum_congr rfl (fun i _ => (finals i w).1)
  have fw w : clasp (complete 1 z) w = fullCapMean 2 (x w) (y w) := by
    rw [fr,clasp_sum]; exact (Finset.sum_congr rfl (fun i _ => (finals i w).2.1)).trans
      ((hpair 2 3 w).trans (fullCapMeans _ _).1.symm)
  have fv : complete 2 z = fun w => fullCapMean 3 (x w) (y w) := by
    rw [fr]; funext w
    exact (Finset.sum_congr rfl (fun i _ =>
      (congrFun (last_symmetric (F i) (H i) (hH i)).symm w).trans (finals i w).2.2)).trans
      ((hpair 4 5 w).trans (fullCapMeans _ _).2.symm)
  have fu : lastTrace S anchor (proper 0 z) = complete 0 z := by
    rw [pr,fr]; funext w; unfold lastTrace; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← join_cut 0 (F i) (H i) (hH i)]
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => outside_zero 0 S (F i) (H i) (hH i) (hS i) _ hc
  have hb := full_word_bound S hc anchor PW PV (by decide) (by decide) (by decide)
    (proper 0 z) (proper 1 z) (proper 2 z) x y (complete 1 z) h₀ h₁ hw hv fw
  have dom (r : Fin 3) : rawEnergy S (proper r z) ≤ rawEnergy Finset.univ (proper r z) :=
    Finset.sum_le_sum (fun w _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) fun _ _ _ => Complex.normSq_nonneg _)
  change 0 ≤ form z
  unfold form; rw [hx,fv,fu] at *
  linarith only [hb,dom 0,dom 1,dom 2]

/-- Positivity on the whole (algebraic, finite-dimensional) tensor product
of the upright packet spaces with the supported marked packet space. -/
theorem nonnegative {d : ℕ} (S : Finset (Fin d)) (hc : S.card = 2)
    {z : Boundary d} (hz : z ∈ Submodule.span ℂ (simple S)) : 0 ≤ form z := by
  classical
  obtain ⟨f,t,ht,_,hz'⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hz
  choose F H hF hH hS eq using (fun i : t => ht i.property)
  let L (i : t) := fun w => f i * F i w
  have hL (i : t) : Inner (L i) := by
    intro p w; exact congrArg (fun a => f i*a) (hF i p w)
  have prodEq (i : t) : product (L i) (fun u => star (H i u)) = f i • i.val := by
    calc
      _ = f i • product (F i) (fun u => star (H i u)) := by
        funext w; change (f i * _) * _ = f i * (_ * _); ring
      _ = _ := congrArg (fun a => f i • a) (eq i)
  have hs : (∑ i : t, product (L i) (fun u => star (H i u))) = z := by
    rw [← hz']; simp_rw [prodEq]; rw [Finset.univ_eq_attach]; exact Finset.sum_attach t (fun a => f a • a)
  rw [← hs]
  exact sum_bound S hc L H hL hH hS

end
end BlockPermanents.FourSupportedTensor
