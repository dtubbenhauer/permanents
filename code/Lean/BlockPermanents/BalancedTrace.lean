import BlockPermanents.BalancedSupport
import BlockPermanents.PairBound

/-! # Completing a balanced cut on a general, possibly entangled pair -/
namespace BlockPermanents.BalancedTrace
open Bend BalancedSupport
noncomputable section

/-- Append a shared cut word to the survivor coordinates. -/
def join {d k r : ℕ} (h : r ≤ k) (w : Word d (k-r)) (t : Word d r) : Word d k :=
  fun i => Fin.append w t (Fin.cast (Nat.sub_add_cancel h).symm i)

def cutMatrix {d k r : ℕ} (h : r ≤ k) (A : Matrix (Word d k) (Word d k) ℂ) :
    Matrix (Word d (k-r)) (Word d (k-r)) ℂ :=
  fun w v => ∑ t : Word d r, A (join h w t) (join h v t)

private theorem joins {d k r : ℕ} (h : r ≤ k) :
    ∃ e : (Word d (k-r) × Word d r) ≃ Word d k, ∀ w t, e (w,t) = join h w t := by
  let e : (Word d (k-r) × Word d r) ≃ Word d k := (Fin.appendEquiv _ _).trans
    (Equiv.arrowCongr (finCongr (Nat.sub_add_cancel h)) (Equiv.refl _))
  exact ⟨e,fun _ _ => rfl⟩

theorem partial_trace {d k r : ℕ} (h : r ≤ k) (A : Matrix (Word d k) (Word d k) ℂ) :
    (cutMatrix h A).trace = A.trace := by
  obtain ⟨e,he⟩ := joins (d := d) h
  unfold Matrix.trace Matrix.diag
  rw [← e.sum_comp (fun i => A i i),Fintype.sum_prod_type]
  simp [cutMatrix,he,Matrix.diag]

private theorem cast_slice {d k s a b : ℕ} (h : a+b = k) (U : Fin d → Fin s → ℂ)
    {f : Word d k → ℂ} (hf : f ∈ space k U) (v : Word d b) :
    (fun w => f (fun i => Fin.append w v (Fin.cast h.symm i))) ∈ space a U := by
  subst k
  exact slice_mem U hf v

/-- Projecting either side of an entangled pair is the ordinary word cut
when the two word arguments are already symmetric. -/
theorem partial_action {d k} (r : CutIndex k k) (A : Matrix (Word d k) (Word d k) ℂ)
    (hrow : ∀ i, Symmetric (A i)) (hcol : ∀ j, Symmetric (fun i => A i j))
    (w v : Word d (k-r)) :
    (wordCap d k k r).mulVec (fun p => A p.1 p.2) (w,v) =
      cutMatrix (PairBound.cut_le r) A w v := by
  let h := PairBound.cut_le r
  have hr (i j) : ∑ b, star (symClasp d k j b) * A i b = A i j := by
    have he (x y : Word d k) : star (symClasp d k x y) = symClasp d k x y := by
      simp [symClasp,star_sum,apply_ite]
    simp_rw [he]
    exact congrFun (hrow i) j
  have hc (i j) : ∑ a, symClasp d k i a * A a j = A i j := congrFun (hcol j) i
  simp only [wordCap,cap,Matrix.mulVec,dotProduct,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_prod_type]
  change (∑ x, ∑ y, symClasp d k (join h w t) x * star (symClasp d k (join h v t) y) * A x y) = _
  simp_rw [mul_assoc,← Finset.mul_sum,hr,hc]

/-- If every turned slice lies in Symᵏ of the same supported plane,
the terminal contraction is bounded by its dimension after any cutMatrix cut. -/
theorem terminal_le {d k r : ℕ} (h : r ≤ k) (U : Fin d → Fin k → ℂ)
    (A : Matrix (Word d k) (Word d k) ℂ) (supported : ∀ w, A w ∈ space k U) :
    Complex.normSq A.trace ≤ ((k+(k-r)-1).choose (k-r) : ℝ) *
      ∑ w, ∑ v, Complex.normSq (cutMatrix h A w v) := by
  have hm (w) : (fun v => cutMatrix h A w v) ∈ space (k-r) U := by
    change (fun v => ∑ t, A (join h w t) (join h v t)) ∈ _
    rw [show (fun v => ∑ t, A (join h w t) (join h v t)) =
      ∑ t, (fun v => A (join h w t) (join h v t)) by ext v; simp]
    exact Submodule.sum_mem _ (fun t _ =>
      cast_slice (Nat.sub_add_cancel h) U (supported (join h w t)) t)
  let M := (cutMatrix h A).transpose
  have he := TraceBound.trace_normSq_le (space (k-r) U) M hm
  rw [show M.trace = A.trace by simp only [M,Matrix.trace_transpose,partial_trace]] at he
  rw [Finset.sum_comm] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast dimension (k-r) U)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end
end BlockPermanents.BalancedTrace
