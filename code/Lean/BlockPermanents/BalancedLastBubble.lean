import BlockPermanents.BalancedSupport
import BlockPermanents.TensorCoordinates
import BlockPermanents.SupportCup

/-! The trace loop on the symmetric survivors of a proper balanced cut. -/
namespace BlockPermanents.BalancedLast
open BalancedSupport Bend TensorCoordinates
open scoped Matrix
noncomputable section

private theorem realize {k t : ℕ} (o : Sym (Fin k) t) :
    ∃ w : Word k t, occupation w = o := by
  induction t with
  | zero => exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  | succ t ih =>
    obtain ⟨a, p, rfl⟩ := o.exists_eq_cons_of_succ
    obtain ⟨w, rfl⟩ := ih p
    refine ⟨Fin.cons a w, Subtype.ext ?_⟩
    change (∑ i, ({(Fin.cons a w : Word k (t+1)) i} : Multiset (Fin k))) = a ::ₘ (∑ i, {w i})
    simp [Fin.sum_univ_succ, Multiset.singleton_add]

private def indicator {k t : ℕ} (o : Sym (Fin k) t) (w : Word k t) : ℂ :=
  if occupation w = o then 1 else 0

/-- The distinct occupations remain independent after embedding the marked plane
in the ambient letter space. This also covers empty cables. -/
theorem expand_independent {d k : ℕ} (t : ℕ) (E : Matrix (Fin d) (Fin k) ℂ)
    (hE : Eᴴ * E = 1) : LinearIndependent ℂ (expand (t := t) E) := by
  classical
  have hI : LinearIndependent ℂ (indicator (k := k) (t := t)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c h o
    obtain ⟨w, hw⟩ := realize o
    simpa [Finset.sum_apply, indicator, hw] using congrFun h w
  let P := power (Fin t) E
  have hinv : Pᴴ * P = 1 := by
    rw [← power_star, ← power_mul, hE, power_one]
  have hinj : Function.Injective P.mulVecLin := by
    intro x y h
    have h' := congrArg Pᴴ.mulVec h
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using h'
  have he : expand (t := t) E = P.mulVecLin ∘ indicator := by
    funext o w
    simp [expand, P, power, Matrix.mulVec, dotProduct, indicator, mul_ite]
  rw [he]
  exact hI.map' _ (LinearMap.ker_eq_bot.mpr hinj)

/-- Exact dimension of the space of symmetric survivors on an orthonormal k-frame. -/
theorem dimension {d k : ℕ} (t : ℕ) (E : Matrix (Fin d) (Fin k) ℂ)
    (hE : Eᴴ * E = 1) : Module.finrank ℂ (space t E) = (k+t-1).choose t := by
  rw [space, finrank_span_eq_card (expand_independent t E hE),
    Sym.card_sym_eq_choose, Fintype.card_fin]

/-- Inserting the orthogonal trace cup and then closing it gives the dimension
of the symmetric survivor cable. -/
theorem bubble {d k : ℕ} (t : ℕ) (E : Matrix (Fin d) (Fin k) ℂ)
    (hE : Eᴴ * E = 1) :
    SupportCup.cap (space t E) * (SupportCup.cap (space t E))ᴴ =
      ((k+t-1).choose t : ℂ) • 1 := by
  rw [SupportCup.bubble, SupportCup.rank_eq, dimension t E hE]

end
end BlockPermanents.BalancedLast
