import BlockPermanents.Occupation
import BlockPermanents.Bridges
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Powerset

/-! Appendix B's multicolour occupation count for a single symmetric split.
The coordinates are the actual permutation average of ordinary tensor words. -/
namespace BlockPermanents.OccupationSplit
open scoped BigOperators
open Finset Bend
noncomputable section

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]

/-- Count slots of each colour in the chosen subset. -/
def counts (w : I → D) (s : Finset I) (j : D) : ℕ := (s.filter fun i => w i=j).card

private def slices (w : I → D) (s : Finset I) (j : D) : Finset {i // w i=j} :=
  s.subtype (fun i => w i=j)

private def unite (w : I → D) (f : (j : D) → Finset {i // w i=j}) : Finset I :=
  (univ.sigma f).map (Equiv.sigmaFiberEquiv w).toEmbedding

omit [Fintype I] [DecidableEq I] [DecidableEq D] in
private theorem mem_unite (w : I → D) (f : (j : D) → Finset {i // w i=j}) (i : I) :
    i ∈ unite w f ↔ (⟨i,rfl⟩ : {j // w j=w i}) ∈ f (w i) := by
  simp only [unite,mem_map_equiv,mem_sigma,mem_univ,true_and]
  rfl

private def fiberEquiv (w : I → D) (b : D → ℕ) :
    {s : Finset I // counts w s=b} ≃ ((j : D) → {v : Finset {i // w i=j} // v.card=b j}) where
  toFun s j := ⟨slices w s.1 j,by simpa [slices,card_subtype,counts] using congrFun s.2 j⟩
  invFun f := ⟨unite w (fun j => (f j).1),by
    funext j
    have h : slices w (unite w fun c => (f c).1) j = (f j).1 := by
      ext ⟨i,hi⟩
      subst j
      simp [slices,mem_unite]
    rw [counts,← card_subtype,← (f j).2]
    exact congrArg card h⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    change i ∈ unite w (fun j => slices w s.val j) ↔ i ∈ s.val
    simp [mem_unite,slices]
  right_inv f := by
    funext j
    apply Subtype.ext
    ext ⟨i,hi⟩
    subst j
    change (⟨i,rfl⟩ : {j // w j=w i}) ∈ slices w (unite w fun c => (f c).1) (w i) ↔ _
    simp [slices,mem_unite]

omit [DecidableEq I] in
/-- The number of possible cap subsets with prescribed colour multiplicities,
including impossible multiplicities as zero binomial coefficients. -/
theorem count_choices (w : I → D) (b : D → ℕ) :
    Fintype.card { s : Finset I // counts w s=b} =
      ∏ j, (counts w univ j).choose (b j) := by
  rw [Fintype.card_congr (fiberEquiv w b), Fintype.card_pi]
  apply prod_congr rfl
  intro j _
  rw [Fintype.card_finset_len (α:={i // w i=j})]
  simp [counts,Fintype.card_subtype]

omit [Fintype I] [DecidableEq I] in
theorem sum_counts (w : I → D) (s : Finset I) : ∑ j, counts w s j = s.card := by
  simpa [counts] using Finset.sum_card_fiberwise_eq_card_filter s univ w

private theorem restricted_count (w : I → D) (b : D → ℕ) (r : ℕ) (h : ∑ j,b j=r) :
    ((univ.powersetCard r).filter (fun s => counts w s=b)).card =
      ∏ j, (counts w univ j).choose (b j) := by
  rw [← count_choices w b]
  symm
  apply Fintype.card_of_subtype
  intro s
  simp only [mem_filter,mem_powersetCard,subset_univ,true_and,and_iff_right_iff_imp]
  intro hs
  rw [← sum_counts w s, hs, h]

omit [Fintype I] [Fintype D] [DecidableEq I] in
private theorem counts_perm (p : Equiv.Perm I) (w : I → D) (s : Finset I) :
    counts (w ∘ p) s = counts w (s.map p.toEmbedding) := by
  funext j
  simp only [counts,filter_map,card_map]
  rfl

/-- Exact fraction of all slot permutations producing the prescribed cap occupation. -/
theorem perm_probability {n d : ℕ} (w : Word d n) (s : Finset (Fin n)) (b : Fin d → ℕ)
    (hb : ∑ j,b j=s.card) :
    (∑ p : Equiv.Perm (Fin n), if counts (w ∘ p) s=b then (1:ℚ) else 0) / n.factorial =
      ((∏ j,(counts w Finset.univ j).choose (b j) : ℕ):ℚ) / n.choose s.card := by
  classical
  let f (t : Finset (Fin n)) : ℚ := if counts w t=b then 1 else 0
  have h := Occupation.symmetrizer_word f s
  rw [show (∑ t ∈ powersetCard s.card (univ : Finset (Fin n)), f t) =
    ((∏ j,(counts w univ j).choose (b j) : ℕ) : ℚ) by
      rw [← restricted_count w b s.card hb];exact Finset.sum_boole _ _] at h
  simpa only [counts_perm,Occupation.permSum,f] using h

/-- Evaluate the genuine complex word clasp against the indicator that the
chosen cap slots have occupation b. This is the multivariate hypergeometric
factor in each positive cable of the appendix's D coefficient. -/
theorem clasp_occupation {n d : ℕ} (w : Word d n) (s : Finset (Fin n)) (b : Fin d → ℕ)
    (hb : ∑ j,b j=s.card) :
    (symClasp d n).mulVec (fun u => if counts u s=b then (1:ℂ) else 0) w =
      ((∏ j, (counts w univ j).choose (b j) : ℕ) : ℂ) / (n.choose s.card : ℂ) := by
  classical
  have h := perm_probability w s b hb
  have hc := congrArg (fun x : ℚ => (x:ℂ)) h
  rw [Bridges.symClasp_action]
  simp only [Closures.clasp,Closures.sumSlots,Fintype.card_fin, counts_perm]
  have ei := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n))) (fun p : Equiv.Perm (Fin n) =>
    if counts w (s.map p.toEmbedding)=b then (1:ℂ) else 0)
  change (n.factorial : ℂ)⁻¹ *
    (∑ p : Equiv.Perm (Fin n), if counts w (s.map ((Equiv.inv _ p).toEmbedding))=b then (1:ℂ) else 0) = _
  rw [ei,mul_comm,← div_eq_mul_inv]
  simpa only [counts_perm,Rat.cast_div,Rat.cast_sum,apply_ite,Rat.cast_one,
    Rat.cast_zero,Rat.cast_natCast] using hc

end
end BlockPermanents.OccupationSplit
