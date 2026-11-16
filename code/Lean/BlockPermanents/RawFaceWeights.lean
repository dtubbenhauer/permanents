import BlockPermanents.RawFaceMeans
import Mathlib.Data.Finset.Sort

/-! Unordered spectator Gram weights and the intrinsic four-label slack. -/
namespace BlockPermanents.RawFaceWeights
open FaceMeans Closures FourTrade RawFaceMeans
open scoped ComplexConjugate
noncomputable section

variable {m n d : ℕ}

private def sq {n : ℕ} (y : Input n d) (i j : Fin n) : ℝ :=
  Complex.normSq (bracket (y i) (y j))

private theorem sq_symm (y : Input n d) (i j : Fin n) : sq y i j = sq y j i := by
  have h : bracket (y i) (y j) = conj (bracket (y j) (y i)) := by
    simp [bracket, map_sum, mul_comm]
  simp only [sq, h, Complex.normSq_conj]

private theorem pair_perm (y : Input 2 d) (p : Equiv.Perm (Fin 2)) :
    sq (y ∘ p) 0 1 = sq y 0 1 := by
  induction p using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap p i j _ ih =>
    change sq (y ∘ p) (Equiv.swap i j 0) (Equiv.swap i j 1) = _
    apply Eq.trans _ ih
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [Equiv.swap_apply_def, sq_symm (y ∘ p) 1 0]

private theorem slack_swap (y : Input 4 d) (a b : Fin 4) :
    FaceTrade.slack (crossGram (y ∘ Equiv.swap a b) (y ∘ Equiv.swap a b)) =
      FaceTrade.slack (crossGram y y) := by
  have hp := permanent_reindex (Equiv.swap a b) (crossGram y y)
  let f := Equiv.swap a b
  change 1 + 7/3*(sq y (f 0) (f 1) + sq y (f 0) (f 2) + sq y (f 0) (f 3) +
    sq y (f 1) (f 2) + sq y (f 1) (f 3) + sq y (f 2) (f 3)) +
    3*(sq y (f 0) (f 1)*sq y (f 2) (f 3) + sq y (f 0) (f 2)*sq y (f 1) (f 3) +
      sq y (f 0) (f 3)*sq y (f 1) (f 2)) -
    ((crossGram y y).submatrix (Equiv.swap a b) (Equiv.swap a b)).permanent.re =
    1 + 7/3*(sq y 0 1 + sq y 0 2 + sq y 0 3 + sq y 1 2 + sq y 1 3 + sq y 2 3) +
      3*(sq y 0 1*sq y 2 3 + sq y 0 2*sq y 1 3 + sq y 0 3*sq y 1 2) - _
  rw [hp]
  apply congrArg (· - _)
  fin_cases a <;> fin_cases b <;>
    simp (config := {decide := true}) [f, Equiv.swap_apply_def, sq_symm y 1 0,
      sq_symm y 2 0, sq_symm y 3 0, sq_symm y 2 1, sq_symm y 3 1, sq_symm y 3 2] <;> ring

/-- Every bijective numbering of the same four packets gives the same slack. -/
theorem slack_perm (y : Input 4 d) (p : Equiv.Perm (Fin 4)) :
    FaceTrade.slack (crossGram (y ∘ p) (y ∘ p)) = FaceTrade.slack (crossGram y y) := by
  induction p using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap p a b _ ih => exact (slack_swap (y ∘ p) a b).trans ih

/-- Evaluate a symmetric packet observable on the increasing enumeration
of a finite subset. The value is zero if the cardinality is incorrect. -/
private def onSet (x : Input m d) (F : Input n d → ℝ) (s : Finset (Fin m)) : ℝ :=
  if h : s.card = n then F (x ∘ s.orderEmbOfFin h) else 0

private theorem onSet_image (x : Input m d) (F : Input n d → ℝ)
    (symm : ∀ (y : Input n d) (p : Equiv.Perm (Fin n)), F (y ∘ p) = F y)
    (e : Fin n ↪ Fin m) :
    onSet x F (Finset.univ.image e) = F (x ∘ e) := by
  let s := Finset.univ.image e
  have h : s.card = n := by simp only [s, Finset.card_image_of_injective _ e.injective,
    Finset.card_univ, Fintype.card_fin]
  let a : Fin n ≃ ↥s := Equiv.ofBijective (fun i => ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun _ _ h => e.injective (congrArg Subtype.val h), by
      rintro ⟨z,hz⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
      exact ⟨i, Subtype.ext hi⟩⟩
  let b := (s.orderIsoOfFin h).toEquiv
  have he : (x ∘ e) ∘ (b.trans a.symm) = x ∘ s.orderEmbOfFin h := by
    funext i
    exact congrArg x (congrArg Subtype.val (a.apply_symm_apply (b i)))
  change onSet x F s = _
  rw [onSet, dif_pos h, ← he, symm]

/-- Squared bracket of the two endpoints of an actual unordered edge. -/
def edgeWeight (x : Input m d) : Finset (Fin m) → ℝ :=
  onSet x (fun y : Input 2 d => sq y 0 1)

/-- Gram slack of a four-element face in increasing order. -/
def faceSlack (x : Input m d) : Finset (Fin m) → ℝ :=
  onSet x (fun y : Input 4 d => FaceTrade.slack (crossGram y y))

theorem edgeWeight_image (x : Input m d) (e : Fin 2 ↪ Fin m) :
    edgeWeight x (Finset.univ.image e) = Complex.normSq (bracket (x (e 0)) (x (e 1))) :=
  onSet_image x _ pair_perm e

theorem faceSlack_image (x : Input m d) (e : Fin 4 ↪ Fin m) :
    faceSlack x (Finset.univ.image e) = FaceTrade.slack (crossGram (x ∘ e) (x ∘ e)) :=
  onSet_image x _ slack_perm e

/-- The raw summand p_L S(J), evaluated on the face and unordered edges themselves. -/
def value (x : Input m d) (c : Config m) : ℝ :=
  (∏ E ∈ c.2, edgeWeight x E) * faceSlack x c.1

open private edge_inj from BlockPermanents.RawFaceMeans in
/-- Forgetting all internal orderings preserves the physical Gram summand. -/
theorem value_forget {r : ℕ} (x : Input m d) (v : Ordered m r) :
    value x (forget v) = weight x v * FaceTrade.slack (crossGram (active x v) (active x v)) := by
  let a : Fin 4 ↪ Fin m := Function.Embedding.inr.trans v
  let b (i : Fin r) : Fin 2 ↪ Fin m :=
    ⟨fun t => v (.inl (i,t)), fun s t h => congrArg Prod.snd (Sum.inl.inj (v.injective h))⟩
  change (∏ E ∈ Finset.univ.image (RawFaceMeans.edge v), edgeWeight x E) *
    faceSlack x (Finset.univ.image a) = _ * _
  rw [Finset.prod_image (edge_inj v).injOn, faceSlack_image]
  apply congrArg₂ (· * ·) _ rfl
  exact Finset.prod_congr rfl (fun i _ => edgeWeight_image x (b i))

/-- The raw weighted four-face sum counts each actual disjoint configuration once. -/
theorem sum_eq (x : Input m d) (r : ℕ) (fit : 4 + 2*r ≤ m) :
    (∑ c ∈ configs m r, value x c) = FaceCounts.multiplicity m r * fourSlack x r := by
  let a : Ordered m r := positions (by omega)
  rw [RawFaceMeans.sum_eq, fourSlack, mean, FaceSampling.sample_eq a, FaceSampling.sample_eq a]
  congr 1
  apply congrArg (Matchings.average m)
  funext σ
  exact value_forget x (a.trans σ.toEmbedding)

end
end BlockPermanents.RawFaceWeights
