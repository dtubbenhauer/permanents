import BlockPermanents.FaceMeanSquares
import Mathlib.Data.Finset.Sort

/-! Unordered triples and four-sets in the exit identities (AA.2). A face
is a subset; the inner average only chooses the roles of its labels. -/
namespace BlockPermanents.RawTripleFaces
open FaceMeans FaceSampling Matchings CycleMatching
noncomputable section

abbrev Face (q t : ℕ) := ↥((Finset.univ : Finset (Fin q)).powersetCard t)

def listing {q t : ℕ} (T : Face q t) : Fin t ↪ Fin q :=
  (T.val.orderEmbOfFin (Finset.mem_powersetCard.mp T.property).2).toEmbedding

theorem face_card (q t : ℕ) : Fintype.card (Face q t) = q.choose t := by
  simp [Face, Finset.card_powersetCard]

/-- Average an observable over the possible marked and ordered roles on one
actual subset, independently of the increasing order chosen to list it. -/
def faceValue {q t d : ℕ} (x : Input q d) (F : Input t d → ℝ) (T : Face q t) : ℝ :=
  average t fun π => F (x ∘ listing T ∘ π)

private def relabel {q t : ℕ} (σ : S q) : Face q t ≃ Face q t :=
  σ.finsetCongr.subtypeEquiv (fun s => by
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Equiv.finsetCongr_apply,
      Finset.card_map])

private theorem faceValue_relabel {q t d : ℕ} (x : Input q d) (F : Input t d → ℝ)
    (σ : S q) (T : Face q t) :
    faceValue (x ∘ σ) F T = faceValue x F (relabel σ T) := by
  let R := relabel σ T
  let a := T.val.orderIsoOfFin (Finset.mem_powersetCard.mp T.property).2
  let b := R.val.orderIsoOfFin (Finset.mem_powersetCard.mp R.property).2
  let c : T.val ≃ R.val := σ.subtypeEquiv fun i => by
    change i ∈ T.val ↔ σ i ∈ T.val.map σ.toEmbedding
    simp
  let τ : S t := (a.toEquiv.trans c).trans b.toEquiv.symm
  have he (i : Fin t) : σ (listing T i) = listing R (τ i) := by
    change σ (a i).val = (b (b.symm (c (a i)))).val
    rw [b.apply_symm_apply]; rfl
  have hf (π : S t) : F ((x ∘ σ) ∘ listing T ∘ π) = F (x ∘ listing R ∘ ((τ*π) : S t)) := by
    congr 1; funext i; exact congrArg x (he (π i))
  unfold faceValue average
  simp_rw [hf]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun π : S t => F (x ∘ listing R ∘ π))

/-- Any prescribed injection of active positions gives the same unweighted face mean. -/
theorem mean_zero {q t d : ℕ} (x : Input q d) (e : Fin t ↪ Fin q) (F : Input t d → ℝ) :
    mean x 0 t F = average q (fun σ => F (x ∘ σ ∘ e)) := by
  let a : Roles 0 t ↪ Fin q :=
    (Equiv.emptySum (Fin 0 × Fin 2) (Fin t)).toEmbedding.trans e
  rw [mean, sample_eq a]
  have hw (v : Roles 0 t → Fin q) : FaceMeans.weight x v = 1 := by simp [FaceMeans.weight]
  simp only [hw, one_mul]
  rfl

private theorem average_comm {q t : ℕ} (f : S q → S t → ℝ) :
    average q (fun σ => average t (f σ)) = average t (fun π => average q (fun σ => f σ π)) := by
  unfold average
  simp only [← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  ring

/-- The unbiased sum over unordered faces. Each T occurs once in the outer
sum. Its t! internal orders are averaged in faceValue. -/
theorem subset_sum {q t d : ℕ} (x : Input q d) (F : Input t d → ℝ) :
    ∑ T : Face q t, faceValue x F T = (q.choose t : ℝ) * mean x 0 t F := by
  have hrel (σ : S q) : (∑ T : Face q t, faceValue (x ∘ σ) F T) = ∑ T : Face q t, faceValue x F T := by
    simp_rw [faceValue_relabel]
    exact (relabel σ).sum_comp (faceValue x F)
  have hT (T : Face q t) : average q (fun σ => faceValue (x ∘ σ) F T) = mean x 0 t F := by
    unfold faceValue
    rw [average_comm]
    have hπ (π : S t) :
        average q (fun σ => F ((x ∘ σ) ∘ listing T ∘ π)) = mean x 0 t F :=
      (mean_zero x (π.toEmbedding.trans (listing T)) F).symm
    simp_rw [hπ]
    exact average_const _ _
  calc
    _ = average q (fun σ => ∑ T : Face q t, faceValue (x ∘ σ) F T) := by
      simp_rw [hrel]; exact (average_const _ _).symm
    _ = ∑ T : Face q t, average q (fun σ => faceValue (x ∘ σ) F T) := average_sum Finset.univ _
    _ = _ := by simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,face_card]

/-- The full exit sum has one term per unordered pair of neighbours of the
mark, averaged over the mark. -/
def exitTotal {n d : ℕ} (x : Input (n+3) d) : ℝ :=
  ((n+2).choose 2 : ℝ) * mean x 0 (n+3) fullExit

private theorem triple_count (n : ℕ) :
    3/(n+4:ℝ) * ((n+4).choose 3 : ℝ) = ((n+3).choose 2 : ℝ) := by
  have h : (n+4:ℝ) * ((n+3).choose 2 : ℝ) = ((n+4).choose 3 : ℝ) * 3 := by
    exact_mod_cast Nat.succ_mul_choose_eq (n+3) 2
  field_simp
  linarith

private theorem quadruple_count (n : ℕ) :
    4/((n+4:ℝ)*(n+1)) * 3 * ((n+4).choose 4 : ℝ) = ((n+3).choose 2 : ℝ) := by
  have h : (n+4:ℝ) * ((n+3).choose 2 : ℝ) = ((n+4).choose 3 : ℝ) * 3 := by
    exact_mod_cast Nat.succ_mul_choose_eq (n+3) 2
  have hj : (n+4).choose 4 * 4 = (n+4).choose 3 * (n+1) := by
    simpa only [show n+4-3=n+1 by omega] using Nat.choose_succ_right_eq (n+4) 3
  have h' : ((n+4).choose 4 : ℝ)*4 = ((n+4).choose 3 : ℝ) * (n+1) := by exact_mod_cast hj
  field_simp
  linear_combination 3*h' - (n+1)*h

/-- The raw three-face identity in (AA.2), for an arbitrary label count q=n+4. -/
theorem triple_faces {n d : ℕ} (x : Input (n+4) d) (unit : ∀ i, Bend.energy (x i) = 1) :
    exitTotal (n:=n+1) x =
      3/(n+4:ℝ) * (∑ T : Face (n+4) 3, faceValue x triple T) +
      ((n+3).choose 2 : ℝ) * FaceMeanSquares.tripleRemainder x 0 (n+1) := by
  rw [exitTotal, FaceMeanSquares.triple_identity x unit (r:=0) (n:=n+1) (by omega),
    subset_sum, ← mul_assoc, triple_count, mul_add]

/-- The raw four-face identity in (AA.2). Each four-set carries three
unordered choices of exit pair for its marked label. -/
theorem quadruple_faces {n d : ℕ} (x : Input (n+4) d) (unit : ∀ i, Bend.energy (x i) = 1) :
    exitTotal (n:=n+1) x =
      4/((n+4:ℝ)*(n+1)) * (∑ T : Face (n+4) 4, 3 * faceValue x quadruple T) +
      ((n+3).choose 2 : ℝ) * FaceMeanSquares.quadRemainder x 0 n := by
  rw [exitTotal, FaceMeanSquares.quad_identity x unit (r:=0) (n:=n) (by omega),
    ← Finset.mul_sum, subset_sum, ← mul_assoc, ← mul_assoc, quadruple_count, mul_add]

theorem three_face_bound {n d : ℕ} (x : Input (n+4) d) (unit : ∀ i, Bend.energy (x i) = 1) :
    3/(n+4:ℝ) * (∑ T : Face (n+4) 3, faceValue x triple T) ≤ exitTotal (n:=n+1) x := by
  rw [triple_faces x unit]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (FaceMeanSquares.tripleRemainder_nonneg x (by omega)))

theorem four_face_bound {n d : ℕ} (x : Input (n+4) d) (unit : ∀ i, Bend.energy (x i) = 1) :
    4/((n+4:ℝ)*(n+1)) * (∑ T : Face (n+4) 4, 3 * faceValue x quadruple T) ≤
      exitTotal (n:=n+1) x := by
  rw [quadruple_faces x unit]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (FaceMeanSquares.quadRemainder_nonneg x (by omega)))

private def partnerTotal {n d : ℕ} (x : Input (n+2) d) : ℝ :=
  ∑ i, ∑ j, FaceRelabel.pairExit i j x

private theorem partnerTotal_perm {n d : ℕ} (x : Input (n+2) d) (p : S (n+1)) :
    partnerTotal (x ∘ FaceRelabel.fixMark p) = partnerTotal x := by
  have h (i j : Fin (n+1)) : FaceRelabel.pairExit i j (x ∘ FaceRelabel.fixMark p) =
      FaceRelabel.pairExit (p i) (p j) x := by simp only [FaceRelabel.pairExit, FaceRelabel.exit_perm]
  have row (i : Fin (n+1)) := Equiv.sum_comp p (fun j => FaceRelabel.pairExit i j x)
  simp only [partnerTotal, h, row]
  exact Equiv.sum_comp p (fun i => ∑ j, FaceRelabel.pairExit i j x)

private theorem mean_partner {n d : ℕ} (x : Input (n+3) d) :
    (n+3:ℝ)*mean x 0 (n+3) partnerTotal = ∑ t, partnerTotal (MatchingCoarse.mark x t) := by
  have h (t : Fin (n+3)) (p : S (n+2)) :
      x ∘ Equiv.Perm.decomposeFin.symm (t,p) =
          MatchingCoarse.mark x t ∘ FaceRelabel.fixMark p := by
    funext i
    exact Fin.cases (by simp [MatchingCoarse.mark]) (fun j => by
      simp [MatchingCoarse.mark,Equiv.Perm.decomposeFin_symm_apply_succ]) i
  rw [mean_zero x (Function.Embedding.refl _) partnerTotal, average,
    Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [show ⇑(Function.Embedding.refl (Fin (n+3))) = id from rfl, Function.comp_id, Finset.sum_map, Equiv.toEmbedding_apply,
    Finset.sum_product, h, partnerTotal_perm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Nat.factorial_succ (n+2)]
  push_cast
  field_simp [Nat.factorial_ne_zero]
  ring

/-- The same E(I), now written directly in the label coordinates of the
marked-packet deletion formula, without a permutation mean. -/
theorem exitTotal_marked {n d : ℕ} (x : Input (n+3) d) :
    exitTotal x = (∑ t, ∑ i, ∑ j, FaceRelabel.pairExit i j (MatchingCoarse.mark x t)) /
      (2*(n+3:ℝ)) := by
  have hs := FacePeel.sum_exit x (r:=0) (n:=n) (by omega)
  have hm := mean_partner x
  have hsum : mean x 0 (n+3) partnerTotal = ∑ i, ∑ j, mean x 0 (n+3) (FaceRelabel.pairExit i j) := by
    change mean x 0 (n+3) (fun y => ∑ i, ∑ j, FaceRelabel.pairExit i j y) = _
    rw [FacePeel.mean_sum x (by omega) (fun i y => ∑ j, FaceRelabel.pairExit i j y)]
    simp_rw [FacePeel.mean_sum x (r:=0) (q:=n+3) (by omega)]
  rw [hs] at hsum
  rw [hsum] at hm
  unfold partnerTotal at hm
  have hc : 2*((n+2).choose 2 : ℝ) = (n+2:ℝ)*(n+1) := by
    have h := Nat.succ_mul_choose_eq (n+1) 1
    simp only [Nat.choose_one_right] at h
    exact_mod_cast (h.trans (Nat.mul_comm _ _)).symm
  unfold exitTotal
  apply (eq_div_iff (by positivity)).2
  rw [← hm, ← hc]
  ring

end
end BlockPermanents.RawTripleFaces
