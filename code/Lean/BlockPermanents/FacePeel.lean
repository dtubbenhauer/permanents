import BlockPermanents.FaceRelabel
import BlockPermanents.FaceWeights

/-! # The averaged deletion identity with a spectator matching -/
namespace BlockPermanents.FacePeel
open Closures FaceMeans FaceSampling FaceRelabel MatchingCoarse Matchings
noncomputable section

private def splitRoles (r q : ℕ) : Roles (r+1) q ≃ (Fin r × Fin 2) ⊕ (Fin 2 ⊕ Fin q) where
  toFun
    | .inl (k,j) => Fin.cases (.inr (.inl j)) (fun t => .inl (t,j)) k
    | .inr j => .inr (.inr j)
  invFun
    | .inl (k,j) => .inl (k.succ,j)
    | .inr (.inl j) => .inl (0,j)
    | .inr (.inr j) => .inr j
  left_inv := by
    rintro (⟨k,j⟩ | j)
    · exact Fin.cases rfl (fun _ => rfl) k
    · rfl
  right_inv := by rintro (⟨k,j⟩ | (j|j)) <;> rfl

private def pairSlots {q : ℕ} (i : Fin (q+1)) : Fin 2 ⊕ Fin q ≃ Fin (q+2) :=
  (finSumFinEquiv.trans (finCongr (Nat.add_comm 2 q))).trans (fixMark (Equiv.swap 0 i))

private theorem slots0 {q : ℕ} (i : Fin (q+1)) : pairSlots i (.inl 0) = 0 := fixMark_zero (Equiv.swap 0 i)
private theorem slots1 {q : ℕ} (i : Fin (q+1)) : pairSlots i (.inl 1) = i.succ := by
  change fixMark (Equiv.swap 0 i) (0 : Fin (q+1)).succ = _
  rw [fixMark_succ, Equiv.swap_apply_left]
private theorem slotsTail {q : ℕ} (i : Fin (q+1)) (a : Fin q) :
    pairSlots i (.inr a) = (omitSlot i a).succ := by
  have e : finCongr (Nat.add_comm 2 q) (finSumFinEquiv (.inr a)) = a.succ.succ := by
    apply Fin.ext; simp [finCongr]
  simp only [pairSlots, Equiv.trans_apply, e, fixMark_succ]
  rfl

/-- A deleted pair joins the spectator matching. -/
theorem mean_pair {m d q r : ℕ} (x : Input m d) (fit : 2*r+(q+2) ≤ m)
    (i : Fin (q+1)) (F : Input q d → ℝ) :
    mean x r (q+2) (fun y => Complex.normSq (bracket (y 0) (y i.succ))*F (remainder y i)) =
      mean x (r+1) q F := by
  let e := (splitRoles r q).trans ((Equiv.refl _).sumCongr (pairSlots i))
  rw [mean, mean, ← restrict e.toEmbedding (positions fit)
    (fun v : Roles (r+1) q → Fin m => weight x v * F (active x v))]
  congr 1
  funext v
  have he : active x (v ∘ e) = remainder (active x v) i := by
    funext a
    change x (v (.inr (pairSlots i (.inr a)))) = _
    rw [slotsTail]
    rfl
  change _ = weight x (v ∘ e) * F (active x (v ∘ e))
  rw [he]
  have hw : weight x (v ∘ e) =
      Complex.normSq (bracket (active x v 0) (active x v i.succ))*weight x v := by
    unfold FaceMeans.weight
    rw [Fin.prod_univ_succ]
    change Complex.normSq (bracket (x (v (.inr (pairSlots i (.inl 0)))))
        (x (v (.inr (pairSlots i (.inl 1)))))) * _ = _
    rw [slots0,slots1]
    rfl
  rw [hw]
  ring

theorem mean_linear {m d r q : ℕ} (x : Input m d) (fit : 2*r+q ≤ m)
    (f g : Input q d → ℝ) : mean x r q (fun y => f y+g y) = mean x r q f+mean x r q g := by
  simp only [mean, sample_eq (positions fit), mul_add, average_add]

theorem mean_smul {m d r q : ℕ} (x : Input m d) (fit : 2*r+q ≤ m)
    (a : ℝ) (f : Input q d → ℝ) : mean x r q (fun y => a*f y) = a*mean x r q f := by
  simp only [mean, sample_eq (positions fit), mul_left_comm _ a, average_smul]

theorem mean_sum {m d r q : ℕ} {T : Type*} [Fintype T] (x : Input m d) (fit : 2*r+q ≤ m)
    (f : T → Input q d → ℝ) : mean x r q (fun y => ∑ i, f i y) = ∑ i, mean x r q (f i) := by
  simp only [mean, sample_eq (positions fit), Finset.mul_sum, average_sum]

def H {m d : ℕ} (x : Input m d) (r q : ℕ) := mean x r q MatchingFine.fine

/-- The fixed-mark variance term after averaging distinct ordered partners. -/
theorem sum_exit {m d n r : ℕ} (x : Input m d) (fit : 2*r+(n+3) ≤ m) :
    (∑ i : Fin (n+2), ∑ j : Fin (n+2), mean x r (n+3) (pairExit i j)) =
      (n+2 : ℝ)*(n+1 : ℝ)*mean x r (n+3) fullExit := by
  have h (i j : Fin (n+2)) : mean x r (n+3) (pairExit i j) =
      if j=i then 0 else mean x r (n+3) fullExit := by
    split
    · subst j
      simp [mean,sample_eq (positions fit), pairExit,Bend.energy,average]
    · rename_i hn
      exact mean_exit x fit i j (Ne.symm hn)
  simp_rw [h]
  have row (i : Fin (n+2)) :
      (∑ j : Fin (n+2), if j=i then (0:ℝ) else mean x r (n+3) fullExit) =
        (n+1 : ℝ)*mean x r (n+3) fullExit := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [if_pos rfl, add_zero]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    simp
  simp_rw [row]
  simp [mul_assoc]

/-- Actual coarse recurrence at every deletion depth, including both
single and pair deletions and the full squared-exit remainder. -/
theorem identity {m d n r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1)
    (fit : 2*r+(n+3) ≤ m) :
    2*H x r (n+3) + (n+2 : ℝ)*(n+1 : ℝ)*mean x r (n+3) fullExit =
      2*(H x r (n+2) + (n+2 : ℝ)^2*H x (r+1) (n+1)) := by
  let lhs (y : Input (n+3) d) := 2*MatchingFine.fine y+
    ∑ i : Fin (n+2), ∑ j : Fin (n+2), pairExit i j y
  let rhs (y : Input (n+3) d) := 2*(MatchingFine.fine (y ∘ Fin.succ)+
    (n+2 : ℝ)*∑ i : Fin (n+2), Complex.normSq (bracket (y 0) (y i.succ))*MatchingFine.fine (remainder y i))
  have idv (v : Roles r (n+3) → Fin m) : lhs (active x v) = rhs (active x v) := by
    let y := active x v
    have h := peel_identity y
    have h0 : (bracket (y 0) (y 0)).re = 1 := by rw [Coarse.bracket_self,Complex.ofReal_re]; exact unit _
    simpa only [lhs,rhs,MatchingFine.fine,pairExit, h0,one_mul, Nat.cast_add, Nat.cast_one,
      show (n:ℝ)+1+1=n+2 by ring] using h
  have h : mean x r (n+3) lhs = mean x r (n+3) rhs := by
    simp only [mean, sample_eq (positions fit)]
    congr 1
    funext σ
    rw [idv]
  simp only [lhs,rhs,mean_linear x fit,mean_smul x fit,mean_sum x fit, sum_exit x fit] at h
  have hs := mean_restrict x fit (Fin.succEmb (n+2)) MatchingFine.fine
  rw [show mean x r (n+3) (fun y => MatchingFine.fine (y ∘ Fin.succ)) = H x r (n+2) from hs] at h
  simp only [mean_pair x fit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add,
    Nat.cast_ofNat, nsmul_eq_mul,← mul_assoc,← sq] at h
  exact h

end
end BlockPermanents.FacePeel
