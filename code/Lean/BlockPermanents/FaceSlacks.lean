import BlockPermanents.FacePeel

/-! # Propagation of the actual four-face slack through marked deletions -/
namespace BlockPermanents.FaceSlacks
open Closures FaceMeans FacePeel FaceExit FaceWeights CycleMatching
noncomputable section

/-- Recursive upper value on q active labels after r edges were set aside. -/
def U (Z : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,r | 1,r => Z r
  | n+2,r => U Z (n+1) r + (n+1 : ℝ)^2 * U Z n (r+1)

def S {m d : ℕ} (x : Input m d) (q r : ℕ) : ℝ :=
  U (Z (crossGram x x)) q r - H x r q

theorem mean_congr {m d q r : ℕ} (x : Input m d) (fit : 2*r+q ≤ m)
    {f g : Input q d → ℝ} (h : ∀ v : Roles r q → Fin m, f (active x v) = g (active x v)) :
    mean x r q f = mean x r q g := by
  simp only [mean, FaceSampling.sample_eq (positions fit)]
  congr 1
  funext σ
  rw [h]

theorem mean_one {m d q r : ℕ} (x : Input m d) (fit : 2*r+q ≤ m) :
    mean x r q (fun _ => 1) = Z (crossGram x x) r := by
  let p := positions fit
  let e := Function.Embedding.inl.trans p
  rw [mean,FaceSampling.sample_eq p]
  simp only [mul_one]
  simpa only [Fintype.card_fin] using mean_edges (crossGram x x) e

private theorem small_zero {m d q r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1)
    (fit : 2*r+q ≤ m) (hs : q ≤ 2) : S x q r = 0 := by
  let z := Z (crossGram x x)
  have h1 {l : ℕ} (fit' : 2*r+l ≤ m) (h : ∀ v : Roles r l → Fin m, MatchingFine.fine (active x v)=1) :
      H x r l = z r := (mean_congr x fit' (g := fun _ => 1) h).trans (mean_one x fit')
  interval_cases q
  · have h := h1 fit fun _ => by simp [MatchingFine.fine,Matrix.permanent_isEmpty]
    exact sub_eq_zero.mpr h.symm
  · have h := h1 fit fun _ => by simp [MatchingFine.fine,crossGram, Coarse.bracket_self,active,unit]
    exact sub_eq_zero.mpr h.symm
  · have h (v : Roles r 2 → Fin m) : MatchingFine.fine (active x v) =
        1 + Complex.normSq (bracket (active x v 0) (active x v 1)) := by
      let y := active x v
      have hh := MatchingCoarse.fixed_mark (n := 0) y
      have he := MatchingCoarse.exit_energy (n := 0) y 0
      have hu (i) : Bend.energy (y i) = 1 := unit _
      simp only [Finset.univ_unique, Finset.sum_singleton] at hh
      rw [Coarse.bracket_self,hu] at hh
      have hh' := congrArg Complex.re hh
      simpa [y, MatchingFine.fine,crossGram, Coarse.bracket_self,hu,he, Matrix.permanent_isEmpty,
        active,unit] using hh'
    have hp := mean_pair x (q := 0) fit 0 (fun _ => 1)
    simp only [mul_one, mean_one x (by omega : 2*(r+1)+0 ≤ m)] at hp
    have h2 := mean_congr x fit (f := MatchingFine.fine)
      (g := fun y => 1 + Complex.normSq (bracket (y 0) (y 1))) h
    rw [mean_linear x fit, mean_one x fit] at h2
    change _ = z r + mean x r 2 (fun y => Complex.normSq (bracket (y 0) (y (0 : Fin 1).succ))) at h2
    rw [hp] at h2
    simp only [S,U, Nat.cast_zero,zero_add,one_pow,one_mul]
    exact sub_eq_zero.mpr h2.symm

private theorem triple_eq {d : ℕ} : @FaceMeans.fullExit d 0 = @FaceMeans.triple d := by
  funext y
  simp [fullExit, exitEnergy_eq, triple, MatchingFine.fine, crossGram,Coarse.bracket_self]

private theorem quad_eq {d : ℕ} : @FaceMeans.fullExit d 1 = @FaceMeans.quadruple d := by
  funext y
  rw [fullExit, exitEnergy_eq, quadruple]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem slack_step {m d n r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1)
    (fit : 2*r+(n+3) ≤ m) :
    2*S x (n+3) r = 2*S x (n+2) r + (n+2 : ℝ)^2*(2*S x (n+1) (r+1)) +
      (n+2 : ℝ)*(n+1 : ℝ)*mean x r (n+3) fullExit := by
  have h := FacePeel.identity x unit fit
  unfold S
  rw [show U (Z (crossGram x x)) (n+3) r =
      U (Z (crossGram x x)) (n+2) r+(n+2 : ℝ)^2*U (Z (crossGram x x)) (n+1) (r+1) by
    rw [U]; push_cast; ring]
  linarith only [h]

private theorem three {m d r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1) (fit : 2*r+3 ≤ m) :
    S x 3 r = mean x r 3 triple := by
  have h := slack_step (n := 0) x unit fit
  rw [show S x (0+2) r = 0 from small_zero x unit (by omega) (by decide),
    show S x (0+1) (r+1) = 0 from small_zero x unit (by omega) (by decide), triple_eq] at h
  norm_num at h
  linarith only [h]

/-- On four labels the entire slack is the four-face exit plus the three-face
exit from deleting one spectator. Signs and multiplicities are retained. -/
theorem four {m d r : ℕ} (x : Input m d) (unit : ∀ i, Bend.energy (x i)=1) (fit : 2*r+4 ≤ m) :
    S x 4 r = mean x r 3 triple + 3*mean x r 4 quadruple := by
  have h := slack_step (n := 1) x unit fit
  rw [show S x (1+2) r = _ from three x unit (by omega),
    show S x (1+1) (r+1) = 0 from small_zero x unit (by omega) (by decide), quad_eq] at h
  norm_num at h
  linarith only [h]

/-- Appendix A.1. Through every deletion depth, the normalized spectator
coefficient h(q,s)/4 multiplies the matching-weighted slack of four labels. -/
theorem propagate {m d : ℕ} (x : Input m d) (schur : ∀ p q, SchurNormalization.HomogeneousSchur d p q)
    (unit : ∀ i, Bend.energy (x i)=1) {r q R : ℕ} (fit : 2*r+q ≤ m) (hR : q ≤ R) :
    FaceWeights.weighted q R r (S x 4) ≤ 4*S x q r := by
  apply FaceWeights.propagate m (S x) (S x 4) _ (fun _ _ => le_rfl) _ _ _ _ hR fit
  · intro q r hfit hq
    by_cases h : q ≤ 2
    · rw [small_zero x unit hfit h]
    · have he : q=3 := by omega
      subst q
      rw [three x unit hfit, mean, FaceSampling.sample_eq (positions hfit)]
      unfold Matchings.average
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro σ _
      apply mul_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)
      unfold triple Bend.energy
      exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

  · intro n r hfit hn
    obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n by omega)
    have h := slack_step (n := a+1) x unit hfit
    have h₃ := triple_face x schur unit hfit
    have h₄ := quadruple_face x schur unit hfit
    rw [four x unit (by omega)] 
    have hc : (((a+2+1).choose 2 : ℕ) : ℝ) = (a+3 : ℝ)*(a+2 : ℝ)/2 := by
      have k := Nat.succ_mul_choose_eq (a+2) 1
      simp only [Nat.choose_one_right] at k
      apply (eq_div_iff (by norm_num)).mpr
      exact_mod_cast k.symm
    rw [hc]
    push_cast at h ⊢
    have hz : 0 ≤ (a+3 : ℝ)*(a+2 : ℝ) := by positivity
    nlinarith only [h, mul_le_mul_of_nonneg_left h₃ hz, mul_le_mul_of_nonneg_left h₄ hz]

end
end BlockPermanents.FaceSlacks
