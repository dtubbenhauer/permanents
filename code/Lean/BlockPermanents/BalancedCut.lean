import BlockPermanents.BalancedCoarse
import BlockPermanents.FourTrade

/-! # The three balanced pair divisions on inserted packet products -/
namespace BlockPermanents.BalancedCut
open Closures Bend BalancedSigned BalancedCoarse FourTrade
open scoped ComplexConjugate
noncomputable section

def sq {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (i j : Fin 4) : ℝ :=
  Complex.normSq (bracket (X i) (X j))

private theorem sq_flip {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (i j : Fin 4) :
    sq X i j = sq X j i := by
  have h : conj (bracket (X i) (X j)) = bracket (X j) (X i) := by simp [bracket,map_sum,mul_comm]
  rw [sq,sq,← h,Complex.normSq_conj]

private theorem double_cap_bound (x y : ℂ) :
    Complex.normSq (x+y) ≤ 2*(Complex.normSq x+Complex.normSq y) := by
  have h := Complex.normSq_nonneg (x-y)
  simp only [Complex.normSq_add, Complex.normSq_sub] at *
  linarith

private theorem residual_nonneg {T : Type*} [Fintype T] (f : T → ℂ) : 0 ≤ energy f :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Signed one-cap gluing at t=1 and the two full caps bound the coarse
permanent by its contributions across a specified balanced cut. -/
theorem one_cut_upper {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ)
    (h : ∀ i, energy (X i) = 1) :
    (crossGram X X).permanent.re ≤
      (1+sq X 0 1)*(1+sq X 2 3) +
      3*(sq X 0 2 + sq X 0 3 + sq X 1 2 + sq X 1 3) + 4*(sq X 0 1*sq X 2 3) +
      2*(sq X 0 2*sq X 1 3 + sq X 0 3*sq X 1 2) := by
  let U := leftSide X
  let V := rightSide X
  let M := survivors U V
  let α := caps U V
  let Dp := sq X 0 2 + sq X 0 3 + sq X 1 2 + sq X 1 3
  let sp := sq X 0 1*sq X 2 3
  have hU (i) : energy (U i)=1 := by fin_cases i <;> simp [U,leftSide,h]
  have hV (i) : energy (V i)=1 := by fin_cases i <;> simp [V,rightSide,h]
  have hα (i : Fin 4) : Complex.normSq (α i) = ![sq X 0 2,sq X 0 3,sq X 1 2,sq X 1 3] i := by
    fin_cases i <;> exact sq_flip _ _ _
  have ha : energy α = Dp := by simp [energy,hα,Fin.sum_univ_succ,Dp,add_assoc]
  have hs := signed_gluing U V hU hV 1 (by norm_num) α
  dsimp only at hs
  have hsg : 0 ≤ (2 + (1:ℝ)^2 + Complex.normSq (bracket (U 1) (U 0)) *
      Complex.normSq (star (bracket (V 1) (V 0)))/1^2) * energy α - energy (M.mulVec α) :=
    hs ▸ add_nonneg (residual_nonneg _) (residual_nonneg _)
  have hin : Complex.normSq (bracket (U 1) (U 0)) * Complex.normSq (star (bracket (V 1) (V 0))) = sp := by
    rw [Complex.star_def,Complex.normSq_conj]
    exact congrArg₂ (· * ·) (sq_flip X 1 0) (sq_flip X 3 2)
  rw [hin,ha] at hsg
  norm_num at hsg
  have w (i j) : sq X i j ≤ 1 := by
    simpa [sq,h] using FiveProjection.bracket_bound (X i) (X j)
  have hD : Dp ≤ 4 := by dsimp [Dp]; linarith only [w 0 2,w 0 3,w 1 2,w 1 3]
  have hsp : 0 ≤ sp := mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hc := double_cap_bound (α 0*α 3) (α 1*α 2)
  simp only [Complex.normSq_mul,hα] at hc
  change Complex.normSq (α 0*α 3+α 1*α 2) ≤ 2*(sq X 0 2*sq X 1 3 + sq X 0 3*sq X 1 2) at hc
  have hopen := open_coarse X h
  change (crossGram X X).permanent.re = (1+sq X 0 1)*(1+sq X 2 3) + energy (M.mulVec α) +
      Complex.normSq (α 0*α 3+α 1*α 2) at hopen
  rw [hopen]
  change _ ≤ _ + 3*Dp + 4*sp + _
  nlinarith only [hsg,hc,mul_le_mul_of_nonneg_left hD hsp]

/-- Adding the signed gluings for all three balanced divisions. -/
theorem three_cut_upper {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ)
    (h : ∀ i, energy (X i) = 1) :
    3 * (crossGram X X).permanent.re ≤ 3 + 7 * edges (crossGram X X) +
      9 * matchings (crossGram X X) := by
  let g := crossGram X X
  have again (π : Equiv.Perm (Fin 4)) :
      (crossGram (X ∘ π) (X ∘ π)).permanent.re = g.permanent.re :=
    congrArg Complex.re (permanent_reindex π g)
  have h₁ := one_cut_upper X h
  have h₂ := one_cut_upper (X ∘ Equiv.swap 1 2) (fun i => h _)
  have h₃ := one_cut_upper (X ∘ Equiv.swap 1 3) (fun i => h _)
  rw [again] at h₂ h₃
  have re (π : Equiv.Perm (Fin 4)) (i j) : sq (X ∘ π) i j = sq X (π i) (π j) := rfl
  simp (config := {decide := true}) [re,Equiv.swap_apply_def] at h₂ h₃
  simp only [sq_flip X 2 1, sq_flip X 3 1, sq_flip X 3 2] at h₂ h₃
  change 3*g.permanent.re ≤ _
  change _ ≤ 3+7*(sq X 0 1+sq X 0 2+sq X 0 3+sq X 1 2+sq X 1 3+sq X 2 3)+
    9*(sq X 0 1*sq X 2 3+sq X 0 2*sq X 1 3+sq X 0 3*sq X 1 2)
  change g.permanent.re ≤ _ at h₁
  linarith only [h₁,h₂,h₃]

end
end BlockPermanents.BalancedCut
