import BlockPermanents.BalancedCubicExterior
import BlockPermanents.FaceTrade

/-! The parameter-dependent reflected squares in Lemma 7D.1. -/
namespace BlockPermanents.FourTradeSquares
open Closures Bend BalancedCoarse BalancedSigned CubicSquares BalancedCubicExterior
noncomputable section

/-- Signed one-cap halves, the difference of the two full-cap halves, and the
four exterior squares across one balanced division. -/
def residualEnergy {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (u : ℝ) : ℝ :=
  let U := leftSide X
  let V := rightSide X
  let α := caps U V
  energy ((survivors U V * phases).mulVec α) +
    energy ((residual (Real.sqrt u) (bracket (U 1) (U 0)) (star (bracket (V 1) (V 0)))).mulVec α) +
    Complex.normSq (α 0*α 3 - α 1*α 2) + internal X/u * crossingWedges X

theorem residualEnergy_nonneg {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) {u : ℝ} (hu : 0 < u) :
    0 ≤ residualEnergy X u := by
  have wedge (a b : D → ℂ) : 0 ≤ wedgeEnergy a b :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (by norm_num)
  have hw : 0 ≤ crossingWedges X := add_nonneg (add_nonneg (add_nonneg (wedge _ _) (wedge _ _)) (wedge _ _)) (wedge _ _)
  have hi : 0 ≤ internal X := mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact add_nonneg (add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)) (mul_nonneg (div_nonneg hi hu.le) hw)

open private sq_flip from BlockPermanents.BalancedCut in
theorem one_division {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (h : ∀ i, energy (X i) = 1)
    (u : ℝ) (hu : 0 < u) :
    (crossGram X X).permanent.re + residualEnergy X u =
      (1+BalancedCut.sq X 0 1)*(1+BalancedCut.sq X 2 3) + (2+u)*crossing X + (4/u)*internal X +
      2*(BalancedCut.sq X 0 2*BalancedCut.sq X 1 3 + BalancedCut.sq X 0 3*BalancedCut.sq X 1 2) := by
  let U := leftSide X
  let V := rightSide X
  let α := caps U V
  let M := survivors U V
  let A := bracket (U 1) (U 0)
  let B := star (bracket (V 1) (V 0))
  have hU (i) : energy (U i)=1 := by fin_cases i <;> simp [U,leftSide,h]
  have hV (i) : energy (V i)=1 := by fin_cases i <;> simp [V,rightSide,h]
  have hα (i : Fin 4) : Complex.normSq (α i) =
      ![BalancedCut.sq X 0 2,BalancedCut.sq X 0 3,BalancedCut.sq X 1 2,BalancedCut.sq X 1 3] i := by
    fin_cases i <;> exact sq_flip _ _ _
  have ha : energy α = crossing X := by simp [energy,hα,Fin.sum_univ_succ,crossing,add_assoc]
  have hin : Complex.normSq A * Complex.normSq B = internal X := by
    dsimp only [A,B]
    rw [Complex.star_def,Complex.normSq_conj]
    exact congrArg₂ (· * ·) (sq_flip X 1 0) (sq_flip X 3 2)
  have hs := signed_gluing U V hU hV (Real.sqrt u) (Real.sqrt_pos.mpr hu) α
  change (2+(Real.sqrt u)^2+(Complex.normSq A*Complex.normSq B)/(Real.sqrt u)^2)*energy α-
    energy (M.mulVec α) = energy ((M*phases).mulVec α)+energy ((residual (Real.sqrt u) A B).mulVec α) at hs
  rw [ha,hin,Real.sq_sqrt hu.le] at hs
  have hp (x y : ℂ) : Complex.normSq (x+y)+Complex.normSq (x-y) =
      2*(Complex.normSq x+Complex.normSq y) := by rw [Complex.normSq_add,Complex.normSq_sub]; ring
  have hc := hp (α 0*α 3) (α 1*α 2)
  simp only [Complex.normSq_mul,hα] at hc
  change _ = 2*(BalancedCut.sq X 0 2*BalancedCut.sq X 1 3+BalancedCut.sq X 0 3*BalancedCut.sq X 1 2) at hc
  rw [open_coarse X h]
  change (1+BalancedCut.sq X 0 1)*(1+BalancedCut.sq X 2 3) + energy (M.mulVec α) + Complex.normSq (α 0*α 3+α 1*α 2) +
    (energy ((M*phases).mulVec α)+energy ((residual (Real.sqrt u) A B).mulVec α) +
    Complex.normSq (α 0*α 3-α 1*α 2)+internal X/u*crossingWedges X) = _
  rw [← crossing_exterior X h]
  linear_combination -hs+hc

/-- The average over the three balanced divisions in (7D.2). -/
def remainder {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (u : ℝ) : ℝ :=
  (∑ j, residualEnergy (X ∘ division j) u) / 3

theorem remainder_nonneg {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) {u : ℝ} (hu : 0 < u) :
    0 ≤ remainder X u :=
  div_nonneg (Finset.sum_nonneg fun _ _ => residualEnergy_nonneg _ hu) (by norm_num)

open private sq_flip from BlockPermanents.BalancedCut in
theorem gram_identity {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (h : ∀ i, energy (X i) = 1)
    (u : ℝ) (hu : 0 < u) :
    let g := crossGram X X
    g.permanent.re + remainder X u = 1 + (5+2*u)/3*FourTrade.edges g + (5+4/u)/3*FourTrade.matchings g := by
  let g := crossGram X X
  have eqn (i : Fin 3) := one_division (X ∘ division i) (fun j => h _) u hu
  have perm (i : Fin 3) : (crossGram (X ∘ division i) (X ∘ division i)).permanent.re = g.permanent.re :=
    congrArg Complex.re (permanent_reindex (division i) g)
  simp only [perm] at eqn
  have a := eqn 0
  have b := eqn 1
  have c := eqn 2
  have re (π : Equiv.Perm (Fin 4)) (i j) : BalancedCut.sq (X ∘ π) i j = BalancedCut.sq X (π i) (π j) := rfl
  have d₀ : division 0 = 1 := rfl
  have d₁ : division 1 = Equiv.swap 1 2 := rfl
  have d₂ : division 2 = Equiv.swap 1 3 := rfl
  dsimp only
  simp only [remainder, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty] 
  change g.permanent.re + (residualEnergy (X ∘ division 0) u + (residualEnergy (X ∘ division 1) u +
      (residualEnergy (X ∘ division 2) u + 0))) / 3 =
      1 + (5+2*u)/3*(BalancedCut.sq X 0 1+BalancedCut.sq X 0 2+BalancedCut.sq X 0 3+
        BalancedCut.sq X 1 2+BalancedCut.sq X 1 3+BalancedCut.sq X 2 3) +
        (5+4/u)/3*(BalancedCut.sq X 0 1*BalancedCut.sq X 2 3 + BalancedCut.sq X 0 2*BalancedCut.sq X 1 3+
        BalancedCut.sq X 0 3*BalancedCut.sq X 1 2)
  simp (config := {decide := true}) [crossing,internal,re,d₀,d₁,d₂,Equiv.swap_apply_def] at a b c ⊢
  simp only [sq_flip X 2 1,sq_flip X 3 2,sq_flip X 3 1] at a b c
  linear_combination (a+b+c)/3

end
end BlockPermanents.FourTradeSquares
