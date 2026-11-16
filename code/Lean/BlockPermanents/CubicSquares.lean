import BlockPermanents.BalancedEndpoint

/-! # The cubic balance with the manuscript's 37/4 remainder -/
namespace BlockPermanents.CubicSquares
open Closures Bend BalancedCoarse BalancedCut BalancedSigned MatchingFine SchurNormalization
open scoped BigOperators
noncomputable section

def division : Fin 3 → Equiv.Perm (Fin 4) := ![1,Equiv.swap 1 2,Equiv.swap 1 3]

def internal {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) :=
  BalancedCut.sq X 0 1 * BalancedCut.sq X 2 3

def crossing {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) :=
  BalancedCut.sq X 0 2 + BalancedCut.sq X 0 3 + BalancedCut.sq X 1 2 + BalancedCut.sq X 1 3

/-- The four nonnegative terms in the last line of the cubic certificate,
for one division. -/
def signedSquares {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) : ℝ :=
  let U := leftSide X
  let V := rightSide X
  let α := caps U V
  energy ((survivors U V * phases).mulVec α) +
    energy ((residual (1/2) (bracket (U 1) (U 0)) (star (bracket (V 1) (V 0)))).mulVec α) +
    Complex.normSq (α 0*α 3 - α 1*α 2) + 4*internal X*(4-crossing X)

private theorem flip {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (i j : Fin 4) :
    BalancedCut.sq X i j = BalancedCut.sq X j i := by
  have h : star (bracket (X i) (X j)) = bracket (X j) (X i) := by simp [bracket,Complex.star_def,map_sum,mul_comm]
  rw [BalancedCut.sq,BalancedCut.sq,← h,Complex.star_def,Complex.normSq_conj]

theorem signedSquares_nonneg {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (h : ∀ i, energy (X i) = 1) :
    0 ≤ signedSquares X := by
  have w (i j) : BalancedCut.sq X i j ≤ 1 := by simpa [BalancedCut.sq,h] using FiveProjection.bracket_bound (X i) (X j)
  have hd : 0 ≤ 4-crossing X := by unfold crossing; linarith only [w 0 2,w 0 3,w 1 2,w 1 3]
  have hi : 0 ≤ internal X := mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  unfold signedSquares
  exact add_nonneg (add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)) (by positivity)

/-- The exact coarse closure at the signed parameter t = 1/2. -/
theorem division_identity {D : Type*} [Fintype D] (X : Fin 4 → D → ℂ) (h : ∀ i, energy (X i) = 1) :
    (crossGram X X).permanent.re + signedSquares X =
    (1+BalancedCut.sq X 0 1)*(1+BalancedCut.sq X 2 3) + 9/4*crossing X + 16*internal X +
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
    fin_cases i <;> exact flip _ _ _
  have ha : energy α = crossing X := by simp [energy,hα,Fin.sum_univ_succ,crossing,add_assoc]
  have hin : Complex.normSq A * Complex.normSq B = internal X := by
    dsimp only [A,B]
    rw [Complex.star_def,Complex.normSq_conj]
    exact congrArg₂ (· * ·) (flip X 1 0) (flip X 3 2)
  have hs := signed_gluing U V hU hV (1/2) (by norm_num) α
  change (2+(1/2:ℝ)^2+(Complex.normSq A*Complex.normSq B)/(1/2:ℝ)^2)*energy α-
    energy (M.mulVec α) = energy ((M*phases).mulVec α)+energy ((residual (1/2) A B).mulVec α) at hs
  rw [ha,hin] at hs
  have hp (x y : ℂ) : Complex.normSq (x+y)+Complex.normSq (x-y) =
      2*(Complex.normSq x+Complex.normSq y) := by rw [Complex.normSq_add,Complex.normSq_sub]; ring
  have hc := hp (α 0*α 3) (α 1*α 2)
  simp only [Complex.normSq_mul,hα] at hc
  change _ = 2*(BalancedCut.sq X 0 2*BalancedCut.sq X 1 3+BalancedCut.sq X 0 3*BalancedCut.sq X 1 2) at hc
  rw [open_coarse X h]
  change (1+BalancedCut.sq X 0 1)*(1+BalancedCut.sq X 2 3) + energy (M.mulVec α) + Complex.normSq (α 0*α 3+α 1*α 2) +
    (energy ((M*phases).mulVec α)+energy ((residual (1/2) A B).mulVec α) +
    Complex.normSq (α 0*α 3-α 1*α 2)+4*internal X*(4-crossing X)) = _
  linear_combination -hs+hc

def pairFine {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) (i j : Fin 4) :=
  fine (Function.uncurry (![x i,x j] : Fin 2 → Fin 3 → Fin d → ℂ))

def tau {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) (i j : Fin 4) :=
  pairFine x i j - (1 + 11/2 * BalancedCut.sq (fun a => packet (x a)) i j)

/-- The terms containing at least one complementary proper-cut slack. -/
def properSquares {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) :=
  let X := fun i => packet (x i)
  tau x 0 1*(1+11/2*BalancedCut.sq X 2 3) + tau x 2 3*(1+11/2*BalancedCut.sq X 0 1) +
    tau x 0 1*tau x 2 3

theorem tau_nonneg {d} (schur : HomogeneousSchur d 3 3) (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) (i j) : 0 ≤ tau x i j := by
  have hp := PairBound.two_packet_lower_bound schur (![x i,x j] : Fin 2 → _)
  change energy (packet (x i)) * energy (packet (x j)) + ((2:ℝ)^3-1)*
    BalancedCut.sq (fun a => packet (x a)) i j ≤ pairFine x i j at hp
  rw [h,h] at hp
  unfold tau
  have hz : 0 ≤ BalancedCut.sq (fun a => packet (x a)) i j := Complex.normSq_nonneg _
  linarith

theorem properSquares_nonneg {d} (schur : HomogeneousSchur d 3 3) (x : Fin 4 → Fin 3 → Fin d → ℂ)
    (h : ∀ i, energy (packet (x i)) = 1) : 0 ≤ properSquares x := by
  have ht := tau_nonneg schur x h
  have hn (i j) : 0 ≤ BalancedCut.sq (fun a => packet (x a)) i j := Complex.normSq_nonneg _
  unfold properSquares
  apply add_nonneg (add_nonneg (mul_nonneg (ht 0 1) ?_) (mul_nonneg (ht 2 3) ?_)) (mul_nonneg (ht 0 1) (ht 2 3))
  · linarith only [hn 2 3]
  · linarith only [hn 0 1]

/-- Each of the three fine remainders is the nonnegative straight-cut
remainder for two groups of six thin inputs. -/
theorem fine_remainder_nonneg {d : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 4 → Fin 3 → Fin d → ℂ) (π : Equiv.Perm (Fin 4)) :
    0 ≤ fine (Function.uncurry x) - pairFine (x ∘ π) 0 1 * pairFine (x ∘ π) 2 3 := by
  let e : (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3) ≃ Fin 4 × Fin 3 :=
    ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))).trans
      (π.prodCongr (Equiv.refl _))
  have h := principal (schur _ _) e (Function.uncurry x)
  have h₁ : (fun i : Fin 2 × Fin 3 => Function.uncurry x (e (.inl i))) =
      Function.uncurry (![(x ∘ π) 0,(x ∘ π) 1] : Fin 2 → _) := by
    funext i; rcases i with ⟨j,k⟩; fin_cases j <;> rfl
  have h₂ : (fun i : Fin 2 × Fin 3 => Function.uncurry x (e (.inr i))) =
      Function.uncurry (![(x ∘ π) 2,(x ∘ π) 3] : Fin 2 → _) := by
    funext i; rcases i with ⟨j,k⟩; fin_cases j <;> rfl
  rw [h₁,h₂] at h
  exact sub_nonneg.mpr h

/-- The exact cubic coefficient left after the signed route and exterior
terms have been removed. Here the fine remainders are the actual differences
between the fine permanent and its two principal pair cuts. -/
theorem cubic_identity {d} (x : Fin 4 → Fin 3 → Fin d → ℂ) (h : ∀ i, energy (packet (x i))=1) :
    let X := fun i => packet (x i)
    let g := crossGram X X
    3 * (fine (Function.uncurry x)-g.permanent.re) =
      (∑ p : Fin 3, let y := x ∘ division p
        fine (Function.uncurry x)-pairFine y 0 1*pairFine y 2 3) +
      (∑ p : Fin 3, properSquares (x ∘ division p)) +
      37/4 * FourTrade.matchings g + ∑ p : Fin 3, signedSquares (X ∘ division p) := by
  let X := fun i => packet (x i)
  let g := crossGram X X
  have hc (p : Fin 3) := division_identity (X ∘ division p) (fun i => h _)
  have he (p : Fin 3) : (crossGram (X ∘ division p) (X ∘ division p)).permanent.re = g.permanent.re :=
    congrArg Complex.re (permanent_reindex _ g)
  simp only [he] at hc
  have hp (y : Fin 4 → Fin 3 → Fin d → ℂ) :
      pairFine y 0 1*pairFine y 2 3 - properSquares y =
        (1+11/2*BalancedCut.sq (fun i => packet (y i)) 0 1)*(1+11/2*BalancedCut.sq (fun i => packet (y i)) 2 3) := by
    simp only [properSquares,tau]; ring
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,add_zero]
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  have p₀ := hp (x ∘ division 0)
  have p₁ := hp (x ∘ division 1)
  have p₂ := hp (x ∘ division 2)
  have re (π : Equiv.Perm (Fin 4)) (i j) : BalancedCut.sq (X ∘ π) i j = BalancedCut.sq X (π i) (π j) := rfl
  have rp (π : Equiv.Perm (Fin 4)) (i j) : BalancedCut.sq (fun a => packet ((x ∘ π) a)) i j =
      BalancedCut.sq X (π i) (π j) := rfl
  simp only [rp] at p₀ p₁ p₂
  have d₀ : division 0 = 1 := rfl
  have d₁ : division 1 = Equiv.swap 1 2 := rfl
  have d₂ : division 2 = Equiv.swap 1 3 := rfl
  simp only [show (0 : Fin 2).succ = (1:Fin 3) by rfl,
    show (0 : Fin 1).succ.succ = (2:Fin 3) by rfl]
  simp (config := {decide := true}) [crossing,internal,re,rp,d₀,d₁,d₂,Equiv.swap_apply_def]
    at h₀ h₁ h₂ p₀ p₁ p₂ ⊢
  simp only [flip X 2 1,flip X 3 2,flip X 3 1] at h₀ h₁ h₂ p₀ p₁ p₂
  change 3*(_-g.permanent.re) = _ + 37/4*(BalancedCut.sq X 0 1*BalancedCut.sq X 2 3+
      BalancedCut.sq X 0 2*BalancedCut.sq X 1 3+BalancedCut.sq X 0 3*BalancedCut.sq X 1 2) + _
  linear_combination (-h₀-h₁-h₂+p₀+p₁+p₂)

end
end BlockPermanents.CubicSquares
