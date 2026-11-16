import BlockPermanents.CubicSquares
import BlockPermanents.HomogeneousSchurProof

/-! The three straight fine remainders in the cubic certificate. Each of
the two groups has six atoms. The order-zero cap supplies the product of
the principal permanents, leaving the six positive-order reflected cuts. -/
namespace BlockPermanents.BalancedCubicFine
open Closures Bend MatchingFine CubicSquares SchurNormalization
noncomputable section

/-- The fine permanent above the straight cut is the sum of the positive-order
cap squares. This equality also applies to zero and unnormalized packets. -/
theorem straight_gap {d k : ℕ} (l r : Fin k → Fin d → ℂ) :
    fine (Sum.elim l r) - fine l * fine r =
      ∑ i ∈ Finset.univ.erase (zeroCut k), cutTerm (packet l) (packet r) i := by
  have total := congrArg Complex.re (closed_bent_schur d k k
    (homogeneousSchur_implies_unbent _ _ _ (homogeneousSchur d k k)) (packet l) (packet r))
  rw [StraightCut.fine_permanent] at total
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, zero_mul, sub_zero] at total
  change fine (Sum.elim l r) = ∑ i, cutTerm (packet l) (packet r) i at total
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (zeroCut k))] at total
  have hz : cutTerm (packet l) (packet r) (zeroCut k) = fine l * fine r := by
    rw [cutTerm, zero_cap_energy (Bridges.packet_symmetric _ _ _) (Bridges.packet_symmetric _ _ _),
      fine_eq_energy, fine_eq_energy]
    simp [weight,zeroCut]
  rw [hz] at total
  linarith

/-- Thin inputs of one six-atom packet, in the indicated pair of cubic blocks. -/
def six {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) (i j : Fin 4) : Fin 6 → Fin d → ℂ :=
  Function.uncurry (![x i, x j] : Fin 2 → _) ∘ (@finProdFinEquiv 2 3).symm

/-- The chosen straight division, before averaging over the three balanced bends. -/
def squares {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) : ℝ :=
  ∑ r ∈ Finset.univ.erase (zeroCut 6), cutTerm (packet (six x 0 1)) (packet (six x 2 3)) r

theorem squares_nonneg {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) : 0 ≤ squares x :=
  Finset.sum_nonneg fun r _ => cutTerm_nonneg _ _ r

/-- The actual straight remainder appearing in the cubic identity, for an
arbitrary ordering of the four packets. -/
theorem fine_remainder {d : ℕ} (x : Fin 4 → Fin 3 → Fin d → ℂ) (π : Equiv.Perm (Fin 4)) :
    fine (Function.uncurry x) - pairFine (x ∘ π) 0 1 * pairFine (x ∘ π) 2 3 =
      squares (x ∘ π) := by
  let y := x ∘ π
  let a : Fin 6 ≃ Fin 2 × Fin 3 := (@finProdFinEquiv 2 3).symm
  let e : (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3) ≃ Fin 4 × Fin 3 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  let perm := (π.prodCongr (Equiv.refl (Fin 3)))
  let c := (a.sumCongr a).trans (e.trans perm)
  have h₁ (i : Fin 2 × Fin 3) : Function.uncurry y (e (.inl i)) =
      Function.uncurry (![y 0,y 1] : Fin 2 → _) i := by
    rcases i with ⟨j,t⟩
    fin_cases j <;> rfl
  have h₂ (i : Fin 2 × Fin 3) : Function.uncurry y (e (.inr i)) =
      Function.uncurry (![y 2,y 3] : Fin 2 → _) i := by
    rcases i with ⟨j,t⟩
    fin_cases j <;> rfl
  have he : Sum.elim (six y 0 1) (six y 2 3) = Function.uncurry x ∘ c := by
    funext i
    cases i with
    | inl u => exact (h₁ (a u)).symm
    | inr u => exact (h₂ (a u)).symm
  have hp (i j) : fine (six y i j) = pairFine y i j := fine_reindex a _
  have h := straight_gap (six y 0 1) (six y 2 3)
  rwa [he, fine_reindex, hp, hp] at h

end
end BlockPermanents.BalancedCubicFine
