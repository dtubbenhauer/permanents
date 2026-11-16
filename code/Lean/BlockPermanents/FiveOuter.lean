import BlockPermanents.FiveProjection
import BlockPermanents.FiveMerge
import BlockPermanents.PacketScale
import BlockPermanents.FiveMean

/-! # Cutting a labeled five-packet Gram matrix into a triple and a pair -/
namespace BlockPermanents.FiveOuter
open Bend Closures FiveProjection FiveMerge MatchingFine SchurNormalization

noncomputable section

private def positions (K : Type*) :
    (((K ⊕ K) ⊕ K) ⊕ (K ⊕ K)) ≃ (Fin 5 × K) where
  toFun
    | .inl (.inl (.inl t)) => (2,t)
    | .inl (.inl (.inr t)) => (1,t)
    | .inl (.inr t) => (0,t)
    | .inr (.inl t) => (3,t)
    | .inr (.inr t) => (4,t)
  invFun u := ![Sum.inl (.inr u.2),.inl (.inl (.inr u.2)),.inl (.inl (.inl u.2)),
    .inr (.inl u.2),.inr (.inr u.2)] u.1
  left_inv u := by rcases u with (((t|t)|t)|(t|t)) <;> rfl
  right_inv u := by obtain ⟨i,t⟩ := u; fin_cases i <;> rfl

theorem straight_outer {d k : ℕ} (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 5 → Fin k → Fin d → ℂ) (σ : FiveCycles.S) :
    tripleFine (packet (x (σ 1))) (packet (x (σ 2))) (packet (x (σ 0))) *
    fine (Sum.elim (x (σ 3)) (x (σ 4))) ≤ fine (Function.uncurry x) := by
  let e := (((finSumFinEquiv.symm : Fin (k+k) ≃ Fin k ⊕ Fin k).sumCongr (Equiv.refl (Fin k))).sumCongr
    (Equiv.refl (Fin k ⊕ Fin k))).trans ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _)))
  have h := principal (schur _ _) e (Function.uncurry x)
  have h₁ : (fun i => Function.uncurry x (e (.inl i))) =
      Sum.elim (joined (x (σ 2)) (x (σ 1))) (x (σ 0)) := by
    funext i
    rcases i with j|j
    · obtain ⟨t,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).surjective j
      change Function.uncurry x ((positions (Fin k)).trans (σ.prodCongr (Equiv.refl _)) (.inl (.inl (finSumFinEquiv.symm (finSumFinEquiv t))))) =
        Sum.elim (x (σ 2)) (x (σ 1)) (finSumFinEquiv.symm (finSumFinEquiv t))
      rw [Equiv.symm_apply_apply]
      cases t <;> rfl
    · rfl
  have h₂ : (fun i => Function.uncurry x (e (.inr i))) = Sum.elim (x (σ 3)) (x (σ 4)) := by
    funext i; cases i <;> rfl
  rw [h₁,h₂] at h
  simpa only [tripleFine,triple_permanent,fine] using h

/-- Equation (five-outer) before averaging, for every assignment of the
five labels. The permanent on the right is that of the raw atom Gram. -/
theorem outer {d k : ℕ} (hk : 3 ≤ k) (schur : ∀ p q, HomogeneousSchur d p q)
    (x : Fin 5 → Fin k → Fin d → ℂ) (hu : ∀ i, energy (packet (x i)) = 1)
    (σ : FiveCycles.S) :
    (1 + 7 * Complex.normSq (bracket (packet (x (σ 3))) (packet (x (σ 4))))) *
    ((pairGram (packet (x (σ 2))) (packet (x (σ 1))) (packet (x (σ 1)))).re +
      41/20 * Complex.normSq (pairGram (packet (x (σ 2))) (packet (x (σ 0))) (packet (x (σ 1))))) ≤
      fine (Function.uncurry x) := by
  have h := straight_outer schur x σ
  have t := testing_free_cable hk (schur _ _) (packet (x (σ 1))) (packet (x (σ 2))) (x (σ 0)) (hu (σ 2)) (hu _)
  have p := PairBound.full_caps_from_pair (schur _ _) (x (σ 3))
    (Bridges.packet_symmetric _ _ (x (σ 4)))
  rw [StraightCut.fine_permanent,hu,hu,one_mul] at p
  have hpow : (8:ℝ) ≤ 2^k := by
    calc (8:ℝ) = 2^3 := by norm_num
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) hk
  have pl : 1 + 7 * Complex.normSq (bracket (packet (x (σ 3))) (packet (x (σ 4)))) ≤
      fine (Sum.elim (x (σ 3)) (x (σ 4))) := by
    refine le_trans ?_ p
    exact add_le_add_left (mul_le_mul_of_nonneg_right (by linarith) (Complex.normSq_nonneg _)) _
  have htr : 0 ≤ tripleFine (packet (x (σ 1))) (packet (x (σ 2))) (packet (x (σ 0))) := by
    rw [tripleFine,triple_permanent]
    change 0 ≤ fine _
    rw [fine_eq_energy]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  rw [mul_comm] at h
  have base : 0 ≤ 1+7*Complex.normSq (bracket (packet (x (σ 3))) (packet (x (σ 4)))) :=
    add_nonneg zero_le_one (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  exact ((mul_le_mul_of_nonneg_left t base).trans (mul_le_mul_of_nonneg_right pl htr)).trans h

end
end BlockPermanents.FiveOuter
