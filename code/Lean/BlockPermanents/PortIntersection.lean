import BlockPermanents.PortAverages
import BlockPermanents.RoutedClasp

/-! # The exact last-cap Gram entry for any cables and support -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

def uniform (A : Type*) [Fintype A] (_ : A) : ℚ := (Fintype.card A : ℚ)⁻¹

private theorem sum_uniform {A : Type*} [Fintype A] (f : A → ℂ) :
    (∑ i,(uniform A i : ℂ)*f i)=mean f := by
  simp only [uniform,mean,Rat.cast_inv,Rat.cast_natCast,← Finset.mul_sum,div_eq_mul_inv]
  ring

private theorem mean_swap {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℂ) :
    mean (fun i => mean (f i)) = mean (fun t => mean (fun i => f i t)) := by
  simp only [mean,← Finset.sum_div,div_div]
  rw [Finset.sum_comm,mul_comm (Fintype.card B : ℂ)]

private theorem mean_mul {A : Type*} [Fintype A] (f : A → ℂ) (c : ℂ) :
    mean (fun a => f a*c)=mean f*c := by
  simp [mean,← Finset.sum_mul]; ring

/-- The Gram scalar of the actual family of routed caps on each nonempty
occupation sector. For cable i, the physical thickness is d i + 1. -/
theorem last_cap_gram {H : Type*} [Fintype H] [DecidableEq H] {N d : ℕ} (sizes : H → ℕ)
    (base : Positive sizes ≃ Option (Fin (N+1)))
    (L : H → Positive sizes ≃ Option (Fin (N+1))) (hl : ∀ i,L i ⟨i,0⟩=none)
    (S : Finset (Fin d)) (i j : H) {f : Bend.Word d (N+1) → ℂ}
    (hf : Bend.Symmetric f) (w : Bend.Word d (N+1)) :
    let P := fun i => lastWiring base (L i)
    let wt := uniform (Inside sizes)
    let ρ := ((occupied S w).card : ℂ)/(N+1 : ℂ)
    Closures.clasp (capAverage S 1 (P i) wt (reflectedAverage S 1 (P j) wt f)) w =
      (ρ+(if i=j then (S.card : ℂ)-ρ else 0)/(sizes i+1:ℂ))*f w := by
  dsimp only
  rw [glued_average,clasp_sum]
  dsimp only
  simp_rw [clasp_sum]
  simp_rw [one_port S _ _ hf w]
  simp_rw [sum_uniform]
  rw [mean_swap]
  simp_rw [mean_mul]
  exact congrArg (fun c : ℂ => c*f w) (return_mean base L hl i j (S.card : ℂ)
    (((occupied S w).card : ℂ)/(N+1 : ℂ)))

end
end BlockPermanents.RoutedTrace
