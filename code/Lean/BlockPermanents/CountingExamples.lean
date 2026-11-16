import BlockPermanents.FaceTrade
import BlockPermanents.MarkedEdges

/-! Examples 7B.2, 7C.2, and 9A.1 in the paper's label order. -/
namespace BlockPermanents.CountingExamples
open CycleMatching Matchings Closures FourTrade MarkedEdges
noncomputable section

private def pairStats (g : Gram 4) := (edges g, matchings g)

private theorem stats_perm (g : Gram 4) (h : ∀ i j, Complex.normSq (g j i) = Complex.normSq (g i j))
    (σ : S 4) : pairStats (fun i j => g (σ i) (σ j)) = pairStats g := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap σ i j _ ih =>
    let g' : Gram 4 := fun i j => g (σ i) (σ j)
    change pairStats (fun a b => g' (Equiv.swap i j a) (Equiv.swap i j b)) = _
    rw [← ih]
    change _ = pairStats g'
    have flip (a b : Fin 4) : Complex.normSq (g' b a) = Complex.normSq (g' a b) := h _ _
    fin_cases i <;> fin_cases j <;>
      simp (config := {decide := true}) [pairStats,edges,matchings,Equiv.swap_apply_def,flip 0 1,
        flip 0 2,flip 0 3,flip 1 2,flip 1 3,flip 2 3] <;> constructor <;> ring

theorem four_matchings {I : Type*} [Fintype I] (x : Fin 4 → I → ℂ) :
    let g := crossGram x x
    edges g = 6*Z g 1 ∧ matchings g = 3*Z g 2 := by
  let g := crossGram x x
  let e : Fin 0 × Fin 2 ↪ Fin 4 := ⟨fun u => u.1.elim0, fun a => a.1.elim0⟩
  have fresh (i : Fin 4) : i ∉ Set.range e := by rintro ⟨a,_⟩; exact a.1.elim0
  have fit := FaceTrade.extensions g e (Function.Embedding.refl _) fresh
  have h (i j) : Complex.normSq (g j i) = Complex.normSq (g i j) := by
    have he : g j i = star (g i j) := by simp [g,crossGram,bracket,star_sum,mul_comm]
    rw [he,Complex.star_def,Complex.normSq_conj]
  have a (σ : S 4) := congrArg Prod.fst (stats_perm g h σ)
  have b (σ : S 4) := congrArg Prod.snd (stats_perm g h σ)
  change ∀ σ : S 4, edges (fun i j => g (σ i) (σ j)) = edges g at a
  change ∀ σ : S 4, matchings (fun i j => g (σ i) (σ j)) = matchings g at b
  simpa only [prefixWeight,Finset.univ_eq_empty,Finset.prod_empty,one_mul,
    Function.Embedding.refl_apply,Fintype.card_fin,a,b,average_const] using fit

theorem four_path_coefficients :
    (![Threshold.pathCoeff 4 0,Threshold.pathCoeff 4 1,Threshold.pathCoeff 4 2] : Fin 3 → ℕ) = ![1,14,9] ∧
    (fun j : Fin 3 => ((2:ℕ).choose j.val)*(2^3-1)^j.val) = ![1,14,49] ∧
    (2:ℕ).choose 1*(2^2-1)^1 = 6 ∧
    (∀ k : ℕ, 3 ≤ k → (6*(5/2)*(2^k-1) ≥ 5*4*9 ↔ 4 ≤ k)) := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro k hk
  by_cases h : 4 ≤ k
  · have he : (2:ℕ)^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) h
    norm_num at he ⊢
    omega
  · have k3 : k=3 := by omega
    subst k
    decide

/-- Exchange one of the first two input slots, then route the three packets
cyclically. The fourth and fifth packets stay fixed. -/
def route : Thin 5 2 :=
  (Equiv.swap ((0,1) : Fin 5 × Fin 2) (1,1)).trans
    (((Equiv.swap (0 : Fin 5) 1).trans (Equiv.swap 0 2)).prodCongr (Equiv.refl _))

theorem whole_edges : whole route = {(2,0),(3,3),(4,4)} := by decide +kernel

theorem five_marks : splitEnds route = ![1,2,1,0,0] ∧
    (∑ t, (5:ℚ) / (2*(5-(whole route).card:ℕ)) * splitEnds route t) / 5 = 1 := by
  have h : splitEnds route = ![1,2,1,0,0] := by
    funext i
    fin_cases i <;> decide +kernel
  refine ⟨h,?_⟩
  have hcard : (whole route).card = 3 := by decide +kernel
  rw [h,hcard]
  norm_num [Fin.sum_univ_succ]

end
end BlockPermanents.CountingExamples
