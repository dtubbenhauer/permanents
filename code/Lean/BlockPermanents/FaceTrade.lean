import BlockPermanents.FourTrade
import BlockPermanents.CycleMatching
import BlockPermanents.TradeMatrix

/-! # The four-face correction with any number of spectators

Averaging a prescribed four-face and a fixed matching on its complement
gives six copies of the next matching moment and three of the one after it.
-/
namespace BlockPermanents.FaceTrade
open CycleMatching Matchings Closures FourTrade
noncomputable section

/-- The four-label slack U(J)−H(J) at unit norm. -/
def slack (g : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  1 + 7/3*edges g + 3*matchings g - g.permanent.re

/-- The exact one-edge and two-edge extension counts on a four-set. -/
theorem extensions {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (J : Fin 4 ↪ Fin m) (fresh : ∀ i, J i ∉ Set.range e) :
    let W := prefixWeight g e
    let G := fun (σ : S m) (i j : Fin 4) => g (σ (J i)) (σ (J j))
    average m (fun σ => W σ * edges (G σ)) = 6*Z g (Fintype.card P+1) ∧
      average m (fun σ => W σ * matchings (G σ)) = 3*Z g (Fintype.card P+2) := by
  let W := prefixWeight g e
  let f (σ : S m) (i j : Fin 4) := sqEdge g (σ (J i)) (σ (J j))
  let G (σ : S m) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => g (σ (J i)) (σ (J j))
  have oneEdge (i j : Fin 4) (hij : i ≠ j) :
      average m (fun σ => W σ * f σ i j) = Z g (Fintype.card P+1) := by
    simpa only [W,f,mul_comm] using mean_extension g e (J i) (J j) (J.injective.ne hij) (fresh i) (fresh j)
  have twoEdges (i v w j : Fin 4) (hij : i ≠ j) (hvw : v ≠ w)
      (hiv : i ≠ v) (hiw : i ≠ w) (hjv : j ≠ v) (hjw : j ≠ w) :
      average m (fun σ => W σ * (f σ i v * f σ w j)) = Z g (Fintype.card P+2) := by
    exact mean_two_edges g e (J.injective.ne hij) (J.injective.ne hvw) (J.injective.ne hiv)
      (J.injective.ne hiw) (J.injective.ne hjv) (J.injective.ne hjw) (fresh _) (fresh _) (fresh _) (fresh _)
  have hp : average m (fun σ => W σ * edges (G σ)) = 6*Z g (Fintype.card P+1) := by
    change average m (fun σ => W σ * (f σ 0 1 + f σ 0 2 + f σ 0 3 + f σ 1 2 + f σ 1 3 + f σ 2 3)) = _
    simp only [mul_add, average_add, oneEdge 0 1 (by decide), oneEdge 0 2 (by decide), oneEdge 0 3 (by decide), oneEdge 1 2 (by decide), oneEdge 1 3 (by decide), oneEdge 2 3 (by decide)]
    ring
  have hd : average m (fun σ => W σ * matchings (G σ)) = 3*Z g (Fintype.card P+2) := by
    change average m (fun σ => W σ * (f σ 0 1 * f σ 2 3 + f σ 0 2 * f σ 1 3 + f σ 0 3 * f σ 1 2)) = _
    simp only [mul_add, average_add,
      twoEdges 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      twoEdges 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      twoEdges 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    ring
  exact ⟨hp,hd⟩

/-- Appendix A.1, the parameter trade on a prescribed four-set with a
disjoint spectator matching. Every factor is an actual Gram entry. -/
theorem weighted_trade {m : ℕ} {P D : Type*} [Fintype P] [Fintype D]
    (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (e : P × Fin 2 ↪ Fin m) (J : Fin 4 ↪ Fin m)
    (fresh : ∀ i, J i ∉ Set.range e) {u : ℝ} (hu : 0 < u) :
    let g := crossGram x x
    4*(1-u)*Z g (Fintype.card P+1) + 4*(1-1/u)*Z g (Fintype.card P+2) ≤
      average m (fun σ => prefixWeight g e σ * slack (fun i j => g (σ (J i)) (σ (J j)))) := by
  let g := crossGram x x
  let W := prefixWeight g e
  let G (σ : S m) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => g (σ (J i)) (σ (J j))
  obtain ⟨hp,hd⟩ := extensions g e J fresh
  change average m (fun σ => W σ * edges (G σ)) = _ at hp
  change average m (fun σ => W σ * matchings (G σ)) = _ at hd
  have localTrade (σ : S m) :
      (2*(1-u)/3) * (W σ * edges (G σ)) + (4*(1-1/u)/3) * (W σ * matchings (G σ)) ≤
        W σ * slack (G σ) := by
    have h := gram_trade (fun i => x (σ (J i))) (fun i => unit _) u hu
    change (G σ).permanent.re ≤ _ at h
    have h' : 2*(1-u)/3*edges (G σ) + 4*(1-1/u)/3*matchings (G σ) ≤ slack (G σ) := by
      unfold slack
      change (G σ).permanent.re ≤ 1+(5+2*u)/3*edges (G σ)+(5+4/u)/3*matchings (G σ) at h
      simp only [div_eq_mul_inv] at h ⊢
      linarith only [h]
    simpa only [mul_add, mul_left_comm, mul_assoc, mul_comm] using
      mul_le_mul_of_nonneg_left h' (prefix_nonneg g e σ)
  have h := average_le localTrade
  rw [average_add, average_smul, average_smul, hp, hd] at h
  dsimp only
  change _ ≤ average m (fun σ => W σ * slack (G σ))
  linarith only [h]

end
end BlockPermanents.FaceTrade
