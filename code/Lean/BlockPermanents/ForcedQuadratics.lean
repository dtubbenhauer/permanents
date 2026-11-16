import BlockPermanents.ForcedRoutes

/-! # The exact product L(D) on rational quadratic packets

The labels of I are the forced pairs. Labeling the two boundary complements
independently gives their ordered lists xs,ys. This is invariant under a
reordering of either partial matching boundary.
-/
namespace BlockPermanents.ForcedQuadratics
open Negative Occupation MarkedEdges ForcedRoutes
noncomputable section

/-- Binary orthonormal-word coefficients of a symmetric quadratic. -/
def amplitude (p : Quad) (w : Fin 2 → Bool) : ℚ :=
  if w 0 then (if w 1 then p.c else p.b/2) else (if w 1 then p.b/2 else p.a)

theorem amplitude_symm (p : Quad) (w : Fin 2 → Bool) (σ : Equiv.Perm (Fin 2)) :
    amplitude p (w ∘ σ) = amplitude p w := by
  have h : ∀ ρ : Equiv.Perm (Fin 2), ρ=1 ∨ ρ=Equiv.swap 0 1 := by decide
  rcases h σ with h|h <;> subst σ
  · rfl
  · cases h0 : w 0 <;> cases h1 : w 1 <;> simp [amplitude,Equiv.swap_apply_def,h0,h1]

theorem amplitude_pair (p q : Quad) :
    ∑ w, amplitude p w * amplitude q w = gram p q := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp (fun w => amplitude p w * amplitude q w),
    Fintype.sum_prod_type]
  simp [Fintype.sum_bool, amplitude, gram,finTwoArrowEquiv]
  ring

/-- Occupied positions of an ordinary two-letter tensor word. -/
def bits (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun w := Finset.univ.filter (fun i => w i)
  invFun s i := decide (i ∈ s)
  left_inv w := by funext i; simp
  right_inv s := by ext i; simp

private theorem bits_perm {n : ℕ} (w : Fin n → Bool) (p : Equiv.Perm (Fin n)) :
    bits n (w ∘ p) = (bits n w).map p.symm.toEmbedding := by
  ext i
  simp [bits,Equiv.apply_symm_apply]

def residual (n : ℕ) (xs : List Quad) (w : Fin n → Bool) : ℚ :=
  packetWordVector n xs (bits n w)

private theorem contraction_eq {n : ℕ} (xs ys : List Quad) (p : Equiv.Perm (Fin n)) :
    contraction (residual n xs) (residual n ys) p =
      mixedWord (packetWordVector n xs) (packetWordVector n ys) p.symm := by
  unfold contraction residual mixedWord
  simp only [bits_perm]
  exact (bits n).sum_comp (fun w => packetWordVector n xs w * packetWordVector n ys (w.map p.symm.toEmbedding))

theorem residual_sum (xs ys : List Quad) (h : xs.length = ys.length) :
    let n := 2*xs.length
    (∑ p : Equiv.Perm (Fin n), contraction (residual n xs) (residual n ys) p) / 2^xs.length =
      fine xs ys := by
  dsimp only
  rw [fine_eq_symmetrized_tensor _ _ h, sum_words]
  simp only [contraction_eq]
  congr 1
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (2*xs.length)))) (fun p => mixedWord (packetWordVector _ xs) (packetWordVector _ ys) p)

/-- The sum of the actual thin permutation gluings containing every
prescribed paired packet equals the product of their Gram entries times
the untouched mixed fine closure. Equal-valued labeled packets may repeat. -/
theorem forced_weight {I : Type*} [Fintype I] [DecidableEq I] (x y : I → Quad)
    (xs ys : List Quad) (h : xs.length = ys.length) :
    let n := 2*xs.length
    let R := Fin n
    letI := Classical.decPred (@preserves I R)
    (∑ p : {p : Equiv.Perm (Slots I R) // preserves p},
      contraction (tensor (fun i => amplitude (x i)) (residual n xs))
        (tensor (fun i => amplitude (y i)) (residual n ys)) p.1) / 2^(Fintype.card I+xs.length) =
      (∏ i, gram (x i) (y i))*fine xs ys := by
  classical
  simpa only [amplitude_pair, residual_sum xs ys h] using forced_factor
    (fun i => amplitude (x i)) (fun i => amplitude (y i)) (residual (2*xs.length) xs)
    (residual (2*xs.length) ys) (fun i => amplitude_symm (y i)) xs.length

end
end BlockPermanents.ForcedQuadratics
