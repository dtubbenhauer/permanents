import BlockPermanents.TwoStepSpectatorSquares
import BlockPermanents.CycleCuts

/-! The reflected alternating halves for either sign of a cycle in Appendix AB. -/
namespace BlockPermanents.ReflectedCycles
open Closures CycleMatching CycleComposition CycleCuts CyclePolynomial Matchings
noncomputable section

def sign (plus : Bool) : ℝ := if plus then 1 else -1

/-- Multiply the manuscript's normalized half by √u before gluing. Its
energy must consequently be divided by u. -/
def half (plus : Bool) (u : ℝ) (a b : ℂ) := (u : ℂ) * a + (sign plus : ℂ) * b

private theorem glue (plus : Bool) (u : ℝ) (a b : ℂ) :
    Complex.normSq (half plus u a b) = u^2 * Complex.normSq a + Complex.normSq b +
      (2*u*sign plus) * (star a * b).re := by
  cases plus <;> simp [half, sign, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

private theorem mean_glue {m : ℕ} (plus : Bool) (u : ℝ) (A B : S m → ℂ) :
    average m (fun σ => Complex.normSq (half plus u (A σ) (B σ))) =
      u^2 * average m (fun σ => Complex.normSq (A σ)) +
      average m (fun σ => Complex.normSq (B σ)) +
      (2*u*sign plus) * average m (fun σ => (star (A σ) * B σ).re) := by
  simp_rw [glue]
  rw [average_add, average_add, average_smul, average_smul]

/-- The lower half consists of the short matching and the coherent two-step path. -/
def lowerHalf {m : ℕ} {P : Type*} [Fintype P] (g : Gram m) (lower : P × Fin 2 ↪ Fin m)
    (i j : Fin m) (U : Finset (Fin m)) (σ : S m) : ℂ :=
  amplitude g lower σ * ∑ v ∈ U, via g i j v σ

private theorem normalize (u n s a b c e r z : ℝ) (hu : u ≠ 0) (hn : n ≠ 0)
    (hB : n*a+n*(n-1)*b = e + r) (hZ : z = u^2*a+e+(2*u*s)*c) :
    (u/n+1/u)/2*a+(n-1)/(2*u)*b+s*(c/n) = (z+r)/(2*u*n) := by
  have he : e = n*a+n*(n-1)*b-r := by linarith
  rw [hZ, he]
  field_simp
  ring

/-- Both signs of the odd cut, retaining the complete spectator path remainder. -/
theorem odd_cut_squares {m : ℕ} {D P Q : Type*} [Fintype D] [Fintype P] [Fintype Q]
    (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (upper : Q × Fin 2 ↪ Fin m) (lower : P × Fin 2 ↪ Fin m)
    (hsize : Fintype.card Q = Fintype.card P + 1) (i j : Fin m) (hij : i ≠ j)
    (hi : i ∉ Set.range lower) (hj : j ∉ Set.range lower) (U : Finset (Fin m))
    (hU : ∀ v ∈ U, i ≠ v ∧ j ≠ v ∧ v ∉ Set.range lower) (hn : 0 < U.card)
    (plus : Bool) (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    (u/(U.card : ℝ) + 1/u)/2 * Z g (Fintype.card Q) +
      ((U.card : ℝ)-1)/(2*u) * Z g (Fintype.card Q+1) +
      sign plus * pathCut g upper lower i j U =
      (average m (fun σ => Complex.normSq (half plus u (amplitude g upper σ) (lowerHalf g lower i j U σ))) +
        TwoStepSpectator.remainder x lower i j U)/(2*u*U.card) := by
  let g := crossGram x x
  dsimp only
  have gl := mean_glue plus u (amplitude g upper) (lowerHalf g lower i j U)
  have hA : average m (fun σ => Complex.normSq (amplitude g upper σ)) = Z g (Fintype.card Q) := by
    simp_rw [normSq_amplitude]
    exact mean_edges g upper
  rw [hA] at gl
  have hB := TwoStepSpectator.path_squares x unit lower i j hij hi hj U hU
  have eB (σ : S m) : Complex.normSq (lowerHalf g lower i j U σ) =
      prefixWeight g lower σ * Complex.normSq (∑ v ∈ U, via g i j v σ) := by
    rw [lowerHalf, Complex.normSq_mul, normSq_amplitude]
  apply normalize _ _ _ _ _ _ _ _ _ hu.ne' (by exact_mod_cast hn.ne')
  · simpa only [hsize, Nat.add_assoc, eB, g] using hB
  · simpa only [eB] using gl

/-- The even cut has no intermediate vertex. Its two diagonal terms have
the same matching mean, leaving one reflected square per sign. -/
theorem even_cut_squares {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (upper lower : P × Fin 2 ↪ Fin m) (plus : Bool) :
    Z g (Fintype.card P) + sign plus * average m (fun σ =>
      (star (amplitude g upper σ) * amplitude g lower σ).re) =
      average m (fun σ => Complex.normSq (half plus 1 (amplitude g upper σ) (amplitude g lower σ))) / 2 := by
  have h := mean_glue plus 1 (amplitude g upper) (amplitude g lower)
  simp only [normSq_amplitude, one_pow, one_mul, mul_one] at h
  have hmean (e : P × Fin 2 ↪ Fin m) : average m (prefixWeight g e) = Z g (Fintype.card P) :=
    mean_edges g e
  rw [hmean, hmean] at h
  rw [h]
  ring

private theorem packets_unitGram {m : ℕ} {D : Type*} [Fintype D]
    (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) : UnitGram (crossGram x x) := by
  constructor
  · intro i; simp [crossGram, Coarse.bracket_self, unit]
  · intro i j; simp [crossGram, bracket, star_sum, star_mul', mul_comm]
  · intro i j; simpa [sqEdge, crossGram, unit] using FiveProjection.bracket_bound (x i) (x j)

open private eval_circuit eval_arcs eval_reverse from BlockPermanents.CycleCuts in
/-- With the directed cycle wires specified, the mixed term is the mean of
the actual circuit. The free middle vertices contribute the two-step remainder. -/
theorem odd_circuit_squares {m r : ℕ} {D : Type*} [Fintype D]
    (x : Fin m → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1) (τ : S m)
    (upper : Fin (r+1) × Fin 2 ↪ Fin m) (lower : Fin r × Fin 2 ↪ Fin m)
    (i j v : Fin m) (U : Finset (Fin m)) (hij : i ≠ j)
    (hi : i ∉ Set.range lower) (hj : j ∉ Set.range lower)
    (hU : ∀ w ∈ U, i ≠ w ∧ j ≠ w ∧ w ∉ Set.range upper ∧ w ∉ Set.range lower) (hv : v ∈ U)
    (hw : wiring τ = (arcs upper).map Prod.swap + (arcs lower + {(i,v),(v,j)}))
    (plus : Bool) (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    (u/(U.card : ℝ) + 1/u)/2 * Z g (r+1) + ((U.card : ℝ)-1)/(2*u) * Z g (r+2) +
      sign plus * (mean g τ).re =
      (average m (fun σ => Complex.normSq (half plus u (amplitude g upper σ) (lowerHalf g lower i j U σ))) +
        TwoStepSpectator.remainder x lower i j U)/(2*u*U.card) := by
  let g := crossGram x x
  have hg := packets_unitGram x unit
  have wire (σ : S m) : circuit g τ σ =
      star (amplitude g upper σ) * (amplitude g lower σ * via g i j v σ) := by
    rw [eval_circuit g hg, hw]
    have join (a b) : evalW g σ (a+b) = evalW g σ a * evalW g σ b := by simp [evalW]
    rw [join, join, eval_reverse g hg, eval_arcs, eval_arcs]
    simp [evalW, via]
  have hm : pathCut g upper lower i j U = (mean g τ).re := by
    rw [pathCut_at _ _ _ _ _ _ _ hv hU, mean, re_complexAverage]
    simp_rw [wire]
  have h := odd_cut_squares x unit upper lower (by simp) i j hij hi hj U
    (fun w hw => ⟨(hU w hw).1,(hU w hw).2.1,(hU w hw).2.2.2⟩)
    (Finset.card_pos.mpr ⟨v,hv⟩) plus u hu
  dsimp only at h ⊢
  dsimp only [g] at hm
  simpa only [Fintype.card_fin, hm] using h

open private eval_circuit eval_arcs eval_reverse from BlockPermanents.CycleCuts in
/-- Closed even circuits on their concrete directed wires. -/
theorem even_circuit_squares {m r : ℕ} (g : Gram m) (hg : UnitGram g)
    (τ : S m) (upper lower : Fin r × Fin 2 ↪ Fin m)
    (hw : wiring τ = (arcs upper).map Prod.swap + arcs lower) (plus : Bool) :
    Z g r + sign plus * (mean g τ).re =
      average m (fun σ => Complex.normSq (half plus 1 (amplitude g upper σ) (amplitude g lower σ))) / 2 := by
  have wire (σ : S m) : circuit g τ σ = star (amplitude g upper σ) * amplitude g lower σ := by
    rw [eval_circuit g hg, hw, show ∀ a b, evalW g σ (a+b) = evalW g σ a * evalW g σ b by
      simp [evalW], eval_reverse g hg, eval_arcs, eval_arcs]
  rw [mean, re_complexAverage]
  simp_rw [wire]
  simpa only [Fintype.card_fin] using even_cut_squares g upper lower plus

end
end BlockPermanents.ReflectedCycles
