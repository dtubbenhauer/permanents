import BlockPermanents.CycleMatching
import BlockPermanents.Statement
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Permutation terms and independent averages for disjoint sets of labels. -/
namespace BlockPermanents.CycleComposition
open CycleMatching Matchings
open scoped BigOperators
noncomputable section

def complexAverage (m : ℕ) (f : S m → ℂ) : ℂ :=
  (m.factorial : ℂ)⁻¹ * ∑ σ, f σ

theorem re_complexAverage {m : ℕ} (f : S m → ℂ) :
    (complexAverage m f).re = average m (fun σ => (f σ).re) := by
  change (((m.factorial : ℝ) : ℂ)⁻¹ * ∑ σ, f σ).re = _
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  rfl

def circuit {m : ℕ} (g : Gram m) (τ σ : S m) : ℂ :=
  ∏ i, g (σ (τ i)) (σ i)

def mean {m : ℕ} (g : Gram m) (τ : S m) : ℂ := complexAverage m (circuit g τ)

theorem mean_conjugate {m : ℕ} (g : Gram m) {τ π : S m} (h : IsConj τ π) :
    mean g τ = mean g π := by
  obtain ⟨ρ,hρ⟩ := isConj_iff.mp h
  have he (σ : S m) : circuit g τ (σ*ρ) = circuit g π σ := by
    unfold circuit
    apply Fintype.prod_equiv ρ
    intro i
    have h := congrArg (fun z : S m => z (ρ i)) hρ
    simpa using congrArg (fun w => g (σ w) (σ (ρ i))) h
  unfold mean complexAverage
  rw [← Equiv.sum_comp (Equiv.mulRight ρ) (circuit g τ)]
  simp only [Equiv.coe_mulRight, he]

theorem mean_real {m : ℕ} (g : Gram m) (hg : ∀ i j, star (g i j) = g j i) (τ : S m) :
    mean g τ = ((mean g τ).re : ℂ) := by
  have hc : star (mean g τ) = mean g τ⁻¹ := by
    have hσ (σ : S m) : star (circuit g τ σ) = circuit g τ⁻¹ σ := by
      simp only [circuit, star_prod, hg]
      apply Fintype.prod_equiv τ
      intro i
      simp
    simp [mean, complexAverage, hσ, star_inv₀]
  rw [mean_conjugate g (Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv τ))] at hc
  exact (Complex.conj_eq_iff_re.mp hc).symm

theorem permanent_sum {m : ℕ} (g : Gram m) :
    (Matrix.permanent g).re = ∑ τ, (mean g τ).re := by
  have h (σ : S m) : (Matrix.permanent g).re = ∑ τ, (circuit g τ σ).re := by
    rw [← Complex.re_sum]
    exact congrArg Complex.re (permanent_reindex σ g).symm
  rw [← average_const m (Matrix.permanent g).re]
  conv_lhs => arg 2; intro σ; rw [h σ]
  rw [average_sum]
  simp [mean, re_complexAverage]

/-- Splitting the ambient labels into two disjoint position sets. -/
def splitPerm {a b m : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m) (π : S a) (ρ : S b) : S m :=
  (e.symm.trans (π.sumCongr ρ)).trans e

def leftGram {a b m} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m) (σ : S m) : Gram a :=
  fun i j => g (σ (e (.inl i))) (σ (e (.inl j)))

def rightGram {a b m} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m) (σ : S m) : Gram b :=
  fun i j => g (σ (e (.inr i))) (σ (e (.inr j)))

theorem split_circuit {a b m : ℕ} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m)
    (p : S a) (q : S b) (σ : S m) (π : S a) (ρ : S b) :
    circuit g (splitPerm e p q) (σ*splitPerm e π ρ) =
      circuit (leftGram g e σ) p π * circuit (rightGram g e σ) q ρ := by
  unfold circuit
  rw [← e.prod_comp, Fintype.prod_sum_type]
  simp [splitPerm, leftGram, rightGram]

private theorem prod_means {a b} (f : S a → ℂ) (h : S b → ℂ) :
    complexAverage a (fun π => complexAverage b (fun ρ => f π * h ρ)) =
      complexAverage a f * complexAverage b h := by
  simp only [complexAverage, ← Finset.mul_sum, mul_left_comm (b.factorial : ℂ)⁻¹, ← Finset.sum_mul,
    mul_assoc]

private theorem complex_average_relabel {m} (f : S m → ℂ) (π : S m) :
    complexAverage m (fun σ => f (σ*π)) = complexAverage m f := by
  unfold complexAverage
  rw [show (∑ σ, f (σ*π)) = ∑ σ, f σ from Equiv.sum_comp (Equiv.mulRight π) f]

private theorem swap_averages {a b} (f : S a → S b → ℂ) :
    complexAverage a (fun π => complexAverage b (f π)) =
      complexAverage b (fun ρ => complexAverage a (fun π => f π ρ)) := by
  simp only [complexAverage, ← Finset.mul_sum]
  rw [Finset.sum_comm, mul_left_comm]

private theorem complex_average_const (m : ℕ) (x : ℂ) : complexAverage m (fun _ => x) = x := by
  simp [complexAverage, Fintype.card_perm, ← mul_assoc, Nat.factorial_ne_zero]

/-- A product of disjoint permutations can be averaged independently inside
their two label sets, before the final average over all labels. -/
theorem split_mean {a b m : ℕ} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m)
    (p : S a) (q : S b) :
    mean g (splitPerm e p q) = complexAverage m (fun σ =>
      mean (leftGram g e σ) p * mean (rightGram g e σ) q) := by
  let f := circuit g (splitPerm e p q)
  calc
    _ = complexAverage a (fun _ => complexAverage b (fun _ => complexAverage m f)) := by
      simp [complex_average_const,f,mean]
    _ = complexAverage a (fun π => complexAverage b (fun ρ =>
        complexAverage m (fun σ => f (σ * splitPerm e π ρ)))) := by
      simp only [complex_average_relabel]
    _ = complexAverage m (fun σ => complexAverage a (fun π => complexAverage b (fun ρ =>
        f (σ*splitPerm e π ρ)))) := by
      simp_rw [swap_averages (a := b) (b := m)]
      rw [swap_averages]
    _ = _ := by simp only [f,split_circuit,prod_means,mean]

/-- Combining two disjoint lists of matching edges. -/
def splitEdges {a b m r s : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    (u : Fin r × Fin 2 ↪ Fin a) (v : Fin s × Fin 2 ↪ Fin b) :
    (Fin r ⊕ Fin s) × Fin 2 ↪ Fin m :=
  ((Equiv.sumProdDistrib _ _ _).toEmbedding.trans (u.sumMap v)).trans e.toEmbedding

private theorem real_swap {a b} (f : S a → S b → ℝ) :
    average a (fun π => average b (f π)) =
      average b (fun ρ => average a (fun π => f π ρ)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm, mul_left_comm]

private theorem real_products {a b} (f : S a → ℝ) (h : S b → ℝ) :
    average a f * average b h = average a (fun π => average b (fun ρ => f π * h ρ)) := by
  simp only [average, ← Finset.mul_sum, mul_left_comm (b.factorial : ℝ)⁻¹, ← Finset.sum_mul,
    mul_assoc]

theorem Z_nonneg {m} (g : Gram m) (r : ℕ) : 0 ≤ Z g r :=
  moment_nonneg (fun _ => zero_le_one) (fun _ _ => Complex.normSq_nonneg _)

theorem Z_outside {m r} (g : Gram m) (h : m < 2*r) : Z g r = 0 := by
  haveI : IsEmpty (Shape (Fin r) (Fin (m-2*r)) ≃ Fin m) := ⟨fun e => by
    have hc := Fintype.card_congr e
    simp [Shape, Fintype.card_sum, Fintype.card_prod] at hc
    omega⟩
  simp [Z,moment]

/-- Disjoint matching degrees add under uniform relabeling, even when
some of the packet values coincide. -/
theorem split_Z {a b m r s : ℕ} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m)
    (hu : 2*r ≤ a) (hv : 2*s ≤ b) :
    average m (fun σ => Z (leftGram g e σ) r * Z (rightGram g e σ) s) = Z g (r+s) := by
  let u : Fin r × Fin 2 ↪ Fin a := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (by omega))
  let v : Fin s × Fin 2 ↪ Fin b := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (by omega))
  let t := splitEdges e u v
  have hprod (σ : S m) (π : S a) (ρ : S b) :
      prefixWeight (leftGram g e σ) u π * prefixWeight (rightGram g e σ) v ρ =
        prefixWeight g t (σ * splitPerm e π ρ) := by
    unfold prefixWeight
    rw [Fintype.prod_sum_type]
    simp [t, splitEdges, splitPerm, leftGram, rightGram, sqEdge]
  have hσ (σ : S m) : Z (leftGram g e σ) r * Z (rightGram g e σ) s =
      average a (fun π => average b (fun ρ => prefixWeight g t (σ * splitPerm e π ρ))) := by
    have ha : average a (prefixWeight (leftGram g e σ) u) = Z (leftGram g e σ) r := by
      simpa using mean_edges (leftGram g e σ) u
    have hb : average b (prefixWeight (rightGram g e σ) v) = Z (rightGram g e σ) s := by
      simpa using mean_edges (rightGram g e σ) v
    rw [← ha, ← hb, real_products]
    simp_rw [hprod]
  simp_rw [hσ]
  rw [real_swap]
  simp_rw [real_swap (a := m) (b := b), average_relabel, average_const]
  simpa only [prefixWeight, Fintype.card_sum, Fintype.card_fin] using mean_edges g t

theorem split_Z_le {a b m r s : ℕ} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m) :
    average m (fun σ => Z (leftGram g e σ) r * Z (rightGram g e σ) s) ≤ Z g (r+s) := by
  by_cases hu : 2*r ≤ a
  · by_cases hv : 2*s ≤ b
    · exact (split_Z g e hu hv).le
    · simpa [Z_outside _ (Nat.lt_of_not_ge hv), average_const] using Z_nonneg g (r+s)
  · simpa [Z_outside _ (Nat.lt_of_not_ge hu), average_const] using Z_nonneg g (r+s)

end
end BlockPermanents.CycleComposition
