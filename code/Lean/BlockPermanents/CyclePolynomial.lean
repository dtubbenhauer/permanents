import BlockPermanents.CycleComposition

/-! # Composing polynomial matching bounds on disjoint permutation cycles -/
namespace BlockPermanents.CyclePolynomial
open CycleMatching CycleComposition Matchings
noncomputable section

abbrev Polynomial := List (ℕ × ℚ)

def evaluate {m} (g : Gram m) (p : Polynomial) : ℝ :=
  (p.map (fun t => (t.2 : ℝ) * Z g t.1)).sum

def combine (p q : Polynomial) : Polynomial :=
  p.flatMap (fun x => q.map (fun y => (x.1+y.1, x.2*y.2)))

structure UnitGram {m : ℕ} (g : Gram m) : Prop where
  diag : ∀ i, g i i = 1
  herm : ∀ i j, star (g i j) = g j i
  unit : ∀ i j, sqEdge g i j ≤ 1

def Admits {m : ℕ} (τ : S m) (p : Polynomial) : Prop :=
  (∀ t ∈ p, 0 ≤ t.2) ∧ ∀ g : Gram m, UnitGram g → |(mean g τ).re| ≤ evaluate g p

private theorem evaluate_nonneg {m : ℕ} (g : Gram m) {p : Polynomial} (hp : ∀ t ∈ p, 0 ≤ t.2) :
    0 ≤ evaluate g p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (by exact_mod_cast hp t ht) (Z_nonneg g _)

private theorem average_list {m : ℕ} {T : Type*} (l : List T) (f : T → S m → ℝ) :
    average m (fun σ => (l.map (fun i => f i σ)).sum) = (l.map (fun i => average m (f i))).sum := by
  induction l with
  | nil => simp [average_const]
  | cons a l ih => simp [average_add, ih]

private theorem average_combine {a b m} (g : Gram m) (e : Fin a ⊕ Fin b ≃ Fin m)
    (p q : Polynomial) (hp : ∀ t ∈ p, 0 ≤ t.2) (hq : ∀ t ∈ q, 0 ≤ t.2) :
    average m (fun σ => evaluate (leftGram g e σ) p * evaluate (rightGram g e σ) q) ≤
      evaluate g (combine p q) := by
  let L := leftGram g e
  let R := rightGram g e
  let f := fun (x y : ℕ × ℚ) σ => ((x.2*y.2 : ℚ) : ℝ) * (Z (L σ) x.1 * Z (R σ) y.1)
  have he (σ) : evaluate (leftGram g e σ) p * evaluate (rightGram g e σ) q =
      (p.map (fun x => (q.map (fun y => f x y σ)).sum)).sum := by
    simp only [evaluate, f, L, R, Rat.cast_mul]
    rw [← List.sum_map_mul_right]
    simp only [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    apply List.map_congr_left
    intro y _
    ring
  simp_rw [he]
  rw [average_list]
  simp_rw [average_list]
  unfold evaluate combine
  simp only [List.map_flatMap, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_apply]
  apply List.sum_le_sum
  intro x hx
  simp only [Function.comp_apply, List.map_map]
  apply List.sum_le_sum
  intro y hy
  dsimp only [f,L,R]
  rw [average_smul]
  apply mul_le_mul_of_nonneg_left (split_Z_le g e)
  exact_mod_cast mul_nonneg (hp x hx) (hq y hy)

/-- Juxtaposed cycle closures satisfy the convolution of their local
matching bounds. All averaging, Hermitian reality, signs, and matching
extensions are over the concrete Gram entries. -/
theorem admits_combine {a b m : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m)
    {p : S a} {q : S b} {P Q : Polynomial}
    (hp : Admits p P) (hq : Admits q Q) : Admits (splitPerm e p q) (combine P Q) := by
  constructor
  · intro z hz
    obtain ⟨x,hx,hm⟩ := List.mem_flatMap.mp hz
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
    subst z
    exact mul_nonneg (hp.1 _ hx) (hq.1 _ hy)
  intro g hg
  have hL (σ : S m) : UnitGram (leftGram g e σ) := ⟨fun _ => hg.diag _,fun _ _ => hg.herm ..,
    fun _ _ => hg.unit ..⟩
  have hR (σ : S m) : UnitGram (rightGram g e σ) := ⟨fun _ => hg.diag _,fun _ _ => hg.herm ..,
    fun _ _ => hg.unit ..⟩
  rw [split_mean, re_complexAverage]
  apply (abs_average_le _).trans
  apply le_trans (average_le ?_) (average_combine g e P Q hp.1 hq.1)
  intro σ
  rw [mean_real _ (hL σ).herm p, mean_real _ (hR σ).herm q, ← Complex.ofReal_mul,
    Complex.ofReal_re, abs_mul]
  exact mul_le_mul (hp.2 _ (hL σ)) (hq.2 _ (hR σ)) (abs_nonneg _) (evaluate_nonneg _ hp.1)

end
end BlockPermanents.CyclePolynomial
