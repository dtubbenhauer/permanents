import BlockPermanents.RoutedUniform
import BlockPermanents.RoutedCapMatrix
import BlockPermanents.RoutedOccupationFrame
import BlockPermanents.SectorProjection

/-! The intersection matrix and the simultaneous range projector in Lemma 4B.2. -/
namespace BlockPermanents.RoutedFamilyProjection
open Matrix RoutedTrace
open scoped Matrix BigOperators ComplexOrder
noncomputable section

/-- Stack the cap rows after restricting their outputs to occupation coordinates. -/
def stack {ι b W K : Type*} [Fintype W] (B : Matrix W b ℂ) (A : ι → Matrix W K ℂ) :
    Matrix (ι × b) K ℂ := fun it k => (Bᴴ * A it.1) it.2 k

private theorem stack_gram {ι b W K : Type*} [Fintype b] [DecidableEq b] [Fintype W] [Fintype K]
    (B : Matrix W b ℂ) (P : Matrix W W ℂ) (A : ι → Matrix W K ℂ)
    (G : b → Matrix ι ι ℂ) (hB : Bᴴ * B = 1) (hP : Bᴴ * P = Bᴴ)
    (ha : ∀ i j, P * A i * (A j)ᴴ * B = B * diagonal (fun t => G t i j)) :
    stack B A * (stack B A)ᴴ = blockDiagonal G := by
  ext ⟨i,s⟩ ⟨j,t⟩
  change ((Bᴴ * A i) * (Bᴴ * A j)ᴴ) s t = _
  calc
    _ = (Bᴴ * (P * A i * (A j)ᴴ * B)) s t := by
      simp only [conjTranspose_mul,conjTranspose_conjTranspose,← Matrix.mul_assoc,hP]
    _ = _ := by
      rw [ha,← Matrix.mul_assoc,hB,one_mul,blockDiagonal_apply']
      by_cases hs : s = t
      · subst t; simp
      · simp [diagonal_apply,hs]

variable {H : Type*} [Fintype H] [DecidableEq H]

abbrev Choices (lengths : H → ℕ) (r : ℕ) :=
  ((i : H) → Equiv.Perm (Fin (lengths i))) × Equiv.Perm (Fin r)

/-- Counts for the loops and support-marked open paths in each opened gluing. -/
structure Terms (T : Type*) (N r : ℕ) where
  loops : T → T → ℕ
  marks : T → T → ℕ
  bound : ∀ i j, marks i j ≤ N ∧ loops i j + marks i j ≤ r

/-- The normalized clasp weights and the support count in the scalar of 4B.2. -/
def evaluate {N r : ℕ} (lengths : H → ℕ) (e : Terms (Choices lengths r) N r) (s ℓ : ℕ) : ℂ :=
  ∑ i, ∑ j, ((claspWeight lengths i * claspWeight lengths j : ℚ) : ℂ) *
    (s : ℂ)^(e.loops i j) * ((ℓ.choose (e.marks i j) : ℕ) : ℂ) / (N.choose (e.marks i j) : ℂ)

private theorem has_terms {N r : ℕ} (lengths : H → ℕ) (base L K : Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) :
    ∃ e : Terms (Choices lengths r) N r, ∀ (d : ℕ) (S : Finset (Fin d)) (f : Bend.Word d N → ℂ),
      Bend.Symmetric f → ∀ w,
      Closures.clasp (capAverage S r (wiring lengths base L markSplit) (claspWeight lengths)
        (reflectedAverage S r (wiring lengths base K markSplit) (claspWeight lengths) f)) w =
        evaluate lengths e S.card (occupied S w).card * f w := by
  obtain ⟨j,k,h,hv⟩ := RoutedUniform.clasped_intersection lengths base L K markSplit
  exact ⟨⟨j,k,fun i t => ⟨(h i t).1,(h i t).2.1⟩⟩,hv⟩

/-- The routed summands are independent of both the ambient dimension and the chosen support. -/
def terms {N r : ℕ} (lengths : H → ℕ) (base L K : Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) : Terms (Choices lengths r) N r :=
  (has_terms lengths base L K markSplit).choose

/-- The scalar matrix indexed by any finite collection of routes on the same boundaries. -/
def gram {N r d : ℕ} {ι : Type*} (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) (ℓ : ℕ) :
    Matrix ι ι ℂ := fun i j => evaluate lengths (terms lengths base (L i) (L j) markSplit) S.card ℓ

/-- The actual family of cap rows in the normalized occupation coordinates.
Its columns are the full physical positive and supported dual seam words. -/
def family {N r d : ℕ} {ι : Type*} (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) :
    Matrix (ι × RoutedOccupationFrame.Index d N) ((Cable (Fin N) r → Fin d) × Mark S r) ℂ :=
  stack (RoutedOccupationFrame.B d N) (fun i =>
    RoutedCapMatrix.A S r (wiring lengths base (L i) markSplit) (claspWeight lengths))

open RoutedOccupationFrame in
/-- The physical averaged rows themselves have the scalar Gram blocks of 4B.2.
All routes may share the same output sector, even when their rows are dependent. -/
theorem family_gram {N r d : ℕ} {ι : Type*} (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) :
    let C := family lengths base L markSplit S
    C * Cᴴ = blockDiagonal (fun t => gram lengths base L markSplit S (sector S t)) := by
  let V := B d N
  let A i := RoutedCapMatrix.A S r (wiring lengths base (L i) markSplit) (claspWeight lengths)
  have hp : Vᴴ * Bend.symClasp d N = Vᴴ := by
    rw [← complete,← Matrix.mul_assoc,orthonormal,Matrix.one_mul]
  apply stack_gram V (Bend.symClasp d N) A _ (orthonormal d N) hp
  intro i j
  ext w t
  rw [mul_diagonal]
  change ((Bend.symClasp d N * A i * (A j)ᴴ).mulVec (fun w => V w t)) w = _
  rw [← mulVec_mulVec,← mulVec_mulVec,Bridges.symClasp_action]
  simp only [A,RoutedCapMatrix.apply_reflect,RoutedCapMatrix.apply_cap]
  have h := (has_terms lengths base (L i) (L j) markSplit).choose_spec d S
    (fun w => V w t) (symmetric t) w
  rw [h]
  by_cases hz : V w t = 0
  · simp [hz]
  · rw [sector_eq S hz]
    exact mul_comm _ _

open RoutedOccupationFrame in
/-- Every occupied sector has a positive semidefinite intersection matrix. -/
theorem gram_psd {N r d : ℕ} {ι : Type*} [Fintype ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) (t : Index d N) :
    (gram lengths base L markSplit S (sector S t)).PosSemidef := by
  let C := family lengths base L markSplit S
  have hP := posSemidef_self_mul_conjTranspose C
  rw [show C * Cᴴ = _ from family_gram lengths base L markSplit S] at hP
  simpa only [submatrix,blockDiagonal_apply_eq] using hP.submatrix (fun i : ι => (i,t))

open RoutedOccupationFrame in
theorem gram_hermitian {N r d : ℕ} {ι : Type*} [Fintype ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) (t : Index d N) :
    (gram lengths base L markSplit S (sector S t)).IsHermitian :=
  (gram_psd lengths base L markSplit S t).isHermitian

open RoutedOccupationFrame in
/-- In each occupied sector, invert the positive eigenvalues and set zero eigenvalues to zero. -/
def inverseBlocks {N r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) :
    Matrix (ι × Index d N) (ι × Index d N) ℂ :=
  blockDiagonal (fun t => GramInverse.inverse (gram_hermitian lengths base L markSplit S t))

open RoutedOccupationFrame in
/-- The routed projector is valid on all occupied sectors, including singular ones. -/
theorem projection_spec {N r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d)) :
    let C := family lengths base L markSplit S
    let P := Cᴴ * inverseBlocks lengths base L markSplit S * C
    P.IsHermitian ∧ P * P = P ∧ Set.range P.mulVec = Set.range Cᴴ.mulVec :=
  GramInverse.sector_projection id _ _ (gram_hermitian lengths base L markSplit S)
    (family_gram lengths base L markSplit S)

open RoutedOccupationFrame in
/-- Multiplication by the adjoint of the stacked rows sums the physical reflected
caps, one freely chosen symmetric output vector for each route. -/
theorem reflected_sum {N r d : ℕ} {ι : Type*} [Fintype ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d))
    (f : ι → Index d N → ℂ) :
    (family lengths base L markSplit S)ᴴ.mulVec (Function.uncurry f) =
      fun v => ∑ i, reflectedAverage S r (wiring lengths base (L i) markSplit)
        (claspWeight lengths) ((B d N).mulVec (f i)) v.1 v.2 := by
  let A i := RoutedCapMatrix.A S r (wiring lengths base (L i) markSplit) (claspWeight lengths)
  have h i : ((B d N)ᴴ * A i)ᴴ.mulVec (f i) = fun v =>
      reflectedAverage S r (wiring lengths base (L i) markSplit) (claspWeight lengths)
        ((B d N).mulVec (f i)) v.1 v.2 := by
    rw [conjTranspose_mul,conjTranspose_conjTranspose,← mulVec_mulVec]
    exact RoutedCapMatrix.apply_reflect _ _ _ _ _
  funext v
  simp_rw [← congrFun (h _) v]
  change (∑ t : ι × Index d N, star (((B d N)ᴴ * A t.1) t.2 v) * (f t.1 t.2)) = _
  exact Fintype.sum_prod_type _

open RoutedOccupationFrame in
/-- A seam vector belongs to the projector range precisely if it is a sum of
routed reflected cups on symmetric outputs. -/
theorem mem_projection_range {N r d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (lengths : H → ℕ)
    (base : Layout lengths N r) (L : ι → Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) (S : Finset (Fin d))
    (y : ((Cable (Fin N) r → Fin d) × Mark S r) → ℂ) :
    let C := family lengths base L markSplit S
    y ∈ Set.range (Cᴴ * inverseBlocks lengths base L markSplit S * C).mulVec ↔
      ∃ f : ι → Bend.Word d N → ℂ, (∀ i, Bend.Symmetric (f i)) ∧
        y = fun v => ∑ i, reflectedAverage S r (wiring lengths base (L i) markSplit)
          (claspWeight lengths) (f i) v.1 v.2 := by
  dsimp only
  rw [(projection_spec lengths base L markSplit S).2.2]
  have sym (a : Index d N → ℂ) : Bend.Symmetric ((B d N).mulVec a) := by
    unfold Bend.Symmetric
    rw [← complete,← mulVec_mulVec, mulVec_mulVec a, orthonormal, Matrix.one_mulVec]
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨fun i => (B d N).mulVec (fun t => x (i,t)),fun i => sym _,?_⟩
    exact reflected_sum lengths base L markSplit S (fun i t => x (i,t))
  · rintro ⟨f,hf,rfl⟩
    let a i := (B d N)ᴴ.mulVec (f i)
    refine ⟨Function.uncurry a,?_⟩
    rw [reflected_sum]
    have h i : (B d N).mulVec (a i) = f i := by
      unfold a
      rw [mulVec_mulVec,complete]
      exact hf i
    simp only [h]

end
end BlockPermanents.RoutedFamilyProjection
