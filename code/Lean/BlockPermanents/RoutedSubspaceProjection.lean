import BlockPermanents.RoutedCapMatrix
import BlockPermanents.RoutedFamilyProjection
import BlockPermanents.GramInverse
import BlockPermanents.FourPlaneBasis
import BlockPermanents.ThreePlaneWords
import Mathlib.Data.Matrix.Kronecker

/-! # The routed cap projection in ambient coordinates

Ordinary letters change by the adapted unitary. A marked dual letter changes
by the conjugate of a column belonging to the prescribed subspace. -/
namespace BlockPermanents.RoutedSubspaceProjection
open Matrix RoutedTrace TensorCoordinates
open scoped Kronecker Matrix Classical
noncomputable section

variable {d N r : ℕ}

/-- Unpack the successive marked ends into the dual word, newest first. -/
def markWord (S : Finset (Fin d)) : (r : ℕ) → Mark S r ≃ (Fin r → S)
  | 0 => (Equiv.ofUnique PUnit (Fin 0 → S))
  | r+1 => ((Equiv.prodComm _ _).trans ((Equiv.refl _).prodCongr (markWord S r))).trans
      (Fin.consEquiv (fun _ => S))

/-- The conjugate frame of the dual of the marked subspace. -/
def dualColumns (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) : Matrix (Fin d) S ℂ :=
  fun i j => star (A i j.val)

theorem dualColumns_isometry (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (S : Finset (Fin d)) :
    (dualColumns A S)ᴴ * dualColumns A S = 1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j.val i.val) hA
  change (∑ k, star (star (A k i.val)) * star (A k j.val)) = _
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Subtype.ext_iff, eq_comm, mul_comm] using h

private theorem power_isometry {I P Q : Type*} [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq Q]
    (A : Matrix P Q ℂ) (hA : Aᴴ*A=1) : (power I A)ᴴ * power I A = 1 := by
  rw [← power_star, ← power_mul, hA, power_one]

private theorem tensor_isometry {I J P Q : Type*} [Fintype I] [Fintype J] [DecidableEq P] [DecidableEq Q]
    (A : Matrix I P ℂ) (B : Matrix J Q ℂ) (ha : Aᴴ*A=1) (hb : Bᴴ*B=1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  have h : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by ext; simp [Matrix.kroneckerMap, Matrix.conjTranspose_apply, mul_comm]
  rw [h, ← Matrix.mul_kronecker_mul, ha,hb,Matrix.one_kronecker_one]

/-- The mixed input frame, in ambient ordinary and ambient dual word coordinates. -/
def inputFrame (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) (N r : ℕ) :
    Matrix ((Cable (Fin N) r → Fin d) × Bend.Word d r)
      ((Cable (Fin N) r → Fin d) × Mark S r) ℂ :=
  (power (Cable (Fin N) r) A) ⊗ₖ
    ((power (Fin r) (dualColumns A S)).submatrix id (markWord S r))

theorem inputFrame_isometry (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (S : Finset (Fin d)) (N r : ℕ) :
    (inputFrame A S N r)ᴴ * inputFrame A S N r = 1 := by
  apply tensor_isometry _ _ (power_isometry A hA)
  have h := power_isometry (I := Fin r) (dualColumns A S) (dualColumns_isometry _ hA S)
  ext i j
  have hh := congrArg (fun M : Matrix (Fin r → S) (Fin r → S) ℂ => M (markWord S r i) (markWord S r j)) h
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
    Matrix.one_apply, Equiv.apply_eq_iff_eq] using hh

private theorem cancel_isometry {X Y J : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    {A : Matrix Y X ℂ} (hA : Aᴴ*A=1) (K : Matrix X J ℂ) : Aᴴ*(A*K) = K := by
  rw [← Matrix.mul_assoc,hA,Matrix.one_mul]

/-- The occupation basis in the original ambient alphabet. -/
def outputBasis (A : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Bend.Word d N) (RoutedOccupationFrame.Index d N) ℂ :=
  power (Fin N) A * RoutedOccupationFrame.B d N

theorem outputBasis_isometry (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (N : ℕ) :
    (outputBasis A N)ᴴ * outputBasis A N = 1 := by
  simp only [outputBasis,Matrix.conjTranspose_mul,Matrix.mul_assoc,
    cancel_isometry (power_isometry A hA), RoutedOccupationFrame.orthonormal]

/-- The rotated basis spans the full symmetric output, even when some sectors are empty. -/
theorem outputBasis_complete (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (N : ℕ) :
    outputBasis A N * (outputBasis A N)ᴴ = Bend.symClasp d N := by
  let U := power (Fin N) A
  have hu : U*Uᴴ=1 := Matrix.mul_eq_one_comm.mp (power_isometry A hA)
  have swap := ThreePlane.clasp_power N A
  change Bend.symClasp d N * U = U * Bend.symClasp d N at swap
  unfold outputBasis
  rw [Matrix.conjTranspose_mul]
  change U * RoutedOccupationFrame.B d N * ((RoutedOccupationFrame.B d N)ᴴ * Uᴴ) = _
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (RoutedOccupationFrame.B d N), RoutedOccupationFrame.complete,
    ← Matrix.mul_assoc, ← swap, Matrix.mul_assoc, hu, Matrix.mul_one]

/-- The ambient projector onto the output occupation with exactly ℓ marked letters. -/
def sectorProjector (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) (N ℓ : ℕ) :
    Matrix (Bend.Word d N) (Bend.Word d N) ℂ :=
  outputBasis A N * diagonal (fun t : RoutedOccupationFrame.Index d N => if RoutedOccupationFrame.sector S t = ℓ then (1:ℂ) else 0) * (outputBasis A N)ᴴ

theorem empty_sector (A : Matrix (Fin d) (Fin d) ℂ) (S : Finset (Fin d)) (N ℓ : ℕ)
    (hempty : ∀ t : RoutedOccupationFrame.Index d N, RoutedOccupationFrame.sector S t ≠ ℓ) :
    sectorProjector A S N ℓ = 0 := by simp [sectorProjector,hempty]

/-- The rotated occupation columns are fixed or annihilated according to their
number of marked letters. This describes the sector on its full symmetric basis. -/
theorem sector_columns (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (S : Finset (Fin d)) (N ℓ : ℕ) :
    sectorProjector A S N ℓ * outputBasis A N = outputBasis A N *
      diagonal (fun t : RoutedOccupationFrame.Index d N => if RoutedOccupationFrame.sector S t = ℓ then (1:ℂ) else 0) := by
  rw [sectorProjector, Matrix.mul_assoc _ (outputBasis A N)ᴴ, outputBasis_isometry A hA, Matrix.mul_one]

/-- The change of basis is the identity on route labels. -/
def outputFrame (ι : Type*) [DecidableEq ι] (A : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (ι × Bend.Word d N) (ι × RoutedOccupationFrame.Index d N) ℂ :=
  (1 : Matrix ι ι ℂ) ⊗ₖ outputBasis A N

private theorem outputFrame_isometry (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ*A=1) (N : ℕ) :
    (outputFrame ι A N)ᴴ * outputFrame ι A N = 1 :=
  tensor_isometry _ _ (by simp) (outputBasis_isometry A hA N)

private theorem orthogonal_transport {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y] [DecidableEq B]
    (T : Matrix A X ℂ) (O : Matrix B Y ℂ) (hT : Tᴴ*T=1) (hO : Oᴴ*O=1)
    (F : Matrix Y X ℂ) (G D : Matrix Y Y ℂ) (hG : F*Fᴴ=G) (hD : D.IsHermitian)
    (hGD : G*D*G=G) :
    let C := O * F * Tᴴ
    let I := O * D * Oᴴ
    let P := Cᴴ * I * C
    C*Cᴴ=O*G*Oᴴ ∧ P=T*(Fᴴ*D*F)*Tᴴ ∧
      P.IsHermitian ∧ P*P=P ∧ Set.range P.mulVec=Set.range Cᴴ.mulVec := by
  dsimp only
  have hg : (O*F*Tᴴ)*(O*F*Tᴴ)ᴴ = O*G*Oᴴ := by
    rw [← hG]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, cancel_isometry hT]
  refine ⟨hg, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc,cancel_isometry hO]
  · apply GramInverse.sandwich_projection _ _ (Matrix.isHermitian_mul_mul_conjTranspose O hD)
    rw [hg]
    have hgd : G * (D * (G * Oᴴ)) = G * Oᴴ := by rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hGD]
    simp only [Matrix.mul_assoc,cancel_isometry hO,hgd]

/-- An adapted ordinary frame and the axes whose conjugate columns give the marked dual. -/
structure Adapted (W : Submodule ℂ (FourPlaneBasis.Ambient d)) where
  A : Matrix (Fin d) (Fin d) ℂ
  S : Finset (Fin d)
  isometry : Aᴴ*A=1
  dimension : S.card = Module.finrank ℂ W
  coordinates : ∀ x : FourPlaneBasis.Ambient d, x ∈ W ↔ ∃ c : Fin d → ℂ,
    (∀ j ∉ S, c j = 0) ∧ A.mulVec c = fun i => x i

/-- In the fixed ambient alphabet the marked one-letter dual consists exactly of
conjugates of the vectors in W, with no orthogonal-complement component. -/
theorem dual_range {W : Submodule ℂ (FourPlaneBasis.Ambient d)} (f : Adapted W)
    (x : FourPlaneBasis.Ambient d) :
    x ∈ W ↔ (fun i => star (x i)) ∈ Set.range (dualColumns f.A f.S).mulVec := by
  rw [f.coordinates]
  constructor
  · rintro ⟨c,hc,he⟩
    refine ⟨fun j => star (c j.val),?_⟩
    funext i
    have h : ∑ j ∈ f.S, f.A i j * c j = ∑ j, f.A i j * c j := by
      exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by simp [hc j hj])
    change ∑ j : f.S, star (f.A i j.val) * star (c j.val) = star (x i)
    rw [f.S.sum_coe_sort (fun j => star (f.A i j) * star (c j))]
    have hfull : (∑ j ∈ f.S, f.A i j*c j) = x i := h.trans (congrFun he i)
    simpa only [star_sum, star_mul'] using congrArg star hfull
  · rintro ⟨c,he⟩
    let a (j : Fin d) := if h : j ∈ f.S then star (c ⟨j,h⟩) else 0
    refine ⟨a,fun j hj => by simp [a,hj],?_⟩
    funext i
    change ∑ j, f.A i j * a j = x i
    have hz (j : Fin d) (_ : j ∈ Finset.univ) (hj : j ∉ f.S) : f.A i j * a j = 0 := by simp [a,hj]
    rw [← Finset.sum_subset (Finset.subset_univ f.S) hz,
      ← f.S.sum_coe_sort (fun j => f.A i j * a j)]
    have h := congrArg star (congrFun he i)
    simpa only [Matrix.mulVec, dotProduct, dualColumns, star_sum, star_mul', star_star,
      a, dif_pos (Subtype.prop _)] using h

/-- Every complex subspace has such coordinates, including zero and full subspaces. -/
def adapted (W : Submodule ℂ (FourPlaneBasis.Ambient d)) : Adapted W := by
  let h := FourPlaneBasis.exists_plane_coordinates W
  let hs := h.choose_spec.choose_spec
  exact ⟨h.choose,h.choose_spec.choose,hs.1,hs.2.1,hs.2.2⟩

variable {H ι : Type*} [Fintype H] [DecidableEq H] [Fintype ι] [DecidableEq ι]
variable (lengths : H → ℕ) (base : Layout lengths N r) (L : ι → Layout lengths N r)
variable (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r)

/-- The physical routed cap family in the fixed ambient word basis on all boundary cables. -/
def ambientFamily {W : Submodule ℂ (FourPlaneBasis.Ambient d)} (f : Adapted W) :=
  outputFrame ι f.A N * RoutedFamilyProjection.family lengths base L markSplit f.S * (inputFrame f.A f.S N r)ᴴ

/-- The scalar Gram blocks on the rotated occupation sectors, extended by zero on the
nonsymmetric output. The inverse uses only occupations that occur. -/
theorem projection {W : Submodule ℂ (FourPlaneBasis.Ambient d)} (f : Adapted W) :
    let C := ambientFamily lengths base L markSplit f
    let O := outputFrame ι f.A N
    let T := inputFrame f.A f.S N r
    let F := RoutedFamilyProjection.family lengths base L markSplit f.S
    let G := blockDiagonal (fun t : RoutedOccupationFrame.Index d N =>
      RoutedFamilyProjection.gram lengths base L markSplit f.S (RoutedOccupationFrame.sector f.S t))
    let D := RoutedFamilyProjection.inverseBlocks lengths base L markSplit f.S
    let P := Cᴴ * (O*D*Oᴴ) * C
    C*Cᴴ = O*G*Oᴴ ∧ P=T*(Fᴴ*D*F)*Tᴴ ∧
      P.IsHermitian ∧ P*P=P ∧ Set.range P.mulVec = Set.range Cᴴ.mulVec := by
  apply orthogonal_transport _ _ (inputFrame_isometry _ f.isometry _ _ _) (outputFrame_isometry _ _ f.isometry _) _ _ _
    (RoutedFamilyProjection.family_gram lengths base L markSplit f.S)
  · unfold RoutedFamilyProjection.inverseBlocks Matrix.IsHermitian
    rw [blockDiagonal_conjTranspose]
    exact congrArg blockDiagonal (funext fun t => GramInverse.hermitian _)
  · unfold RoutedFamilyProjection.inverseBlocks
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    exact congrArg blockDiagonal (funext fun t => GramInverse.sandwich _)

/-- Lemma 4B.2 for an arbitrary actual marked subspace in ambient word coordinates. -/
theorem for_subspace (W : Submodule ℂ (FourPlaneBasis.Ambient d)) :
    let f := adapted W
    let C := ambientFamily lengths base L markSplit f
    let O := outputFrame ι f.A N
    let D := RoutedFamilyProjection.inverseBlocks lengths base L markSplit f.S
    let P := Cᴴ*(O*D*Oᴴ)*C
    f.S.card = Module.finrank ℂ W ∧ P.IsHermitian ∧ P*P=P ∧
      Set.range P.mulVec = Set.range Cᴴ.mulVec :=
  ⟨(adapted W).dimension, (projection lengths base L markSplit (adapted W)).2.2⟩

end
end BlockPermanents.RoutedSubspaceProjection
