import BlockPermanents.ThreeBlocks
import BlockPermanents.StraightCut
import BlockPermanents.Bridges
import BlockPermanents.SchurNormalization
import BlockPermanents.Quadratic
import BlockPermanents.Statement
import Mathlib.Logic.Equiv.Fin.Basic

namespace BlockPermanents
open scoped ComplexOrder

/-- The first quadratic case, with the same matrix and block definitions as
the main theorem, proved independently by the explicit one-cap formula. -/
theorem two_quadratic : MarcusAt 2 2 := by
  intro A hA
  let e : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let M := A.submatrix e.symm e.symm
  have hM : M.PosSemidef := hA.submatrix _
  obtain ⟨s, hs, h⟩ := Quadratic.psd_gap M hM
  have hper : M.permanent = A.permanent := permanent_reindex e.symm A
  have hind (i t : Fin 2) : e.symm (Quadratic.strand i t) = (i,t) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Fin.ext
    simp [e, finProdFinEquiv, Quadratic.strand, Nat.mul_comm, Nat.add_comm]
  have hblock : Quadratic.blockMatrix M = blockPermanentMatrix A := by
    ext i j
    unfold Quadratic.blockMatrix blockPermanentMatrix
    congr 1
    ext t u
    simp [M, Matrix.submatrix_apply, hind]
  exact ⟨s, hs, hper ▸ hblock ▸ h⟩

/-- Lemma 2F.1 on complex PSD matrices, from the cited homogeneous switch.
The specialization, binomial coefficients, bending, extreme cuts and the
identification of both closures with actual matrix permanents are built in. -/
theorem marcus_two {k : ℕ} (hk : 0 < k)
    (homogeneous : SchurNormalization.HomogeneousSchur (k+k) k k) : MarcusAt 2 k :=
  Bridges.marcus_two hk (SchurNormalization.homogeneousSchur_implies_unbent _ _ _ homogeneous)

/-- The normalized proper-cut identity before Gram factorization. The
ambient dimension and all columns are arbitrary. -/
theorem two_block_squares {d k : ℕ} (hk : 0 < k)
    (homogeneous : SchurNormalization.HomogeneousSchur d k k)
    (x : Fin 2 → Fin k → Fin d → ℂ) :
    (Closures.crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
      (blockPermanentMatrix (Closures.crossGram (Function.uncurry x) (Function.uncurry x))).permanent =
      ((∑ r ∈ Bend.properCuts k, Bend.cutTerm (Closures.packet (x 0)) (Closures.packet (x 1)) r : ℝ) : ℂ) :=
  Bridges.two_block_gram_gap hk (SchurNormalization.homogeneousSchur_implies_unbent _ _ _ homogeneous) x


/-- A new matrix case via the Section 7 matching argument: three packets
of common thickness k ≥ 3. The same referenced homogeneous relation is used
on (k,k) for the pair strengthening and on (2k,k) for the straight cut. -/
theorem marcus_three {k : ℕ} (hk : 3 ≤ k)
    (pairSchur : SchurNormalization.HomogeneousSchur (3*k) k k)
    (mergeSchur : SchurNormalization.HomogeneousSchur (3*k) (2*k) k) : MarcusAt 3 k := by
  apply ThreeBlocks.marcus_three_of_lieb hk pairSchur
  apply StraightCut.principal_blocks
  simpa only [Fintype.card_prod, Fintype.card_fin, show 2*k+k = 3*k by omega] using mergeSchur

end BlockPermanents
