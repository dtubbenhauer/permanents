import BlockPermanents.ThreeCoarse
import BlockPermanents.Coarse
import BlockPermanents.Statement
import BlockPermanents.ThreeFine
import BlockPermanents.PairBound
import Mathlib.Logic.Equiv.Fin.Basic

namespace BlockPermanents.ThreeBlocks
noncomputable section
open scoped BigOperators ComplexOrder
open Closures

/-- Diagonal term after multiplying all three packet norms. -/
def diagonalTerm {D : Type*} [Fintype D] (y : Fin 3 → D → ℂ) : ℝ :=
  Bend.energy (y 0) * Bend.energy (y 1) * Bend.energy (y 2)

/-- The cap shared by i and j, with the remaining packet h passing through. -/
def edgeTerm {D : Type*} [Fintype D] (y : Fin 3 → D → ℂ) (i j h : Fin 3) : ℝ :=
  Complex.normSq (bracket (y i) (y j)) * Bend.energy (y h)

theorem energy_nonneg {D : Type*} [Fintype D] (v : D → ℂ) : 0 ≤ Bend.energy v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem edge_nonneg {D : Type*} [Fintype D] (y : Fin 3 → D → ℂ) (i j h : Fin 3) :
    0 ≤ edgeTerm y i j h := mul_nonneg (Complex.normSq_nonneg _) (energy_nonneg _)

/-- The actual coarse Gram permanent satisfies the homogeneous three-edge
bound, including vanishing packets, without division by any packet norm. -/
theorem coarse_homogeneous {D : Type*} [Fintype D] (y : Fin 3 → D → ℂ) :
    3 * (crossGram y y).permanent.re ≤ 3 * diagonalTerm y +
      5 * (edgeTerm y 0 1 2 + edgeTerm y 0 2 1 + edgeTerm y 1 2 0) := by
  have h := ThreeCoarse.three_exit_identity_general y
  dsimp only at h
  change 3 * (crossGram y y).permanent + _ = _ at h
  simp only [crossGram, Coarse.bracket_self] at h
  have hre := congrArg Complex.re h
  rw [← Complex.ofReal_ofNat 3] at hre
  rw [← Complex.ofReal_ofNat 5] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero] at hre
  have hs (i j h : Fin 3) := Finset.sum_nonneg (fun d (_ : d ∈ Finset.univ) =>
    Complex.normSq_nonneg (bracket (y i) (y j) * y h d - bracket (y i) (y h) * y j d))
  change ∀ i j h : Fin 3, 0 ≤ ThreeCoarse.exitSquare y i j h at hs
  unfold diagonalTerm edgeTerm
  linarith only [hre, hs 0 1 2, hs 1 0 2, hs 2 0 1]

/-- Reality of the permanent of every finite Gram matrix, directly from the
normalized packet. -/
theorem gram_permanent_real {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (x : I → D → ℂ) : (crossGram x x).permanent = ((crossGram x x).permanent.re : ℂ) := by
  rw [← packet_gram, Coarse.bracket_self, Complex.ofReal_re]


private theorem three_pair_average {D : Type*} [Fintype D] (y : Fin 3 → D → ℂ)
    (fine : ℝ) (lower : ∀ σ : Equiv.Perm (Fin 3),
      Bend.energy (y (σ 0)) * Bend.energy (y (σ 1)) * Bend.energy (y (σ 2)) +
        5 * edgeTerm y (σ 0) (σ 1) (σ 2) ≤ fine) :
    (crossGram y y).permanent.re ≤ fine := by
  have h01 := lower 1
  have h02 := lower (Equiv.swap 1 2)
  have h12 := lower ((Equiv.swap 0 1) * (Equiv.swap 1 2))
  simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] at h01 h02 h12
  have hc := coarse_homogeneous y
  unfold diagonalTerm at hc
  linarith only [h01, h02, h12, hc]

theorem coarse_eq_packet_gram {k d : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :
    blockPermanentMatrix (crossGram (Function.uncurry x) (Function.uncurry x)) =
      crossGram (fun i => packet (x i)) (fun i => packet (x i)) := by
  ext i j
  exact (packet_gram (x i) (x j)).symm

private theorem psd_of_three_gram {k : ℕ}
    (gram : ∀ x : Fin 3 → Fin k → Fin (3*k) → ℂ,
      (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
        (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re) : MarcusAt 3 k := by
  intro A hA
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  let e : Fin 3 × Fin k ≃ Fin (3*k) := finProdFinEquiv
  let x (i : Fin 3) (j : Fin k) (t : Fin (3*k)) := B (e.symm t) (i,j)
  let f := Function.uncurry x
  let y := fun i => packet (x i)
  have ha : A = crossGram f f := by
    rw [hB]
    ext i j
    exact (e.symm.sum_comp (fun t => star (B t i) * B t j)).symm
  rw [ha, coarse_eq_packet_gram x]
  refine ⟨_, sub_nonneg.mpr (gram x), ?_⟩
  rw [Complex.ofReal_sub, ← gram_permanent_real f, ← gram_permanent_real y]


/-- Three packets of thickness at least three. This follows the matching
argument of Section 7 on three labels. The marked square uses two exits,
and the three choices of spectator use three applications of the straight cut. -/
theorem three_gram {k d : ℕ} (hk : 3 ≤ k)
    (schur : SchurNormalization.HomogeneousSchur d k k)
    (lieb : ThreeFine.LiebPrincipalBlocks (Fin 2 × Fin k) (Fin k))
    (x : Fin 3 → Fin k → Fin d → ℂ) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re := by
  let y := fun i => packet (x i)
  apply three_pair_average y
  intro σ
  let pair := fun i : Fin 2 => x (σ i.castSucc)
  have hpair := PairBound.two_packet_lower_bound schur pair
  have h := ThreeFine.straight_cut_packet lieb σ x
  rw [Coarse.bracket_self, Complex.ofReal_re] at h
  have he := energy_nonneg (y (σ 2))
  have hcut := (mul_le_mul_of_nonneg_right hpair he).trans h
  have bnd : (5:ℝ) ≤ 2^k-1 := by
    have hpow : (2:ℝ)^3 ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    linarith
  change _ + 5 * edgeTerm y (σ 0) (σ 1) (σ 2) ≤ _
  calc
    _ ≤ Bend.energy (y (σ 0)) * Bend.energy (y (σ 1)) * Bend.energy (y (σ 2)) +
        ((2:ℝ)^k-1) * edgeTerm y (σ 0) (σ 1) (σ 2) :=
      add_le_add_left (mul_le_mul_of_nonneg_right bnd (edge_nonneg ..)) _
    _ = (Bend.energy (y (σ 0)) * Bend.energy (y (σ 1)) +
        ((2:ℝ)^k-1) * Complex.normSq (bracket (y (σ 0)) (y (σ 1)))) * Bend.energy (y (σ 2)) := by
      unfold edgeTerm
      ring
    _ ≤ _ := hcut

/-- Three-block matrix conclusion, retaining the two classical inputs. -/
theorem marcus_three_of_lieb {k : ℕ} (hk : 3 ≤ k)
    (schur : SchurNormalization.HomogeneousSchur (3*k) k k)
    (lieb : ThreeFine.LiebPrincipalBlocks (Fin 2 × Fin k) (Fin k)) : MarcusAt 3 k :=
  psd_of_three_gram (three_gram hk schur lieb)

end
end BlockPermanents.ThreeBlocks
