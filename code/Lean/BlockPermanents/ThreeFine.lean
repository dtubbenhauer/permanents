import BlockPermanents.Closures
import BlockPermanents.Statement
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The straight principal cut on three packets

The published two-principal-block inequality of Lieb [Lie66], also proved
by Djoković [Djo69], is isolated as a proposition on ordinary PSD matrices.
In the coefficient theorem, scale the first principal block by λ. The
leading coefficient is the product of its permanent and the complementary
principal permanent; all coefficients are nonnegative. Set λ = 1.
A zero row gives equality. See DOI 10.1512/iumj.1967.16.16008 and
10.1017/S0017089500000525.
The passage to Gram matrices of thin columns, simultaneous row/column
reindexing, and each choice of spectator are proved below.
-/
namespace BlockPermanents.ThreeFine

open Closures
open scoped ComplexOrder

noncomputable section
variable {I J L K D : Type*}

/-- The classical principal-block inequality, with one index set for each
block. The off-diagonal blocks of the PSD matrix are unrestricted. -/
def LiebPrincipalBlocks (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ A : Matrix (I ⊕ J) (I ⊕ J) ℂ, A.PosSemidef →
    (A.submatrix Sum.inl Sum.inl).permanent.re *
      (A.submatrix Sum.inr Sum.inr).permanent.re ≤ A.permanent.re

theorem gram_psd [Fintype D] [Fintype I] (x : I → D → ℂ) : (crossGram x x).PosSemidef := by
  let B : Matrix D I ℂ := fun r i => x i r
  change (B.conjTranspose * B).PosSemidef
  exact Matrix.posSemidef_conjTranspose_mul_self B

/-- The straight cut with an arbitrary ordering of all thin columns. -/
theorem principal_cut [Fintype I] [Fintype J] [Fintype L] [Fintype D]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (lieb : LiebPrincipalBlocks I J) (e : (I ⊕ J) ≃ L) (x : L → D → ℂ) :
    (crossGram (fun i => x (e (Sum.inl i))) (fun i => x (e (Sum.inl i)))).permanent.re *
      (crossGram (fun j => x (e (Sum.inr j))) (fun j => x (e (Sum.inr j)))).permanent.re ≤
      (crossGram x x).permanent.re := by
  have h := lieb ((crossGram x x).submatrix e e) ((gram_psd x).submatrix e)
  rw [permanent_reindex e] at h
  exact h

/-- Concatenate the two packets in the principal pair and the remaining
packet. Reindex the packet labels on both boundaries by the same σ. -/
def splitSlots (K : Type*) (σ : Equiv.Perm (Fin 3)) : ((Fin 2 × K) ⊕ K) ≃ (Fin 3 × K) :=
  let base : ((Fin 2 × K) ⊕ K) ≃ (Fin 3 × K) :=
    { toFun := Sum.elim (fun p => (p.1.castSucc, p.2)) (fun t => (Fin.last 2, t))
      invFun := fun p => Fin.lastCases (Sum.inr p.2) (fun i => Sum.inl (i,p.2)) p.1
      left_inv := by intro a; cases a with
                     | inl a => simp
                     | inr a => simp only [Sum.elim_inr, Fin.lastCases_last]
      right_inv := by
        rintro ⟨i,t⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.lastCases_last, Sum.elim_inr]
        · simp }
  base.trans (σ.prodCongr (Equiv.refl K))

/-- The fine closure on all three matrix packets dominates the two-packet
fine closure multiplied by the spectator's diagonal Gram permanent. -/
theorem straight_cut [Fintype K] [DecidableEq K] [Fintype D]
    (lieb : LiebPrincipalBlocks (Fin 2 × K) K) (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → K → D → ℂ) :
    let pair : Fin 2 × K → D → ℂ := fun p => x (σ p.1.castSucc) p.2
    (crossGram pair pair).permanent.re *
      (crossGram (x (σ 2)) (x (σ 2))).permanent.re ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re :=
  principal_cut lieb (splitSlots K σ) (Function.uncurry x)

/-- The right-hand packet factor can be read directly as the squared norm
of the spectator packet with the paper's square-root-factorial normalization. -/
theorem straight_cut_packet [Fintype K] [DecidableEq K] [Fintype D]
    (lieb : LiebPrincipalBlocks (Fin 2 × K) K) (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → K → D → ℂ) :
    let pair : Fin 2 × K → D → ℂ := fun p => x (σ p.1.castSucc) p.2
    (crossGram pair pair).permanent.re *
      (bracket (packet (x (σ 2))) (packet (x (σ 2)))).re ≤
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent.re := by
  dsimp only
  rw [packet_gram]
  exact straight_cut lieb σ x

end
end BlockPermanents.ThreeFine
