import BlockPermanents.FourRoutes
import BlockPermanents.WireSchur
import BlockPermanents.Bridges

/-! Open a marked symmetric clasp after arbitrary (possibly spectator-sliced)
upright maps and an arbitrary marked input map. The equality is an operator
identity on the whole mixed tensor product and includes nondiagonal entries. -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend ThreeTransfer SchurNormalization FourRoutes
open scoped BigOperators Matrix
noncomputable section

variable {A B I J S : Type*}

def legs (P : Matrix A I ℂ) (N : Matrix B J ℂ) : Matrix (A×B) (I×J) ℂ :=
  fun a i => P a.1 i.1 * N a.2 i.2

def dual (N : Matrix B J ℂ) : Matrix B J ℂ := fun a j => star (N a j)

private theorem bend_legs [Fintype A] [Fintype B] (P : Matrix A I ℂ) (N : Matrix B J ℂ)
    (L : Matrix (A×B) (A×B) ℂ) :
    partialTranspose ((legs P N)ᴴ * L * legs P N) =
      (legs P (dual N))ᴴ * partialTranspose L * legs P (dual N) := by
  ext ⟨i,j⟩ ⟨u,v⟩
  simp only [partialTranspose,legs,dual,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,map_mul,star_star,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro a _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro a' _
  simp only [star_mul',star_star]
  ring

def opened {d p k : ℕ} [Fintype S] (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ) :
    Matrix (I×J) (I×J) ℂ :=
  ∑ s, (legs (M s) N)ᴴ * totalClasp d p k * legs (M s) N

def routed {d p k : ℕ} (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex p k) (s : S) :=
  wordCap d p k r * legs (M s) (dual N)

theorem schur_open {d p k : ℕ} [Fintype S]
    (h : HomogeneousSchur d p k) (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ) :
    ((p+k).choose p : ℂ) • partialTranspose (opened M N) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • ∑ s, Support.reflected (routed M N r s) := by
  have hb : ((p+k).choose p : ℂ) • partialTranspose (totalClasp d p k) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • Support.reflected (wordCap d p k r) := by
    ext i j
    simpa only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,Support.reflected] using
      bent_schur d p k (homogeneousSchur_implies_unbent _ _ _ h) i j
  have hs (s : S) : ((p+k).choose p : ℂ) • partialTranspose ((legs (M s) N)ᴴ *
        totalClasp d p k * legs (M s) N) =
      ∑ r : CutIndex p k, (weight p k r : ℂ) • Support.reflected (routed M N r s) := by
    rw [bend_legs, ← Matrix.smul_mul,← Matrix.mul_smul,hb,Matrix.mul_sum,Matrix.sum_mul]
    simp only [Support.reflected,routed,Matrix.conjTranspose_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_assoc]
  have he : partialTranspose (opened M N) =
      ∑ s, partialTranspose ((legs (M s) N)ᴴ * totalClasp d p k * legs (M s) N) := by
    ext i j; simp only [opened,partialTranspose,Matrix.sum_apply]
  rw [he,Finset.smul_sum]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

/-- On symmetric columns a routed entry is the literal contraction of the
two ordered word coefficients; the outer index can carry entanglement. -/
theorem routed_entry {d p k : ℕ} (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ s i, Symmetric (fun w => M s w i)) (hN : ∀ j, Symmetric (fun w => N w j))
    (r : CutIndex p k) (s : S) (i : I) (j : J) (a : Word d (p-r)) (b : Word d (k-r)) :
    routed M N r s (a,b) (i,j) =
      ∑ t : Word d r, M s (fun u => Fin.append a t (Fin.cast (Nat.sub_add_cancel (WireSchur.leftLe r)).symm u)) i *
        star (N (fun u => Fin.append b t (Fin.cast (Nat.sub_add_cancel (WireSchur.rightLe r)).symm u)) j) := by
  change (wordCap d p k r).mulVec (product (fun w => M s w i) (fun w => star (N w j))) (a,b) = _
  rw [wordCap,cap_product]
  simp only [split_symmetric _ (hM s i),split_symmetric _ (hN j)]

end
end BlockPermanents.ThreeGeneralOpen
