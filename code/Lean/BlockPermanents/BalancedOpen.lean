import BlockPermanents.SchurNormalization
import BlockPermanents.Support

/-! The balanced bend on four ordinary packets. Both crossing pairings are
evaluated on the same ordered word space. The identities are entrywise,
so they also apply to entangled mixed states. -/
namespace BlockPermanents.BalancedOpen
open Bend Support SchurNormalization
open scoped BigOperators Matrix
noncomputable section

abbrev Boundary (K : Type*) := (K × K) × (K × K)

def arrange {K : Type*} (flip : Bool) (z : Boundary K) : Boundary K :=
  if flip then ((z.1.1,z.2.2),(z.1.2,z.2.1)) else ((z.1.1,z.2.1),(z.1.2,z.2.2))

def productRows {K U V : Type*} (flip : Bool) (A : Matrix U (K×K) ℂ)
    (B : Matrix V (K×K) ℂ) : Matrix (U×V) (Boundary K) ℂ :=
  fun z c => A z.1 (arrange flip c).1 * B z.2 (arrange flip c).2

def productOperator {K : Type*} (flip : Bool) (A B : Matrix (K×K) (K×K) ℂ) :
    Matrix (Boundary K) (Boundary K) ℂ :=
  fun z c => A (arrange flip z).1 (arrange flip c).1 * B (arrange flip z).2 (arrange flip c).2

theorem bend_product {K : Type*} (flip : Bool) (A B : Matrix (K×K) (K×K) ℂ) :
    partialTranspose (productOperator flip A B) =
      productOperator flip (partialTranspose A) (partialTranspose B) := by
  cases flip <;> rfl

theorem glue_product {K U V : Type*} [Fintype U] [Fintype V] (flip : Bool)
    (A : Matrix U (K×K) ℂ) (B : Matrix V (K×K) ℂ) :
    reflected (productRows flip A B) = productOperator flip (reflected A) (reflected B) := by
  ext i j
  simp only [reflected,productOperator,productRows,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,star_mul',Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A pair of real square-fork caps on the two disjoint crossing edges,
before gluing. The order of the two remaining pairs of words is explicit. -/
def productCap (flip : Bool) (d k : ℕ) (r t : CutIndex k k) :=
  productRows flip (wordCap d k k r) (wordCap d k k t)

/-- Upright two-block fine clasps on the two crossing edges. -/
def productFine (flip : Bool) (d k : ℕ) :=
  productOperator flip (totalClasp d k k) (totalClasp d k k)

theorem crossing_schur {d k : ℕ} (flip : Bool) (h : HomogeneousSchur d k k) :
    (((k+k).choose k : ℂ)^2) • partialTranspose (productFine flip d k) =
      ∑ r : CutIndex k k, ∑ t : CutIndex k k,
        ((weight k k r : ℂ) * (weight k k t : ℂ)) • reflected (productCap flip d k r t) := by
  have hs := bent_schur d k k (homogeneousSchur_implies_unbent _ _ _ h)
  ext i j
  simp only [productFine,bend_product,productCap,glue_product,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,productOperator,pow_two]
  rw [mul_mul_mul_comm, hs, hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  unfold reflected
  ring

private def join {d k : ℕ} (z : Boundary (Word d k)) : Word d (k+k) × Word d (k+k) :=
  (Fin.append z.1.1 z.1.2, Fin.append z.2.1 z.2.2)

/-- The fine four-packet clasp, with the ordinary pair and the turned pair
joined without changing the order of their thin slots. -/
def totalFine (d k : ℕ) : Matrix (Boundary (Word d k)) (Boundary (Word d k)) ℂ :=
  fun x y => totalClasp d (k+k) (k+k) (join x) (join y)

def totalCap (d k : ℕ) (r : CutIndex (k+k) (k+k)) :
    Matrix (Word d (k+k-r) × Word d (k+k-r)) (Boundary (Word d k)) ℂ :=
  fun z x => wordCap d (k+k) (k+k) r z (join x)

/-- The merged fine opening on the same four-word input as both pairings. -/
theorem total_schur {d k : ℕ} (h : HomogeneousSchur d (k+k) (k+k)) :
    (((k+k+(k+k)).choose (k+k) : ℂ)) • partialTranspose (totalFine d k) =
      ∑ r : CutIndex (k+k) (k+k), (weight (k+k) (k+k) r : ℂ) • reflected (totalCap d k r) := by
  ext i j
  simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  exact bent_schur d (k+k) (k+k) (homogeneousSchur_implies_unbent _ _ _ h) (join i) (join j)

end
end BlockPermanents.BalancedOpen
