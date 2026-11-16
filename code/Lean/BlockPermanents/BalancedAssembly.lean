import BlockPermanents.BalancedCorners
import BlockPermanents.BalancedPacket

/-! The operator identity at the balanced bend 12|34. The ambient thin
word coordinates include the packet-symmetric boundary. The crossed packet
projectors explicitly retain their internal clasps. -/
namespace BlockPermanents.BalancedAssembly
open Bend Support BalancedOpen BalancedCorners SchurNormalization
open scoped BigOperators Matrix
noncomputable section

abbrev K (d k : ℕ) := Word d k
abbrev B (d k : ℕ) := Boundary (K d k)

private def bendLin (K : Type*) :
    Matrix (Boundary K) (Boundary K) ℂ →ₗ[ℂ] Matrix (Boundary K) (Boundary K) ℂ where
  toFun := partialTranspose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pairFine (d k : ℕ) : Matrix (B d k) (B d k) ℂ := fun x y =>
  totalClasp d k k x.1 y.1 * totalClasp d k k x.2 y.2

private theorem zero_fine (d k : ℕ) :
    reflected (totalCap d k (zeroCut (k+k))) = partialTranspose (pairFine d k) := by
  ext x y
  let u := (Fin.append x.1.1 x.1.2, Fin.append x.2.1 x.2.2)
  let v := (Fin.append y.1.1 y.1.2, Fin.append y.2.1 y.2.2)
  change reflected (wordCap d (k+k) (k+k) (zeroCut _)) u v = _
  rw [first_square]
  change _*symClasp _ _ _ _ = _*symClasp _ _ _ _
  congr 1
  rw [← WireSchur.symClasp_star]
  simp [symClasp,star_sum,apply_ite,u,v]

private theorem packet_zero (K : Type*) [Fintype K] :
    partialTranspose (BalancedPacket.straight K) = BalancedPacket.straight K := by
  ext x y
  change _ * symClasp _ _ _ _ = _ * symClasp _ _ _ _
  congr 1
  rw [← WireSchur.symClasp_star]
  simp [symClasp,star_sum,apply_ite]

def a (k : ℕ) : ℂ := (k+k).choose k
def bigCoefficient (k : ℕ) : ℂ := (k+k+(k+k)).choose (k+k)

/-- Fine minus coarse before moving the three pairings. -/
def defect (d k : ℕ) :=
  (a k^2*bigCoefficient k) • totalFine d k - (24:ℂ) • BalancedPacket.total (K d k)

def parallelCorrection (d k : ℕ) :=
  (a k^2) • pairFine d k - (4:ℂ) • BalancedPacket.straight (K d k)

/-- The representative Y_p before the bend on the chosen division p=12|34. -/
def marked (d k : ℕ) := defect d k - parallelCorrection d k +
  (1/2:ℂ) • (correction false d k + correction true d k)

def fineProper (d k : ℕ) :=
  ∑ r ∈ Finset.univ.erase (zeroCut (k+k)), (weight (k+k) (k+k) r : ℂ) • reflected (totalCap d k r)

def edgeProper (flip : Bool) (d k : ℕ) :=
  ∑ u ∈ (corners k)ᶜ, weighted flip d k u

/-- Equation cubic-open as equality of matrices on the four-word space.
The two negative packet-scale terms have the relative coefficients 16 and 4
before taking the four-way and two-way cap averages. -/
theorem opening {d k : ℕ} (hk : 0<k) (hs : HomogeneousSchur d k k)
    (hb : HomogeneousSchur d (k+k) (k+k))
    (hp : HomogeneousSchur (Fintype.card (K d k)) 2 2) :
    partialTranspose (marked d k) = a k^2 • fineProper d k +
      (1/2:ℂ) • (edgeProper false d k + edgeProper true d k) -
      (16:ℂ) • reflected (BalancedPacket.half (K d k) 1) -
      (4:ℂ) • reflected (BalancedPacket.half (K d k) 2) := by
  have sf := total_schur hb
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (zeroCut (k+k)))] at sf
  change bigCoefficient k • partialTranspose (totalFine d k) = fineProper d k +
    (weight (k+k) (k+k) (zeroCut (k+k)) : ℂ) • _ at sf
  rw [show weight (k+k) (k+k) (zeroCut (k+k))=1 by simp [weight,zeroCut],Nat.cast_one,one_smul,
    zero_fine] at sf
  have sc := BalancedPacket.opening (K d k) hp
  change bendLin (K d k) (marked d k) = _
  simp only [marked,defect,parallelCorrection,map_sub,map_add,map_smul]
  change (a k^2*bigCoefficient k) • partialTranspose (totalFine d k) -
    (24:ℂ) • partialTranspose (BalancedPacket.total (K d k)) -
    (a k^2 • partialTranspose (pairFine d k) - (4:ℂ) • partialTranspose (BalancedPacket.straight (K d k))) +
    (1/2:ℂ) • (partialTranspose (correction false d k)+partialTranspose (correction true d k)) = _
  rw [← smul_smul,sf,sc,packet_zero,open_correction hk false hs,open_correction hk true hs,smul_add]
  unfold edgeProper
  abel

end
end BlockPermanents.BalancedAssembly
