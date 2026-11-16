import BlockPermanents.BalancedPacket
import BlockPermanents.BalancedRoutes

/-! Remove the factors four and two in the balanced packet half maps
before gluing. Input coefficients on the four packets may be entangled. -/
namespace BlockPermanents.BalancedPacket
open Bend BalancedRoutes Equiv
open scoped BigOperators Matrix
noncomputable section
variable {K : Type*} [Fintype K]

private def chart (K : Type*) [Fintype K] : Boundary K ≃ Four (Fin (Fintype.card K)) :=
  let e := (Fintype.equivFin K).prodCongr (Fintype.equivFin K)
  e.prodCongr e

private def moved (z : Boundary K → ℂ) := z ∘ (chart K).symm

private theorem half_reindex (r : CutIndex 2 2) (z : Boundary K → ℂ) (a) :
    (half K r).mulVec z a =
      (wordCap (Fintype.card K) 2 2 r).mulVec (fromWords (moved z)) a := by
  let e := (letters K).prodCongr (letters K)
  change (∑ x, wordCap _ 2 2 r a (e x) * z x) = _
  exact Fintype.sum_equiv e _ _ fun x => by simp [e,fromWords,moved,chart,letters]

private def through (K : Type*) [Fintype K] : Word (Fintype.card K) 1 ≃ K :=
  (Equiv.funUnique _ _).trans (Fintype.equivFin K).symm

def oneSum (z : Boundary K → ℂ) (w : K×K) : ℂ :=
  L00 z w + L01 z w + L10 z w + L11 z w

private theorem moved_one (z : Boundary K → ℂ) (a b : Fin (Fintype.card K)) :
    oneSum (moved z) (a,b) = oneSum z ((Fintype.equivFin K).symm a,(Fintype.equivFin K).symm b) := by
  let e := (Fintype.equivFin K).symm
  have he (f : K→ℂ) : (∑ i : Fin (Fintype.card K), f (e i)) = ∑ i, f i := Equiv.sum_comp e f
  unfold oneSum L00 L01 L10 L11
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply congrArg₂ (·+·)
      · exact he (fun x => z ((x,e a),(x,e b)))
      · exact he (fun x => z ((x,e a),(e b,x)))
    · exact he (fun x => z ((e a,x),(x,e b)))
  · exact he (fun x => z ((e a,x),(e b,x)))

theorem half_one (z : Boundary K → ℂ) (a b : Word (Fintype.card K) 1) :
    4 * (half K 1).mulVec z (a,b) = oneSum z (through K a,through K b) :=
  (congrArg ((4:ℂ)*·) (half_reindex 1 z (a,b))).trans
    ((one (moved z) a b).trans (moved_one z _ _))

private theorem moved_two (z : Boundary K → ℂ) :
    Ndirect (moved z) + Ncross (moved z) = Ndirect z + Ncross z := by
  let e := (Fintype.equivFin K).symm
  have he (f : K → K→ℂ) : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
    simp_rw [fun i : Fin (Fintype.card K) => Equiv.sum_comp e (fun j => f (e i) j)]
    exact Equiv.sum_comp e (fun i => ∑ j, f i j)
  exact congrArg₂ (·+·) (he (fun x y => z ((x,y),(x,y)))) (he (fun x y => z ((x,y),(y,x))))

theorem half_two (z : Boundary K → ℂ) (a b : Word (Fintype.card K) 0) :
    2 * (half K 2).mulVec z (a,b) = Ndirect z + Ncross z :=
  (congrArg ((2:ℂ)*·) (half_reindex 2 z (a,b))).trans
    ((two (moved z) a b).trans (moved_two z))

theorem one_energy (z : Boundary K → ℂ) :
    16 * energy ((half K 1).mulVec z) = energy (oneSum z) := by
  unfold energy
  rw [Finset.mul_sum,← ((through K).prodCongr (through K)).sum_comp (fun w => Complex.normSq (oneSum z w))]
  apply Finset.sum_congr rfl;intro ⟨a,b⟩ _
  change 16 * _ = Complex.normSq (oneSum z (through K a,through K b))
  rw [← half_one,Complex.normSq_mul]
  norm_num

theorem two_energy (z : Boundary K → ℂ) :
    4 * energy ((half K 2).mulVec z) = Complex.normSq (Ndirect z + Ncross z) := by
  have he (a b : Word (Fintype.card K) 0) :
      4 * Complex.normSq ((half K 2).mulVec z (a,b)) = Complex.normSq (Ndirect z + Ncross z) := by
    rw [← half_two z a b,Complex.normSq_mul];norm_num
  unfold energy
  change 4*(∑ p : Word _ 0 × Word _ 0,_) = _
  rw [Finset.mul_sum,Fintype.sum_prod_type]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul]

end
end BlockPermanents.BalancedPacket
