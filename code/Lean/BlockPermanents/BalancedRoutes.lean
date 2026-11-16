import BlockPermanents.Bridges
import Mathlib.GroupTheory.Perm.Fin

/-! # The opening of the coarse balanced cap on arbitrary mixed inputs -/
namespace BlockPermanents.BalancedRoutes
open Closures Bend
noncomputable section

abbrev Four (D : Type*) := (D×D)×(D×D)

def fromWords {D : Type*} (z : Four D → ℂ) (p : (Fin 2 → D)×(Fin 2 → D)) : ℂ :=
  z ((p.1 0,p.1 1),(p.2 0,p.2 1))

def L00 {D : Type*} [Fintype D] (z : Four D → ℂ) (p : D×D) := ∑ x, z ((x,p.1),(x,p.2))
def L01 {D : Type*} [Fintype D] (z : Four D → ℂ) (p : D×D) := ∑ x, z ((x,p.1),(p.2,x))
def L10 {D : Type*} [Fintype D] (z : Four D → ℂ) (p : D×D) := ∑ x, z ((p.1,x),(x,p.2))
def L11 {D : Type*} [Fintype D] (z : Four D → ℂ) (p : D×D) := ∑ x, z ((p.1,x),(p.2,x))
def Ndirect {D : Type*} [Fintype D] (z : Four D → ℂ) := ∑ x, ∑ y, z ((x,y),(x,y))
def Ncross {D : Type*} [Fintype D] (z : Four D → ℂ) := ∑ x, ∑ y, z ((x,y),(y,x))

private theorem clasp_two {d} (w : Word d 2) (f : Word d 2 → ℂ) :
    ∑ a, symClasp d 2 w a * f a = (f w + f (w ∘ Equiv.swap 0 1))/2 := by
  change ((symClasp d 2).mulVec f) w = _
  rw [Bridges.symClasp_action]
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
  simp [clasp,sumSlots,hu,show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide,Nat.factorial,
    div_eq_mul_inv,mul_comm]

private theorem clasp_real {d k} (a b : Word d k) : star (symClasp d k a b) = symClasp d k a b := by
  simp [symClasp,star_sum,apply_ite]

private def folded {d} (z : Four (Fin d) → ℂ) (a b : Word d 2) : ℂ :=
  (z ((a 0,a 1),(b 0,b 1)) + z ((a 0,a 1),(b 1,b 0)) +
   z ((a 1,a 0),(b 0,b 1)) + z ((a 1,a 0),(b 1,b 0)))/4

private theorem both_clasps {d} (z : Four (Fin d) → ℂ) (a b : Word d 2) :
    ∑ p : Word d 2 × Word d 2, symClasp d 2 a p.1 * star (symClasp d 2 b p.2) * fromWords z p =
      folded z a b := by
  rw [Fintype.sum_prod_type]
  simp_rw [clasp_real, mul_assoc, ← Finset.mul_sum]
  have hb (v : Word d 2) := clasp_two b (fun w => fromWords z (v,w))
  simp_rw [hb]
  rw [clasp_two a (fun v => (fromWords z (v,b)+fromWords z (v,b ∘ Equiv.swap 0 1))/2)]
  simp (config := {decide := true}) [fromWords,folded,Equiv.swap_apply_def]
  ring

private def join {d r} (h : r ≤ 2) (a : Word d (2-r)) (t : Word d r) : Word d 2 :=
  fun i => Fin.append a t (Fin.cast (Nat.sub_add_cancel h).symm i)

private theorem cap_action {d} (r : CutIndex 2 2) (z : Four (Fin d) → ℂ) (a b : Word d (2-r.val)) :
    (wordCap d 2 2 r).mulVec (fromWords z) (a,b) =
      ∑ t : Word d r, folded z (join (by omega) a t) (join (by omega) b t) := by
  simp only [wordCap, cap, Matrix.mulVec,dotProduct,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact both_clasps z _ _

/-- Four different choices of crossing edge, all with coefficient 1/4. -/
theorem one {d} (z : Four (Fin d) → ℂ) (a b : Word d 1) :
    4 * (wordCap d 2 2 (1 : CutIndex 2 2)).mulVec (fromWords z) (a,b) =
    (L00 z (a 0,b 0)+L01 z (a 0,b 0)+L10 z (a 0,b 0)+L11 z (a 0,b 0)) := by
  rw [cap_action]
  let g := fun x : Fin d => (z ((a 0,x),(b 0,x))+z ((a 0,x),(x,b 0))+
    z ((x,a 0),(b 0,x))+z ((x,a 0),(x,b 0)))/4
  have ht (t : Word d 1) : folded z (join (by decide) a t) (join (by decide) b t) = g (t 0) := rfl
  change 4*(∑ t : Word d 1, _) = _
  simp_rw [ht]
  rw [show (∑ t : Word d 1, g (t 0)) = ∑ x, g x from (Equiv.funUnique (Fin 1) (Fin d)).sum_comp g]
  simp [g,L00,L01,L10,L11,Finset.sum_add_distrib,← Finset.sum_div]
  ring

/-- The full cut has the two bijections between the two pairs of packets. -/
theorem two {d} (z : Four (Fin d) → ℂ) (a b : Word d 0) :
    2 * (wordCap d 2 2 (2 : CutIndex 2 2)).mulVec (fromWords z) (a,b) = Ndirect z + Ncross z := by
  rw [cap_action]
  let g := fun p : Fin d × Fin d => folded z ![p.1,p.2] ![p.1,p.2]
  have ht (t : Word d 2) : folded z (join (by decide) a t) (join (by decide) b t) =
      g (finTwoArrowEquiv (Fin d) t) := rfl
  change 2*(∑ t : Word d 2, _) = _
  simp_rw [ht]
  rw [(finTwoArrowEquiv (Fin d)).sum_comp g,Fintype.sum_prod_type]
  simp [g,folded,Ndirect,Ncross,← Finset.sum_div,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => z ((y,x),(x,y))),
    Finset.sum_comm (f := fun x y => z ((y,x),(y,x)))]
  ring

end
end BlockPermanents.BalancedRoutes
