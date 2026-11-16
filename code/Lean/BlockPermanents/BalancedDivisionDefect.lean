import BlockPermanents.BalancedAssembly
import BlockPermanents.OccupationBasis

/-! Rotating the last three slots permutes the three balanced divisions.
Both total clasps retain exactly the same occupation counts. -/
namespace BlockPermanents.BalancedDivision
open Bend BalancedOpen BalancedAssembly OccupationBasis

def rotate {D : Type*} (x : Boundary D) : Boundary D :=
  ((x.1.1,x.2.1),(x.2.2,x.1.2))

private theorem occ_append {d p q : ℕ} (u : Word d p) (v : Word d q) (j : Fin d) :
    occ (Fin.append u v) j = occ u j + occ v j := by
  simp only [occ, OccupationSplit.counts, Finset.card_filter, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

private def joined {d k : ℕ} (x : Boundary (Word d k)) : Word d (k+k+(k+k)) :=
  Fin.append (Fin.append x.1.1 x.1.2) (Fin.append x.2.1 x.2.2)

private theorem occ_rotate {d k : ℕ} (x : Boundary (Word d k)) :
    occ (joined (rotate x)) = occ (joined x) := by
  funext j
  simp only [joined, rotate, occ_append]
  omega

theorem totalFine_rotate (d k : ℕ) (x y : Boundary (Word d k)) :
    totalFine d k (rotate x) (rotate y) = totalFine d k x y := by
  change symClasp _ _ (joined (rotate x)) (joined (rotate y)) = symClasp _ _ (joined x) (joined y)
  simp only [← kernel_word, kernel_eq, occ_rotate]

private noncomputable def coarseWord {D : Type*} [Fintype D] (x : Boundary D) : Word (Fintype.card D) 4 :=
  Fin.append (BalancedPacket.letters D x.1) (BalancedPacket.letters D x.2)

private theorem occ_pair {D : Type*} [Fintype D] (p : D × D) (j : Fin (Fintype.card D)) :
    occ (BalancedPacket.letters D p) j =
      (if Fintype.equivFin D p.1 = j then 1 else 0) +
      (if Fintype.equivFin D p.2 = j then 1 else 0) := by
  simp only [occ, OccupationSplit.counts, Finset.card_filter, Fin.sum_univ_two]
  rfl

private theorem occ_coarse_rotate {D : Type*} [Fintype D] (x : Boundary D) :
    occ (coarseWord (rotate x)) = occ (coarseWord x) := by
  funext j
  have h (v : Boundary D) : occ (coarseWord v) j = _ :=
    occ_append (BalancedPacket.letters D v.1) (BalancedPacket.letters D v.2) j
  rw [h, h]
  simp only [rotate, occ_pair]
  omega

theorem totalPacket_rotate {D : Type*} [Fintype D] (x y : Boundary D) :
    BalancedPacket.total D (rotate x) (rotate y) = BalancedPacket.total D x y := by
  change symClasp _ _ (coarseWord (rotate x)) (coarseWord (rotate y)) = symClasp _ _ (coarseWord x) (coarseWord y)
  simp only [← kernel_word, kernel_eq, occ_coarse_rotate]

theorem defect_rotate (d k : ℕ) (x y : B d k) :
    defect d k (rotate x) (rotate y) = defect d k x y := by
  simp only [defect, Matrix.sub_apply, Matrix.smul_apply,totalFine_rotate,totalPacket_rotate]

end BlockPermanents.BalancedDivision
