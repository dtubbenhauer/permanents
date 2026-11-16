import BlockPermanents.FourMatrix

/-! # The marked four-quadratic operator on arbitrary symmetric product boundaries -/
namespace BlockPermanents.FourGeneralProduct
open FourTarget FourWireAlgebra FourWireCut FourUpright FourFootAverage FourCapOrbit
open FourRoutes FourFullValues FourAdjoints FourLocalCompression Closures TransferBlocks SchurNormalization
open scoped BigOperators
noncomputable section

/-- The ordinary packets are read from the mark toward the other boundary. -/
def upright {d : ℕ} (F : Triple d 2 → ℂ) (H : Bend.Word d 2 → ℂ) :=
  packets d 2 ori (product (first F) H)

private theorem reverse_twice (d : ℕ) (z : Boundary d) :
    packets d 2 ori (packets d 2 ori z)=z := by
  rw [← Module.End.mul_apply,← map_mul,show ori*ori=1 by decide,map_one]
  rfl

private theorem fixed {d : ℕ} (F : Triple d 2 → ℂ) (hF : Inner F) (H : Bend.Word d 2 → ℂ)
    (hH : Bend.Symmetric H) : W d (upright F H) = upright F H := by
  let z := product (first F) H
  have h (p : Fin 4 → Equiv.Perm (Fin 2)) : act d 2 (withinHom p) z=z := by
    funext w
    change (F (fun i j => w (i.castSucc,p i.castSucc j))) * H (fun j => w (3,p 3 j)) =
      F (fun i j => w (i.castSucc,j)) * H (fun j => w (3,j))
    have ha := hF (fun i => p i.castSucc) (fun i j => w (i.castSucc,j))
    have hb := clasp_invariant H (p 3).symm (fun j => w (3,j))
    rw [Bend.Symmetric,Bridges.symClasp_action] at hH
    simp only [hH,Equiv.symm_symm] at hb
    exact congrArg₂ (·*·) ha hb
  have zfix : W d z=z := by
    simp only [W,Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,MonoidHom.comp_apply,h,
      Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ]
    exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) z
  change (W d * packets d 2 ori) z=_
  rw [W_comm_packet,Module.End.mul_apply,zfix]
  rfl

private theorem open_eval {d : ℕ} (z : Boundary d) (h : W d z=z)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) :
    (bracket z (Q d 2 z)).re = (bracket z (raw (ordinary (packets d 2)) (localClasp d 2 3)
      (localClasp d 2 2) (movedPair (packets d 2) (localClasp d 2 2)) (act d 2 eWire)
      (packets d 2 swap14) z)).re := by
  have he := FourActualAlgebra.actual_open d (sand (W d)) (act d 2 eWire)
    (FourOpenings.openings_three d h₂ h₄ h₆)
  have self : Reflected (W d) (W d) := average_self (D:=Fin d) withinHom
  have readout (A : Op d 2) : bracket z (sand (W d) A z) = bracket z (A z) := by
    change bracket z (W d (A (W d z)))=_
    rw [self,h]
  simpa only [readout] using congrArg (fun T : Op d 2 => (bracket z (T z)).re) he

set_option maxHeartbeats 1900000 in
/-- Evaluation on an arbitrary internally symmetric ordinary tensor and an arbitrary
symmetric marked word vector. The ordinary factors of F may be entangled. -/
theorem marked_product {d : ℕ} (F : Triple d 2 → ℂ) (hF : Inner F)
    (H : Bend.Word d 2 → ℂ) (hH : Bend.Symmetric H) (h₂ : HomogeneousSchur d 2 2)
    (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) :
    (bracket (upright F H) (Q d 2 (upright F H))).re = cutForm F H := by
  let z := product (first F) H
  let E := localClasp d 2 3
  let P := localClasp d 2 2
  let J := ordinary (packets d 2)
  let R := movedPair (packets d 2) P
  have jz : J z=product (feet F) H := ordinary_product F H
  have hz := merged_zero F hF
  have u : J z=product (merged 0 F) H := jz.trans (by rw [hz])
  have w : R (J z)=product (merged 1 F) H := by
    change (movedPair (packets d 2) (localClasp d 2 2)) (J z)=_
    rw [show movedPair (packets d 2) (localClasp d 2 2)=suffix d 1 from reversed_pair d,
      jz,suffix_product]
  have v : E z=product (merged 2 F) H := by
    have a := DFunLike.congr_fun (entire_ordinary d 2) z
    change E (J z)=E z at a
    rw [←a,jz]; change localClasp d 2 3 _=_
    rw [entire,suffix_product]
  have x : P (J z)=product (spectator (merged 0 F)) H := by
    rw [hz,jz]; exact spectator_product _ _
  have adj {A : Op d 2} (a : Reflected A A) : AdjointableHere A :=
    fun u v => congrArg Complex.re (a u v)
  have glued := raw_cutForm J E R P z F H hH (adj (ordinary_self d 2)) (adj (local_self d 2 3))
    (adj (moved_self d 2)) (adj (local_self d 2 2)) u w v x
  have o := congrArg Complex.re (oriented_raw d (upright F H))
  change _ = (bracket (packets d 2 ori (packets d 2 ori z))
    (raw J E R P (act d 2 single) (act d 2 double) (packets d 2 ori (packets d 2 ori z)))).re at o
  rw [reverse_twice] at o
  exact (open_eval _ (fixed F hF H hH) h₂ h₄ h₆).trans (o.trans glued)

end
end BlockPermanents.FourGeneralProduct
