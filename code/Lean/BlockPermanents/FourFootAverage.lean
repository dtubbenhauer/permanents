import BlockPermanents.FourWireCutDefs
import BlockPermanents.FourActualAlgebra
import BlockPermanents.ThreeWire

/-! # Averaging the ordinary packets and their four spectator strands -/
namespace BlockPermanents.FourFootAverage
open FourTarget FourWireCut FourCapOrbit FourCapValues FourRoutes FourWireAlgebra TransferBlocks
open LocalAction LocalGroup Equiv
open scoped BigOperators
noncomputable section

def liftOrd (p : Perm (Fin 3)) : FourPerm := (finSuccEquivLast.trans (p.optionCongr.trans finSuccEquivLast.symm))

private theorem lifts : ((ThreeWire.permutations 3).map liftOrd) =
    [1,swap12,swap23,swap12*swap23,swap23*swap12,swap12*swap23*swap12] ∨
    ((ThreeWire.permutations 3).map liftOrd).Perm
      [1,swap12,swap23,swap12*swap23,swap23*swap12,swap12*swap23*swap12] := by decide +kernel

private theorem six (f : FourPerm → ℂ) :
    (∑ p : Perm (Fin 3), f (liftOrd p)) = f 1+f swap12+f swap23+f (swap12*swap23)+
      f (swap23*swap12)+f (swap12*swap23*swap12) := by
  rw [← ThreeWire.sum_permutations]
  have l := lifts.elim (fun h => h ▸ List.Perm.refl _) id
  have h := (l.map f).sum_eq (M := ℂ)
  simpa [List.map_map,Function.comp_def,add_assoc] using h

def first {d : ℕ} (F : Triple d 2 → ℂ) (w : Pos → Fin d) := F (fun i j => w (i,j))

theorem ordinary_product {d : ℕ} (F : Triple d 2 → ℂ) (H : Bend.Word d 2 → ℂ) :
    ordinary (packets d 2) (product (first F) H) = product (feet F) H := by
  funext w
  let f (p : FourPerm) := (packets d 2 p (product (first F) H)) w
  have h (p : Perm (Fin 3)) : f (liftOrd p) =
      F (fun i j => w ((p i).castSucc,j)) * H (fun j => w (3,j)) := by
    have hh : finSuccEquivLast (3:Fin 4) = none := by decide
    simp [f,packets,act,wires,Transfer.tensorAction,first,product,liftOrd,hh]
  have hsum := six f
  simp_rw [h] at hsum
  have inv : (∑ p : Perm (Fin 3), F (fun i j => w ((p.symm i).castSucc,j))) =
      ∑ p : Perm (Fin 3), F (fun i j => w ((p i).castSucc,j)) :=
    Equiv.sum_comp (Equiv.inv (Perm (Fin 3))) (fun p : Perm (Fin 3) => F (fun i j => w ((p i).castSucc,j)))
  simp only [ordinary,triple,LinearMap.smul_apply,Pi.smul_apply,Rat.smul_def,smul_eq_mul,
    LinearMap.add_apply,Pi.add_apply,← map_mul]
  change ((↑(1/6:ℚ):ℂ) * (f 1+f swap12+f swap23+f (swap12*swap23)+f (swap23*swap12)+
    f (swap12*swap23*swap12))) = _
  rw [← hsum,← Finset.sum_mul]
  simp [product,feet,inv,mul_assoc]

theorem merged_zero {d : ℕ} (F : Triple d 2 → ℂ) (hF : Inner F) : merged 0 F = feet F := by
  have hs : ∀ p : Perm (A 0), (order 0 p).trans (order 0 1).symm =
      twist 1 (fun i => if i=2 then p else 1) := by decide
  funext w
  simp only [merged,hs,feet_invariant hF,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  norm_num [A,Nat.factorial]
  ring

/-- The average of three ordinary packets absorbs their reversal. -/
theorem ori_product {d : ℕ} (F : Triple d 2 → ℂ) (H : Bend.Word d 2 → ℂ) :
    packets d 2 (Equiv.swap 0 2) (product (feet F) H) = product (feet F) H := by
  let u := packets d 2 swap12
  let v := packets d 2 swap23
  let f := ordinary (packets d 2)
  have uu : u*u=1 := by change packets d 2 _*packets d 2 _=_;rw [← map_mul,show swap12*swap12=1 by decide,map_one]
  have vv : v*v=1 := by change packets d 2 _*packets d 2 _=_;rw [← map_mul,show swap23*swap23=1 by decide,map_one]
  have b : u*v*u=v*u*v := by dsimp [u,v];simp only [← map_mul];congr 1;decide
  have hu : u*f=f := triple_left _ _ uu
  have hv : v*f=f := by change v*triple u v=triple u v;rw [triple_flip _ _ b,triple_left _ _ vv]
  have he : packets d 2 (Equiv.swap 0 2) = u*v*u := by
    dsimp [u,v];simp only [← map_mul];congr 1;decide
  rw [← ordinary_product F H,he]
  change (u*v*u) (f _) = f _
  rw [← Module.End.mul_apply, mul_assoc _ u f,hu, mul_assoc,hv,hu]

private def layout (n : ℕ) : (Fin 2 × Fin 2) ⊕ (Fin n × Fin 2) ≃ Fin (2+n) × Fin 2 :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))

private theorem spectator_layout (d : ℕ) :
    extend (layout 1) (Transfer.clasp (Transfer.tensorAction (Fin 2 × Fin 2) (Fin d))) = spectator := by
  apply projector_extend <;> decide

private theorem first_two_layout (d : ℕ) :
    extend (layout 2) (Transfer.clasp (Transfer.tensorAction (Fin 2 × Fin 2) (Fin d))) =
      localClasp d 2 2 := by
  rw [FourLocalSlots.local_is_projector]
  apply projector_extend <;> decide

private theorem thin_product {d : ℕ} (p : Perm (Fin 2 × Fin 2))
    (u : (Pos → Fin d) → ℂ) (H : Bend.Word d 2 → ℂ) :
    act d 2 (liftPerm (layout 2) p) (product u H) =
      product (Transfer.tensorAction Pos (Fin d) (liftPerm (layout 1) p) u) H := by
  have hi : ∀ (p : Perm (Fin 2 × Fin 2)) (a : Pos),
      liftPerm (layout 2) p (a.1.castSucc,a.2) =
        ((liftPerm (layout 1) p a).1.castSucc, (liftPerm (layout 1) p a).2) := by decide
  have hj : ∀ (p : Perm (Fin 2 × Fin 2)) (i : Fin 2),
      liftPerm (layout 2) p (3,i)=(3,i) := by decide
  funext w
  simp only [product,act,Transfer.tensorAction,MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.coe_mk,
    AddHom.coe_mk,Function.comp_apply,hi,hj]
  rfl

/-- The actual fine clasp on the first four thin slots acts only on the
ordinary tensor and agrees with the spectator projector in the cut. -/
theorem spectator_product {d : ℕ} (u : (Pos → Fin d) → ℂ) (H : Bend.Word d 2 → ℂ) :
    localClasp d 2 2 (product u H) = product (spectator u) H := by
  rw [← first_two_layout,← spectator_layout]
  simp only [extend_clasp]
  funext w
  simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply,
    Rat.smul_def,smul_eq_mul,Finset.sum_apply,Fintype.card_perm,MonoidHom.comp_apply]
  change (↑(((Fintype.card (Fin 2 × Fin 2)).factorial : ℚ)⁻¹) : ℂ) *
      ∑ p : Perm (Fin 2 × Fin 2), (act d 2 (liftPerm (layout 2) p) (product u H)) w = _
  simp only [thin_product,product,Pi.smul_apply,Rat.smul_def,smul_eq_mul,
    Finset.sum_apply,← Finset.sum_mul,mul_assoc]

end
end BlockPermanents.FourFootAverage
