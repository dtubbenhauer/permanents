import BlockPermanents.ThreeMarkedAverage
import BlockPermanents.ThreeCanonicalGlue
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # The three-packet clasp operator in the common algebra of thin permutations -/
namespace BlockPermanents.ThreeThin
open Equiv Bend Closures ThreeGeneralOpen ThreeMarkedAverage TransferBlocks
open scoped BigOperators Matrix
noncomputable section

abbrev L (k : ℕ) := Fin ((k+k)+k)
abbrev A (k : ℕ) := MonoidAlgebra ℚ (Perm (L k))
def slots (k : ℕ) : Fin 3 × Fin k ≃ L k := finProdFinEquiv.trans (finCongr (by omega))
def joinAll (d k : ℕ) : ThreeWords d k ≃ K d ((k+k)+k) :=
  (join3 d k).trans (Fin.appendEquiv (k+k) k)

def liftPacket (k : ℕ) (p : G) : Perm (L k) := (slots k).permCongr (p.prodCongr (Equiv.refl _))

def warp {d k : ℕ} (p : Perm (L k)) (w : ThreeWords d k) : ThreeWords d k :=
  (joinAll d k).symm ((joinAll d k w) ∘ p.symm)

theorem warp_mul {d k : ℕ} (p q : Perm (L k)) (w : ThreeWords d k) : warp (p*q) w=warp p (warp q w) := by
  simp [warp,Function.comp_def]; rfl

theorem warp_one {d k : ℕ} (w : ThreeWords d k) : warp (1 : Perm (L k)) w=w := by simp [warp]

def permMat (d k : ℕ) : Perm (L k) →* Matrix (ThreeWords d k) (ThreeWords d k) ℂ where
  toFun p := fun i j => if i = warp p j then 1 else 0
  map_one' := by ext i j; simp [warp_one,Matrix.one_apply]
  map_mul' p q := by ext i j; simp [Matrix.mul_apply,mul_ite,warp_mul]

def realization (d k : ℕ) := MonoidAlgebra.lift ℚ _ _ (permMat d k)

def wave {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) (w : ThreeWords d k) : ℂ :=
  ∏i, packet (x i) (tuple _ w i)

theorem join_index {d k : ℕ} (w : ThreeWords d k) (i : Fin 3) (j : Fin k) :
    joinAll d k w (slots k (i,j)) = tuple _ w i j := by
  have h₀ : slots k (0,j) = Fin.castAdd k (Fin.castAdd k j) := by
    apply Fin.ext; simp [slots,finProdFinEquiv,finCongr]
  have h₁ : slots k (1,j) = Fin.castAdd k (Fin.natAdd k j) := by
    apply Fin.ext; simp [slots,finProdFinEquiv,finCongr]
  have h₂ : slots k (2,j) = Fin.natAdd (k+k) j := by
    apply Fin.ext; simp [slots,finProdFinEquiv,finCongr];omega
  change Fin.append (Fin.append w.1.1 w.1.2) w.2 _ = _
  fin_cases i
  · change Fin.append _ _ ((slots k) (0,j)) = _
    rw [h₀,Fin.append_left,Fin.append_left];rfl
  · change Fin.append _ _ ((slots k) (1,j)) = _
    rw [h₁,Fin.append_left,Fin.append_right];rfl
  · change Fin.append _ _ ((slots k) (2,j)) = _
    rw [h₂,Fin.append_right];rfl

theorem lift_warp {d k : ℕ} (p : G) (w : ThreeWords d k) :
    warp (liftPacket k p) w = reorder p w := by
  apply (joinAll d k).injective; funext i
  obtain ⟨⟨a,j⟩,rfl⟩ := (slots k).surjective i
  have h : (liftPacket k p).symm (slots k (a,j)) = slots k (p.symm a,j) := by simp [liftPacket,Equiv.permCongr_def]
  unfold warp
  rw [apply_symm_apply,Function.comp_apply,h,join_index,join_index]
  simp only [reorder,apply_symm_apply];rfl

theorem matrix_packet (d k : ℕ) (p : G) : permMat d k (liftPacket k p) = rep (K d k) p := by
  ext i j;simp [permMat,rep,lift_warp]

def base (k : ℕ) := MonoidAlgebra.of ℚ (Perm (L k))
def all (k : ℕ) : A k := Transfer.clasp (base k)

theorem matrix_all (d k : ℕ) : realization d k (all k) = allFine d k := by
  ext i j
  simp only [realization,all,Transfer.clasp,map_smul,map_sum,base,MonoidAlgebra.lift_of,
    Matrix.smul_apply,Matrix.sum_apply,Fintype.card_perm,Fintype.card_fin,Rat.smul_def,Rat.cast_inv,
    Rat.cast_natCast,smul_eq_mul]
  change _ * (∑ p : Perm (L k), if i=warp p j then (1:ℂ) else 0) = _
  change _ = _ * (∑ p : Perm (L k), if joinAll d k i = joinAll d k j ∘ p then (1:ℂ) else 0)
  congr 1
  apply Fintype.sum_equiv (Equiv.inv _);intro p
  simp only [warp,Equiv.apply_eq_iff_eq_symm_apply,Equiv.inv_apply];rfl

def frontLift (k : ℕ) : Perm (Fin (k+k)) →* Perm (L k) where
  toFun p := permJoin p 1
  map_one' := by ext i;simp [permJoin]
  map_mul' p q := by ext i;simp [permJoin,Perm.mul_apply]

def front (k : ℕ) : A k := Transfer.clasp ((base k).comp (frontLift k))

theorem front_warp {d k : ℕ} (p : Perm (Fin (k+k))) (w : ThreeWords d k) :
    warp (frontLift k p) w = ((Bridges.joinWords d k).symm (Fin.append w.1.1 w.1.2 ∘ p.symm),w.2) := by
  apply (joinAll d k).injective
  unfold warp; rw [apply_symm_apply]
  change Fin.append (Fin.append w.1.1 w.1.2) w.2 ∘ (permJoin p 1).symm =
    Fin.append ((Bridges.joinWords d k) ((Bridges.joinWords d k).symm _)) w.2
  rw [apply_symm_apply]
  exact (append_permute _ _ p.symm (1 : Perm (Fin k))).symm

theorem matrix_first (d k : ℕ) : realization d k (front k) = firstFine d k := by
  ext i j
  simp only [realization,front,Transfer.clasp,map_smul,map_sum,base,MonoidHom.comp_apply,MonoidAlgebra.lift_of,
    Matrix.smul_apply,Matrix.sum_apply,Fintype.card_perm,Fintype.card_fin,Rat.smul_def,Rat.cast_inv,
    Rat.cast_natCast,smul_eq_mul]
  change _ * (∑ p, if i=warp (frontLift k p) j then (1:ℂ) else 0) = _
  simp only [front_warp,Prod.ext_iff]
  by_cases hh : i.2=j.2
  · simp only [hh,and_true,firstFine,ThreeTransfer.upright,if_true,totalClasp,symClasp]
    congr 1
    apply Fintype.sum_equiv (Equiv.inv _);intro p
    congr 1
    rw [← Prod.ext_iff];exact propext ((Bridges.joinWords d k).apply_eq_iff_eq_symm_apply.symm)
  · simp [firstFine,ThreeTransfer.upright,hh]

end
end BlockPermanents.ThreeThin
