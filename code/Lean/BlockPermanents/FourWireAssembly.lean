import BlockPermanents.FourOutputProjection
import BlockPermanents.FourRoutePositive
import BlockPermanents.FourWireAlgebra

/-! Evaluation of the seven fixed-mark terms on the common marked input. -/
namespace BlockPermanents.FourWireCut
open Bend Closures FourTarget FourCapOrbit FourCapValues FourFullValues FourRoutes
open scoped BigOperators
noncomputable section

abbrev Boundary (d : ℕ) := (Slot 2 → Fin d) → ℂ

def pair {d : ℕ} (u : Boundary d) : Boundary d →ₗ[ℚ] ℝ where
  toFun v := (bracket u v).re
  map_add' v w := by simp [bracket,mul_add,Finset.sum_add_distrib]
  map_smul' r v := by
    change (bracket u (r • v)).re = r • (bracket u v).re
    simp only [bracket,Pi.smul_apply,Rat.smul_def,smul_eq_mul,mul_left_comm _ (r:ℂ),
      ← Finset.mul_sum,Complex.mul_re,Complex.ratCast_re,Complex.ratCast_im,zero_mul,sub_zero]

def scalar {d : ℕ} (z : Boundary d) : Op d 2 →ₗ[ℚ] ℝ where
  toFun T := pair z (T z)
  map_add' A B := map_add _ _ _
  map_smul' r A := by
    change pair z (r • (A z)) = r • pair z (A z)
    exact map_smul (pair z) r (A z)

def AdjointableHere {d : ℕ} (A : Op d 2) : Prop :=
  ∀ u v : Boundary d, pair u (A v) = pair (A u) v

private theorem closed_difference {d : ℕ} (A B : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) :
    closedCut (A - (1/15:ℚ) • B) H =
      fun t => closedCut A H t - closedCut B H t/15 := by
  funext v
  simp only [closedCut,cut,Pi.sub_apply,Pi.smul_apply,Rat.smul_def,smul_eq_mul,
    sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
  norm_num; ring

private theorem product_difference {d : ℕ} (A B : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) :
    product A H - (1/15:ℚ) • product B H = product (A - (1/15:ℚ) • B) H := by
  funext w
  simp [product,Rat.smul_def,sub_mul,mul_assoc]

private theorem pair_diff {d : ℕ} (z y v : Boundary d) (c : ℚ) :
    pair (z - c • y) v = pair z v - c • pair y v := by
  change (bracket (z-c • y) v).re = _
  simp only [pair,LinearMap.coe_mk,AddHom.coe_mk,bracket,Pi.sub_apply,Pi.smul_apply,
    Rat.smul_def,smul_eq_mul,map_sub,map_mul,sub_mul,mul_assoc,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Complex.sub_re,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.ratCast_re,Complex.ratCast_im,neg_zero,zero_mul,sub_zero]

/-- This equality is valid whenever the four upright halves act as
the three active merges and the spectator projector on the given product. -/
theorem raw_cutForm {d : ℕ} (J E P R : Op d 2) (z : Boundary d)
    (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (hH : Symmetric H)
    (aJ : AdjointableHere J) (aE : AdjointableHere E) (aP : AdjointableHere P) (aR : AdjointableHere R)
    (u : J z = product (merged 0 F) H)
    (w : P (J z) = product (merged 1 F) H)
    (v : E z = product (merged 2 F) H)
    (x : R (J z) = product (spectator (merged 0 F)) H) :
    (bracket z (FourWireAlgebra.raw J E P R (act d 2 single) (act d 2 double) z)).re =
      cutForm F H := by
  let e := act d 2 single
  let t := act d 2 double
  let M := E - (1/15:ℚ) • (R*J)
  have m : M z = product (merged 2 F - (1/15:ℚ) • spectator (merged 0 F)) H := by
    change E z - (1/15:ℚ) • R (J z) = _
    rw [v,x,product_difference]
  have s1 : scalar z (J*e*J) = properEnergy 0 F H := by
    change pair z (J (e (J z))) = _
    rw [aJ,u,proper_eq_raw]
    exact (single_square _ _).trans (congrArg _ (cut_merged 0 F H hH))
  have s2 : scalar z (J*P*e*P*J) = properEnergy 1 F H := by
    change pair z (J (P (e (P (J z))))) = _
    rw [aJ,aP,w,proper_eq_raw]
    exact (single_square _ _).trans (congrArg _ (cut_merged 1 F H hH))
  have s3 : scalar z (E*e*E) = properEnergy 2 F H := by
    change pair z (E (e (E z))) = _
    rw [aE,v,proper_eq_raw]
    exact (single_square _ _).trans (congrArg _ (cut_merged 2 F H hH))
  have s4 : scalar z ((E - (1/15:ℚ) • (J*R))*t*M) =
      energy (fun i => full 2 F H i-clasp (full 0 F H) i/15) := by
    change pair z (E (t (M z)) - (1/15:ℚ) • J (R (t (M z)))) = _
    rw [map_sub,map_smul,aE,aJ,aR,← pair_diff]
    change pair (M z) (t (M z)) = _
    rw [m]
    exact (double_square _ _).trans (by rw [closed_difference,closed_spectator,
      closed_merged _ _ _ hH,closed_merged _ _ _ hH])
  have s5 : scalar z (J*P*t*P*J) = energy (full 1 F H) := by
    change pair z (J (P (t (P (J z))))) = _
    rw [aJ,aP,w]
    exact (double_square _ _).trans (congrArg _ (closed_merged 1 F H hH))
  have s6 : scalar z (J*t*J) = energy (full 0 F H) := by
    change pair z (J (t (J z))) = _
    rw [aJ,u]
    exact (double_square _ _).trans (congrArg _ (closed_merged 0 F H hH))
  have s7 : scalar z (J*R*t*R*J) = energy (clasp (full 0 F H)) := by
    change pair z (J (R (t (R (J z))))) = _
    rw [aJ,aR,x]
    exact (double_square _ _).trans (by rw [closed_spectator,closed_merged _ _ _ hH])
  change scalar z (FourWireAlgebra.raw J E P R e t) = _
  simp only [FourWireAlgebra.raw,map_add,map_sub,map_smul]
  change _ + _ + _ + (1350:ℚ) • scalar z ((E-(1/15:ℚ) • (J*R))*t*M) + _ - _ - _ = _
  rw [s1,s2,s3,s4,s5,s6,s7]
  norm_num [cutForm,Rat.smul_def]

end
end BlockPermanents.FourWireCut
