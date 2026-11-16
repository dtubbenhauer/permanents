import BlockPermanents.FourWireCutDefs
import BlockPermanents.FourRouteNorm
import BlockPermanents.FourFullValues

namespace BlockPermanents.FourWireCut
open Bend Closures FourRoutes FourCapOrbit FourCapValues FourFullValues FourLastCaps FourTarget Equiv
open scoped BigOperators Matrix
noncomputable section

def ordinaryWord {D : Type*} (u : Port → D) (t : D) : Pos → D :=
  (fun l : Letter => l.elim t u) ∘ order 0 1

def cut {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) (u : Port → Fin d) (b : Fin d) : ℂ :=
  ∑ t, U (ordinaryWord u t) * star (H ![b,t])

def closedCut {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) (v : Word d 4) : ℂ :=
  ∑ b, cut U H (insertAt anchor v b) b

private theorem same_order (r : Fin 3) : order r 1 = order 0 1 := by
  ext ⟨i,j⟩;fin_cases r <;> fin_cases i <;> fin_cases j <;> rfl

theorem cut_merged {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Symmetric H) : cut (merged r F) H = raw r F H := by
  funext u b
  rw [raw_formula r F H hH]
  have he (p : Perm (A r)) (t : Fin d) :
      ordinaryWord u t ∘ (order r p).trans (order r 1).symm =
      (fun l : Letter => l.elim t u) ∘ order r p := by
    funext j
    change ((order 0 1) ((order r 1).symm ((order r p) j))).elim t u = _
    rw [← same_order r, Equiv.apply_symm_apply]; rfl
  simp only [cut,merged,he,mul_assoc,Finset.sum_mul,← Finset.mul_sum]
  congr 1;exact Finset.sum_comm

theorem closed_merged {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Symmetric H) : closedCut (merged r F) H = full r F H := by
  funext v
  simp only [closedCut,cut_merged _ _ _ hH,join_cut r F H hH]

private def combine {D : Type*} (a : Pos → D) (h : Fin 2 → D) : Slot 2 → D :=
  fun ij => ![(fun j => a (0,j)),(fun j => a (1,j)),(fun j => a (2,j)),h] ij.1 ij.2

private theorem combine_ord {D : Type*} (a : Pos → D) (h : Fin 2 → D) :
    (fun i : Pos => combine a h (i.1.castSucc,i.2)) = a := by
  funext ⟨i,j⟩; fin_cases i <;> rfl
private theorem combine_mark {D : Type*} (a : Pos → D) (h : Fin 2 → D) :
    (fun j => combine a h (3,j)) = h := rfl

private def properCoords (D : Type*) :
    (((Port → D) × D) × (D × D)) ≃ (Slot 2 → D) where
  toFun q := combine (ordinaryWord q.1.1 q.2.1) ![q.1.2,q.2.2]
  invFun w := (((fun p => let i := (order 0 1).symm (some p)
                          w (i.1.castSucc,i.2)), w (3,0)), (w (2,1),w (3,1)))
  left_inv := by
    rintro ⟨⟨u,b⟩,a,c⟩
    apply Prod.ext
    · apply Prod.ext
      · funext j; cases j with
        | none => rfl
        | some j => fin_cases j <;> rfl
      · rfl
    · rfl
  right_inv w := by funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl

private theorem single_action {D : Type*} (q : (((Port → D) × D) × (D × D))) :
    (properCoords D q) ∘ single = properCoords D (q.1,q.2.swap) := by
  funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl

private def fullCoords (D : Type*) :
    ((Fin 4 → D) × ((Fin 2 → D) × (Fin 2 → D))) ≃ (Slot 2 → D) where
  toFun q := combine (ordinaryWord (insertAt anchor q.1 (q.2.1 0)) (q.2.1 1)) q.2.2
  invFun w := ((fun i => let p := (order 0 1).symm (some (swap none anchor (some i)))
                         w (p.1.castSucc,p.2)), (fun j => w (2,j)), fun j => w (3,j))
  left_inv := by
    rintro ⟨v,a,b⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
  right_inv w := by funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl

private theorem double_action {D : Type*} (q : ((Fin 4 → D) × ((Fin 2 → D) × (Fin 2 → D)))) :
    (fullCoords D q) ∘ double = fullCoords D (q.1,q.2.swap) := by
  funext ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl

private theorem kernel_square {J T : Type*} [Fintype J] [Fintype T] (V H : J → T → ℂ) :
    (∑ j, ∑ a, ∑ b, star (V j a * H j b) * (V j b * H j a)) =
      ∑ j, (Complex.normSq (∑ a, V j a * star (H j a)) : ℂ) := by
  simp only [Complex.normSq_eq_conj_mul_self, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def,Complex.conj_conj]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem single_square {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) :
    (bracket (product U H) (act d 2 single (product U H))).re =
      rawEnergy Finset.univ (cut U H) := by
  let V := fun (q : (Port → Fin d) × Fin d) (a : Fin d) => U (ordinaryWord q.1 a)
  let Z := fun (q : (Port → Fin d) × Fin d) (a : Fin d) => H ![q.2,a]
  have h := kernel_square V Z
  have rec (q : (((Port → Fin d) × Fin d) × (Fin d × Fin d))) :
      product U H (properCoords _ q) = V q.1 q.2.1 * Z q.1 q.2.2 := by
    change U _ * H _ = _
    simp only [properCoords,Equiv.coe_fn_mk,combine_ord,combine_mark]
    rfl
  unfold bracket
  change (∑ w, star (product U H w) * product U H (w ∘ single)).re = _
  rw [← (properCoords (Fin d)).sum_comp]
  simp only [single_action,rec,Fintype.sum_prod_type,Prod.swap_prod_mk]
  simpa only [Fintype.sum_prod_type,Complex.re_sum,Complex.ofReal_re,cut,V,Z,rawEnergy]
    using congrArg Complex.re h

theorem double_square {d : ℕ} (U : (Pos → Fin d) → ℂ) (H : Word d 2 → ℂ) :
    (bracket (product U H) (act d 2 double (product U H))).re = energy (closedCut U H) := by
  let V := fun (v : Word d 4) (a : Word d 2) => U (ordinaryWord (insertAt anchor v (a 0)) (a 1))
  let Z := fun (_ : Word d 4) (a : Word d 2) => H a
  have h := kernel_square V Z
  have rec (q : Word d 4 × Word d 2 × Word d 2) :
      product U H (fullCoords _ q) = V q.1 q.2.1 * Z q.1 q.2.2 := by
    change U _ * H _ = _
    simp only [fullCoords,Equiv.coe_fn_mk,combine_ord,combine_mark]
    rfl
  have g (v : Word d 4) : (∑ a, V v a * star (Z v a)) = closedCut U H v := by
    let e := finTwoArrowEquiv (Fin d)
    rw [← e.symm.sum_comp,Fintype.sum_prod_type]
    rfl
  unfold bracket
  change (∑ w, star (product U H w) * product U H (w ∘ double)).re = _
  rw [← (fullCoords (Fin d)).sum_comp]
  simp only [double_action,rec,Fintype.sum_prod_type,Prod.swap_prod_mk]
  simpa only [g,Complex.re_sum,Complex.ofReal_re,energy] using congrArg Complex.re h

end
end BlockPermanents.FourWireCut
