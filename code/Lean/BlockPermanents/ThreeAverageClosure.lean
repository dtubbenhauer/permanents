import BlockPermanents.ThreeMarkedAverage

namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen ThreeTransfer TransferBlocks Equiv
open scoped Matrix BigOperators
noncomputable section

def flat (d k : ℕ) : ThreeWords d k ≃ (Fin 3×Fin k → Fin d) :=
  (tuple _).trans (Equiv.curry _ _ _).symm

def data {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) (w : ThreeWords d k) := Closures.flatPackets x (flat d k w)

def target (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ :=
  ((k+k).choose k : ℂ) • (((k+k+k).choose (k+k):ℂ) • allFine d k) -
    (6:ℚ) • triple (swapFront d k) ThreeTransfer.cross

theorem whole_closure {d k : ℕ} (z : (Fin 3×Fin k → Fin d) → ℂ) :
    quadratic (triple (swapFront d k) ThreeTransfer.cross) (z ∘ flat d k) =
      Closures.bracket z (Closures.packetClasp z) := by
  let A := triple (swapFront d k) (ThreeTransfer.cross : Matrix (ThreeWords d k) (ThreeWords d k) ℂ)
  let y := z ∘ flat d k
  let ρ := rep (K d k)
  have action (p : G) (x : ThreeWords d k) : (ρ p).mulVec y x = y (reorder p⁻¹ x) := by
    have he (b) : x=reorder p b ↔ b=reorder p⁻¹ x := by
      constructor <;> rintro rfl <;> simp [←reorder_mul]
    simp [ρ,rep,Matrix.mulVec,dotProduct,ite_mul,he]
  have sum_action (x : ThreeWords d k) : (∑ p, ρ p).mulVec y x = ∑ p, y (reorder p⁻¹ x) := by
    simp only [Matrix.mulVec,dotProduct,Matrix.sum_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => action p x)
  have hA (x : ThreeWords d k) : A.mulVec y x = Closures.packetClasp z (flat d k x) := by
    rw [show A=Transfer.clasp ρ from (whole_clasp d k).symm]
    simp only [Transfer.clasp,Matrix.smul_mulVec_assoc,Pi.smul_apply,sum_action,
      Finset.sum_apply,action,Rat.smul_def,smul_eq_mul,Rat.cast_inv,Rat.cast_natCast,Fintype.card_perm,
      Closures.packetClasp,Closures.clasp,Closures.sumSlots,Fintype.card_fin]
    congr 1
    let f := fun p : G => z (Function.uncurry ((tuple _ x) ∘ p))
    have eqy (p : G) : y (reorder p⁻¹ x) = f p := by
      change z (Function.uncurry ((tuple _ ) ((tuple _).symm _))) = _
      rw [Equiv.apply_symm_apply]; rfl
    simp_rw [eqy]
    change (∑ p : G, f p) = ∑ p : G, f p.symm
    exact (Equiv.sum_comp (Equiv.inv G) f).symm
  change (∑ i, ∑ j, star (y i) * A i j * y j) = _
  simp only [mul_assoc,← Finset.mul_sum]
  change (∑ i, star (y i) * A.mulVec y i) = _
  simp_rw [hA];exact (flat d k).sum_comp (fun w => star (z w) * Closures.packetClasp z w)

/-- The omitted piece of the corrected representative has zero simultaneous
packet average. No symmetry or product hypothesis on the boundary is used. -/
theorem average_original (d k : ℕ) : Transfer.bracket (rep (K d k)) (original d k) =
    Transfer.bracket (rep (K d k)) (target d k) := by
  let u := swapFront d k
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  let p := firstFine d k
  let a : ℚ := (k+k).choose k
  have he : original d k = target d k + a • movedDifference u t p := by
    unfold original target movedDifference
    have h := shifted d k
    dsimp only at h
    rw [← h]
    have h2 (A : Matrix (ThreeWords d k) (ThreeWords d k) ℂ) : (2:ℚ) • A = (2:ℂ) • A := by
      ext i j;simp [Matrix.smul_apply,Rat.smul_def]
    rw [h2]
    simp only [u,t,p,mul_assoc,Rat.smul_def,add_assoc]
    rfl
  rw [he,map_add,map_smul,average_correction,smul_zero,add_zero]

theorem conjugate_eval {T : Type*} [Fintype T] [DecidableEq T] (p : G)
    (Z : Matrix ((T×T)×T) ((T×T)×T) ℂ) (v : ((T×T)×T) → ℂ) :
    quadratic (rep T p * Z * rep T p⁻¹) v = quadratic Z (fun w => v (reorder p w)) := by
  let e : ((T×T)×T) ≃ ((T×T)×T) :=
    ⟨reorder p,reorder p⁻¹,fun w => by simp [←reorder_mul],fun w => by simp [←reorder_mul]⟩
  simp only [quadratic,rep_right,rep_left]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl;intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl;intro j _
  simp [e,←reorder_mul]

private def qlin {T : Type*} [Fintype T] (v : T→ℂ) : Matrix T T ℂ →ₗ[ℚ] ℂ where
  toFun Z := quadratic Z v
  map_add' _ _ := by simp [quadratic,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' r Z := by
    simp [quadratic,Matrix.smul_apply,Rat.smul_def,Finset.mul_sum,mul_assoc,mul_left_comm]

theorem average_eval {T : Type*} [Fintype T] [DecidableEq T] (Z : Matrix ((T×T)×T) ((T×T)×T) ℂ)
    (v : ((T×T)×T) → ℂ) :
    quadratic (Transfer.bracket (rep T) Z) v = (6:ℂ)⁻¹ * ∑ p : G, quadratic Z (fun w => v (reorder p w)) := by
  change qlin v _ = _
  simp only [Transfer.bracket,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    Fintype.card_perm,Fintype.card_fin,Rat.smul_def,Rat.cast_inv,Rat.cast_natCast,smul_eq_mul]
  change ((↑(Nat.factorial 3):ℂ)⁻¹) * ∑ p, quadratic (rep T p * Z * rep T p⁻¹) v = _
  rw [show (3:ℕ).factorial=6 by decide]
  simp only [Nat.cast_ofNat,conjugate_eval]

theorem data_reorder {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) (p : G) (w : ThreeWords d k) :
    data x (reorder p w) = data (x ∘ p) w := by
  change (∏ i, Closures.packet (x i) ((tuple _ (reorder p w)) i)) =
    ∏ i, Closures.packet (x (p i)) (tuple _ w i)
  simp only [reorder,Equiv.apply_symm_apply,Function.comp_apply]
  exact (Equiv.prod_comp p (fun i => Closures.packet (x i) ((tuple _ w) (p.symm i)))).symm.trans (by simp)

theorem sum_original {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :
    ∑ p : G, quadratic (original d k) (data (x ∘ p)) =
      ∑ p : G, quadratic (target d k) (data (x ∘ p)) := by
  have h := congrArg (fun A => quadratic A (data x)) (average_original d k)
  simp only [average_eval,data_reorder] at h
  exact mul_left_cancel₀ (by norm_num : (6:ℂ)⁻¹≠0) h

end
end BlockPermanents.ThreeMarkedAverage
