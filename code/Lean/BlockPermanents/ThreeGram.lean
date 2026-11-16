import BlockPermanents.ThreeThin
import BlockPermanents.ThreeAverageClosure

/-! # Gram transport and permanent closure of the corrected three-packet representative -/
namespace BlockPermanents.ThreeGram
open Equiv Bend Closures ThreeGeneralOpen ThreeMarkedAverage TransferBlocks ThreeThin
open scoped BigOperators Matrix
noncomputable section

def formalQ (k : ℕ) : ThreeThin.A k :=
  let u := base k (liftPacket k firstSwap)
  let t := base k (liftPacket k lastSwap)
  let p := ThreeThin.front k
  let q := (u*t*u)*p*(u*t*u)
  let f := pair u
  let g := pair t
  let a : ℚ := (k+k).choose k
  let b : ℚ := (k+k+k).choose (k+k)
  a • (b • ThreeThin.all k) - (6:ℚ) • triple u t +
    a • ((2:ℚ) • (f*q*f) - p*g*f - f*g*p)

theorem realize (d k : ℕ) : realization d k (formalQ k) = original d k := by
  have basis (x) : realization d k (base k x) = permMat d k x := MonoidAlgebra.lift_of ..
  have shift := shifted d k
  dsimp only at shift
  simp only [formalQ,original,pair,triple,map_add,map_sub,map_one,map_smul,map_mul,
    basis,matrix_packet,ThreeMarkedAverage.front,ThreeMarkedAverage.back,matrix_first,matrix_all,shift,
    Rat.smul_def,Rat.cast_natCast,Rat.cast_ofNat]
  ext i j
  simp [Matrix.smul_apply,Rat.smul_def]

theorem flat_as {d k} (w : ThreeWords d k) : flat d k w = joinAll d k w ∘ slots k :=
  funext fun ⟨a,j⟩ => (join_index w a j).symm

theorem thin_closure {d k : ℕ} (p : Perm (L k)) (z : (Fin 3×Fin k → Fin d) → ℂ) :
    quadratic (permMat d k p) (z ∘ flat d k) =
      bracket z (fun w => z (w ∘ (slots k).symm.permCongr p)) := by
  have act (w : ThreeWords d k) : (permMat d k p).mulVec (z ∘ flat d k) w =
      z (flat d k (warp p⁻¹ w)) := by
    have he (b) : w=warp p b ↔ b=warp p⁻¹ w := by
      constructor <;> rintro rfl <;> simp [←warp_mul,warp_one]
    simp [permMat,Matrix.mulVec,dotProduct,ite_mul,he]
  have wf (w : ThreeWords d k) : flat d k (warp p⁻¹ w) =
      flat d k w ∘ (slots k).symm.permCongr p := by
    simp [flat_as,warp,Equiv.permCongr_def,Function.comp_def];rfl
  rw [Bridges.quadratic_bracket]
  unfold bracket
  simp_rw [act,wf]
  exact (flat d k).sum_comp (fun w => star (z w)*z (w ∘ (slots k).symm.permCongr p))

theorem wire_closure {k d e : ℕ} (p : Equiv.Perm (Fin 3×Fin k))
    (a b : Fin 3 → Fin k → Fin d → ℂ) (c f : Fin 3 → Fin k → Fin e → ℂ)
    (h : crossGram (Function.uncurry a) (Function.uncurry b) =
      crossGram (Function.uncurry c) (Function.uncurry f)) :
    bracket (flatPackets a) (fun w => flatPackets b (w ∘ p)) =
      bracket (flatPackets c) (fun w => flatPackets f (w ∘ p)) := by
  classical
  have term (σ τ : Fin 3 → Equiv.Perm (Fin k)) :
      bracket (fun w => pureWord (Function.uncurry a) (w ∘ (withinPackets σ).symm))
        (fun w => pureWord (Function.uncurry b) ((w ∘ p) ∘ (withinPackets τ).symm)) =
      bracket (fun w => pureWord (Function.uncurry c) (w ∘ (withinPackets σ).symm))
        (fun w => pureWord (Function.uncurry f) ((w ∘ p) ∘ (withinPackets τ).symm)) := by
    have eqw {D} (x : Fin 3×Fin k → D → ℂ) (w : Fin 3×Fin k → D) :
        pureWord x ((w ∘ p) ∘ (withinPackets τ).symm) =
          pureWord (x ∘ ((withinPackets τ)*p.symm)) w :=
      pure_reindex x ((withinPackets τ)*p.symm) w
    rw [show (fun w => pureWord (Function.uncurry b) ((w ∘ p) ∘ (withinPackets τ).symm)) = _ from
      funext (eqw (Function.uncurry b)), show (fun w => pureWord (Function.uncurry f) ((w ∘ p) ∘ (withinPackets τ).symm)) = _ from
      funext (eqw (Function.uncurry f))]
    simp only [pure_reindex,bracket_pureWord]
    change (∏ i, bracket ((Function.uncurry a) ((withinPackets σ) i))
      ((Function.uncurry b) (((withinPackets τ)*p.symm) i))) = _
    apply Finset.prod_congr rfl
    intro i _
    exact congrFun (congrFun h ((withinPackets σ) i)) (((withinPackets τ)*p.symm) i)
  change bracket (flatPackets a) (fun w => flatPackets b (w ∘ p)) =
    bracket (flatPackets c) (fun w => flatPackets f (w ∘ p))
  have hx {D} (x : Fin 3 → Fin k → D → ℂ) : flatPackets x =
      fun w => packetScale (Fin k) ^ Fintype.card (Fin 3) * ∑ σ : Fin 3 → Equiv.Perm (Fin k),
        pureWord (Function.uncurry x) (w ∘ (withinPackets σ).symm) :=
    funext (flatPackets_expand x)
  rw [hx a,hx b,hx c,hx f]
  simp only [bracket_scale, bracket_sum_left,bracket_sum_right,term]

private def evaluation {I : Type*} [Fintype I] (v : I → ℂ) : Matrix I I ℂ →ₗ[ℚ] ℂ where
  toFun Z := quadratic Z v
  map_add' _ _ := by simp [quadratic,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' r Z := by
    simp [quadratic,Matrix.smul_apply,Rat.smul_def,Finset.mul_sum,mul_assoc,mul_left_comm]

theorem gram_invariant {k d e : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) (y : Fin 3 → Fin k → Fin e → ℂ)
    (h : crossGram (Function.uncurry x) (Function.uncurry x) =
      crossGram (Function.uncurry y) (Function.uncurry y)) :
    quadratic (original d k) (data x) = quadratic (original e k) (data y) := by
  suffices aux : ∀ u : ThreeThin.A k,
      evaluation (data x) (realization d k u) = evaluation (data y) (realization e k u) by
    simpa only [realize] using aux (formalQ k)
  intro u
  simp only [realization,MonoidAlgebra.lift_apply,Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  change quadratic _ (flatPackets x ∘ flat d k) = quadratic _ (flatPackets y ∘ flat e k)
  rw [thin_closure,thin_closure]
  exact wire_closure _ x x y y h

theorem fine_eval {d k : ℕ} (z : (Fin 3×Fin k → Fin d) → ℂ) :
    quadratic (allFine d k) (z ∘ flat d k) = bracket z (clasp z) := by
  let g := fun w : K d ((k+k)+k) => z (w ∘ slots k)
  have eqz : z ∘ flat d k = g ∘ joinAll d k := funext (fun w => congrArg z (flat_as w))
  rw [eqz]
  change quadratic (fun i j => symClasp d ((k+k)+k) (joinAll d k i) (joinAll d k j)) _ = _
  rw [Bridges.quadratic_reindex,Bridges.quadratic_bracket,Bridges.symClasp_action]
  exact Bridges.bracket_transport (slots k) z

private theorem weight (k : ℕ) : ((k+k).choose k:ℂ) * ((k+k+k).choose (k+k):ℂ) =
    fineWeight (Fin 3) (Fin k) := by
  simp only [fineWeight,Fintype.card_fin]
  apply (eq_div_iff (pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero k))).mpr
  have h₁ : ((k+k).choose k:ℂ) * k.factorial * k.factorial = (k+k).factorial := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k k
  have h₂ : ((k+k+k).choose (k+k):ℂ) * (k+k).factorial * k.factorial = (k+k+k).factorial := by
    have hh := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (k+k) k)
    rw [Nat.add_sub_cancel_left] at hh
    exact_mod_cast hh
  rw [show 3*k=k+k+k by omega,←h₂,←h₁]
  ring

theorem target_gap {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :
    quadratic (target d k) (data x) =
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
        (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent := by
  let z := flatPackets x
  have release : quadratic (target d k) (data x) =
      fineWeight (Fin 3) (Fin k) * bracket z (clasp z) - 6*bracket z (packetClasp z) := by
    have ev {I : Type} [Fintype I] (A : Matrix I I ℂ) (v:I→ℂ) (c:ℂ) :
        quadratic (c • A) v = c * quadratic A v := by
      simp [quadratic,Matrix.smul_apply,Finset.mul_sum,mul_assoc,mul_left_comm]
    have sub {I : Type} [Fintype I] (A B : Matrix I I ℂ) (v:I→ℂ) :
        quadratic (A-B) v=quadratic A v-quadratic B v := by
      simp [quadratic,mul_sub,sub_mul,Finset.sum_sub_distrib]
    have six (A : Matrix (ThreeWords d k) (ThreeWords d k) ℂ) : (6:ℚ) • A = (6:ℂ) • A := by
      ext i j; simp [Matrix.smul_apply,Rat.smul_def]
    change quadratic (target d k) (z ∘ flat d k) = _
    simp only [target,six,sub,ev,←mul_assoc,weight,fine_eval,whole_closure]
  have entries : (fun i j => (crossGram (x i) (x j)).permanent) =
      crossGram (fun i => packet (x i)) (fun i => packet (x i)) := by
    funext i j; exact (packet_gram (x i) (x j)).symm
  rw [←entries,←defect_closure,release]
  unfold defect
  rw [bracket_scaled_sub]
  simp [z,show (3:ℕ).factorial=6 by decide]

end
end BlockPermanents.ThreeGram
