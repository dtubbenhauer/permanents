import BlockPermanents.RoutingReadout
import BlockPermanents.ForcedQuadratics

/-! # The forced-edge readout on genuine rational symmetric tensor packets -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {m n k : ℕ} {D S : Type*}

/-- Pullback of word coordinates by a wire permutation over ℚ. -/
def wordAction (S D : Type*) : Perm S →* Module.End ℚ ((S→D)→ℚ) where
  toFun p := {toFun := fun v w => v (w ∘ p), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl}
  map_one' := rfl
  map_mul' _ _ := rfl

def packetState (x : Fin m → (Fin k→D) → ℚ) (w : Slot m k → D) : ℚ :=
  ∏ i,x i (fun t => w (i,t))

def readState [Fintype S] [DecidableEq S] [Fintype D] (v h : (S→D)→ℚ) : Module.End ℚ ((S→D)→ℚ) →ₗ[ℚ] ℚ where
  toFun M := ∑ w,v w * M h w
  map_add' _ _ := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a M := by simp only [LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]; apply Finset.sum_congr rfl; intro w _;ring

private theorem pack_invariant (x : Fin m → (Fin k→D) → ℚ)
    (hx : ∀ i w (p : Perm (Fin k)), x i (w∘p)=x i w) (w : Slot m k→D) (g : Fin m → Perm (Fin k)) :
    packetState x (w ∘ within g) = packetState x w := by
  apply Finset.prod_congr rfl;intro i _;exact hx i (fun t => w (i,t)) (g i)

private theorem reflect_sum [Fintype S] [DecidableEq S] [Fintype D] (v h : (S→D)→ℚ) (p : Perm S) :
    (∑ w,v w * h (w ∘ p)) = ∑ w,v (w ∘ p.symm) * h w := by
  let e := p.symm.arrowCongr (Equiv.refl D)
  have hw (w : S→D) : e w ∘ p.symm = w := by funext i; simp [e]
  exact (show (∑ w,v w * h (w ∘ p)) = ∑ w,v (e w ∘ p.symm) * h (e w) by simp only [hw];rfl).trans
    (e.sum_comp (fun w => v (w ∘ p.symm) * h w))

private theorem internal_fix (x : Fin m → (Fin k→D) → ℚ)
    (hx : ∀ i w (p : Perm (Fin k)), x i (w∘p)=x i w) :
    internal (wordAction (Slot m k) D) (packetState x) = packetState x := by
  funext w
  have hi : (Fintype.card (Fin m → Perm (Fin k)):ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [internal,Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply,Finset.sum_apply,
    MonoidHom.comp_apply,wordAction,MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
    pack_invariant x hx,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ,inv_smul_smul₀ hi]

theorem read_compressed [Fintype D] (x y : Fin m → (Fin k→D) → ℚ)
    (hx : ∀ i w (p : Perm (Fin k)), x i (w∘p)=x i w)
    (hy : ∀ i w (p : Perm (Fin k)), y i (w∘p)=y i w) (p : Wire m k) :
    readState (packetState x) (packetState y) (compressed (wordAction (Slot m k) D) p) =
      ∑ w, packetState x w * packetState y (w∘p) := by
  let z := fun w : Slot m k→D => packetState y (w∘p)
  change (∑ w,packetState x w * internal (wordAction (Slot m k) D)
    (wordAction _ _ p (internal (wordAction _ _) (packetState y))) w) = _
  rw [internal_fix y hy]
  change (∑ w,packetState x w * internal (wordAction (Slot m k) D) z w) = ∑ w,packetState x w*z w
  have inv (g : Fin m → Perm (Fin k)) : (within g).symm = within (fun i => (g i).symm) := rfl
  have term (g : Fin m → Perm (Fin k)) : (∑ w,packetState x w * z (w ∘ within g)) = ∑ w,packetState x w*z w := by
    rw [reflect_sum];simp only [inv,pack_invariant x hx]
  simp only [internal,Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply,Finset.sum_apply,
    MonoidHom.comp_apply,wordAction,MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
    smul_eq_mul,mul_left_comm (packetState x _),← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [term,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_mul]

/-- The concrete two-letter quadratic packet readout uses one half-factorial
per packet. The coefficient polynomial is built from genuine constrained
permutation contractions on the actual product word states. -/
theorem quadratic_polynomial (x y : Fin (n+1) → Negative.Quad) (a : Fin (n+1)) (hn : 0<n) :
    let u := packetState (fun i => ForcedQuadratics.amplitude (x i))
    let v := packetState (fun i => ForcedQuadratics.amplitude (y i))
    readState u v (marked (wordAction (Slot (n+1) 2) Bool) a) =
      ∑ h ∈ Finset.range (n+1), ((n+1:ℚ)/(2*(n+1-h:ℕ))) *
        (WholeEdges.certificate (MarkedEdges.whole (m:=n+1) (k:=2))
          (fun p => ForcedRoutes.contraction u v p / 2^(n+1)) (MarkedEdges.ends a)).coeff h := by
  dsimp only
  rw [marked_polynomial _ _ (by decide : 0<2) hn]
  simp only [read_compressed _ _ (fun i => ForcedQuadratics.amplitude_symm (x i))
    (fun i => ForcedQuadratics.amplitude_symm (y i))]
  rfl

end
end BlockPermanents.RoutingFibres
