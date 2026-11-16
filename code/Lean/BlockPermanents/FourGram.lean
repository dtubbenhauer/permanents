import BlockPermanents.FourTarget
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # The marked evaluation only depends on the atom Gram matrix

Changing the orthonormal coordinates for the marked support can change the
ambient word space. Every permutation product occurring in Q is transported
through the same rational group algebra of thin strands. -/
namespace BlockPermanents.FourGram
open FourTarget TransferBlocks Closures
open scoped BigOperators
noncomputable section

abbrev U (k : ℕ) := MonoidAlgebra ℚ (Wire k)
def basisOp (k : ℕ) := MonoidAlgebra.of ℚ (Wire k)
def rep (d k : ℕ) : U k →ₐ[ℚ] Op d k := MonoidAlgebra.lift ℚ _ _ (act d k)
local instance (k n : ℕ) : Fintype (FourTarget.group k n) := Fintype.ofFinite _

def formalQ (k : ℕ) : U k :=
  let ρ := (basisOp k).comp (wires k)
  let A n := Transfer.clasp ((basisOp k).comp (FourTarget.group k n).subtype)
  let u := ρ swap12
  let v := ρ swap23
  let X₃ := (((3*k).factorial : ℚ)/k.factorial^3) • A 3 - (6:ℚ) • triple u v
  let X₄ := (((4*k).factorial : ℚ)/k.factorial^4) • Transfer.clasp (basisOp k) -
    (24:ℚ) • Transfer.clasp ρ
  fourOperator ((k+k).choose k) u v (ρ swap34) (ρ swap14) (A 2) X₃ X₄

theorem realize (d k : ℕ) : rep d k (formalQ k) = Q d k := by
  change (MonoidAlgebra.lift ℚ _ _ (act d k)) (formalQ k) = Q d k
  simp only [formalQ,Q,fourOperator,corrected,movedDifference,pair,triple,
    X₃,X₄,fineClasp,packetClaspOp,localClasp,Transfer.clasp,packets,
    map_one,map_add,map_sub,map_smul,map_mul,map_sum,MonoidHom.comp_apply,
    basisOp,MonoidAlgebra.lift_of]

/-- An individual permutation on all 4k slots has the same closure after
a Gram-preserving change of coordinates, even for a mixed pair of inputs. -/
theorem wire_closure {k d e : ℕ} (p : Wire k)
    (a b : Fin 4 → Fin k → Fin d → ℂ) (c f : Fin 4 → Fin k → Fin e → ℂ)
    (h : crossGram (Function.uncurry a) (Function.uncurry b) =
      crossGram (Function.uncurry c) (Function.uncurry f)) :
    bracket (flatPackets a) (act d k p (flatPackets b)) =
      bracket (flatPackets c) (act e k p (flatPackets f)) := by
  classical
  have term (σ τ : Fin 4 → Equiv.Perm (Fin k)) :
      bracket (fun w => pureWord (Function.uncurry a) (w ∘ (withinPackets σ).symm))
        (fun w => pureWord (Function.uncurry b) ((w ∘ p) ∘ (withinPackets τ).symm)) =
      bracket (fun w => pureWord (Function.uncurry c) (w ∘ (withinPackets σ).symm))
        (fun w => pureWord (Function.uncurry f) ((w ∘ p) ∘ (withinPackets τ).symm)) := by
    have eqw {D} (x : Slot k → D → ℂ) (w : Slot k → D) :
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
  have hx {D} (x : Fin 4 → Fin k → D → ℂ) : flatPackets x =
      fun w => packetScale (Fin k) ^ Fintype.card (Fin 4) * ∑ σ : Fin 4 → Equiv.Perm (Fin k),
        pureWord (Function.uncurry x) (w ∘ (withinPackets σ).symm) :=
    funext (flatPackets_expand x)
  rw [hx a,hx b,hx c,hx f]
  simp only [bracket_scale, bracket_sum_left,bracket_sum_right,term]

theorem gram_invariant {k d e : ℕ} (a : Fin 4 → Fin k → Fin d → ℂ) (b : Fin 4 → Fin k → Fin e → ℂ)
    (h : crossGram (Function.uncurry a) (Function.uncurry a) =
      crossGram (Function.uncurry b) (Function.uncurry b)) :
    bracket (flatPackets a) (Q d k (flatPackets a)) = bracket (flatPackets b) (Q e k (flatPackets b)) := by
  suffices aux : ∀ u : U k, bracket (flatPackets a) (rep d k u (flatPackets a)) =
      bracket (flatPackets b) (rep e k u (flatPackets b)) by
    simpa only [realize] using aux (formalQ k)
  intro u
  simp only [rep,MonoidAlgebra.lift_apply,Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,
    bracket,Finset.sum_apply,Pi.smul_apply,Rat.smul_def,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s := (Finset.univ : Finset (Slot k → Fin e)))]
  apply Finset.sum_congr rfl
  intro p _
  have hp := wire_closure p a a b b h
  unfold bracket at hp
  simpa only [mul_left_comm _ ((u p:ℚ):ℂ), ← Finset.mul_sum] using
    congrArg (fun z : ℂ => ((u p:ℚ):ℂ)*z) hp

end
end BlockPermanents.FourGram
