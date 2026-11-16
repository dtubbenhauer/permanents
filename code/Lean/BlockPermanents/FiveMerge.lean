import BlockPermanents.StraightCut
import BlockPermanents.PairBound

/-! # Two consecutive symmetric merges on atom packets (Section 8A) -/
namespace BlockPermanents.FiveMerge
open Bend Closures PairBound
open scoped BigOperators
noncomputable section

def joined {k d : ℕ} (h f : Fin k → Fin d → ℂ) : Fin (k+k) → Fin d → ℂ :=
  Sum.elim h f ∘ finSumFinEquiv.symm

def mergeScale (k : ℕ) : ℂ := StraightCut.c (Fin k) * StraightCut.c (Fin k) / StraightCut.c (Fin (k+k))

theorem merge_atoms {d k : ℕ} (h f : Fin k → Fin d → ℂ) :
    (symmetricProductMatrix (packet h)).mulVec (packet f) =
    fun w => mergeScale k * packet (joined h f) w := by
  let e : Fin k ⊕ Fin k ≃ Fin (k+k) := finSumFinEquiv
  have hh : (fun w : Word d (k+k) => packet h (fun t => w (Fin.castAdd k t)) *
      packet f (fun t => w (Fin.natAdd k t))) =
      fun w => StraightCut.paired h f (w ∘ e) := rfl
  have hp : pureWord (joined h f) = fun w => pureWord (Sum.elim h f) (w ∘ e) := by
    funext w
    symm
    exact Fintype.prod_equiv e _ _ (by intro i; simp [joined,e,Function.comp_def])
  have hp' : packet (joined h f) = fun w => StraightCut.c (Fin (k+k)) *
        clasp (pureWord (joined h f)) w := by
    funext w
    simp [packet, StraightCut.c, clasp, sumSlots_pure, mul_assoc, Nat.factorial_ne_zero]
  have hn : StraightCut.c (Fin (k+k)) ≠ 0 := by
    intro h0
    have hc := StraightCut.c_sq (Fin (k+k))
    simp [h0] at hc
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) : ((k+k).factorial : ℂ) ≠ 0) hc.symm
  rw [symmetricProductMatrix_action, hh, hp', hp]
  funext w
  simp only [Bridges.clasp_transport, StraightCut.absorb_pair, mergeScale]
  field_simp
  ring

theorem mergeScale_sq (k : ℕ) : ((k+k).choose k : ℂ) * (star (mergeScale k) * mergeScale k) = 1 := by
  let c := StraightCut.c (Fin k)
  let v := StraightCut.c (Fin (k+k))
  have hc : star c * c = (k.factorial : ℂ) := by simpa [c] using StraightCut.c_sq (Fin k)
  have hv : star v * v = ((k+k).factorial : ℂ) := by simpa [v] using StraightCut.c_sq (Fin (k+k))
  change _ * (star (c*c/v)*(c*c/v)) = 1
  rw [star_div₀,star_mul',mul_comm (star c) (star c), div_mul_div_comm, hv]
  rw [show star c * star c * (c*c) = (star c*c)*(star c*c) by ring, hc]
  rw [← mul_div_assoc, div_eq_one_iff_eq (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  norm_cast
  simpa [mul_assoc] using Nat.add_choose_mul_factorial_mul_factorial k k

theorem quadratic_scale_left {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix (I × J) (I × J) ℂ) (t : ℂ) (P : I → ℂ) (G : J → ℂ) :
    quadratic M (product (fun i => t * P i) G) =
    (star t * t) * quadratic M (product P G) := by
  simp only [quadratic,product,star_mul',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem triple_permanent {d k : ℕ} (f h g : Fin k → Fin d → ℂ) :
    ((k+k).choose k : ℝ) * ((((k+k)+k).choose (k+k) : ℂ) *
      quadratic (totalClasp d (k+k) k)
        (product ((symmetricProductMatrix (packet h)).mulVec (packet f)) (packet g))).re =
      (crossGram (Sum.elim (joined h f) g) (Sum.elim (joined h f) g)).permanent.re := by
  rw [← StraightCut.fine_permanent, merge_atoms, quadratic_scale_left]
  have mulRe (a : ℕ) (z : ℂ) : (a:ℝ)*z.re = ((a:ℂ)*z).re := by simp [Complex.mul_re]
  rw [mulRe]
  congr 1
  linear_combination ((↑(((k+k)+k).choose (k+k)) : ℂ) *
    quadratic (totalClasp d (k+k) k) (product (packet (joined h f)) (packet g))) * mergeScale_sq k

end
end BlockPermanents.FiveMerge
