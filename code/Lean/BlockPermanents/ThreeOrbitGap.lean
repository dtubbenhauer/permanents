import BlockPermanents.ThreeAverageClosure
import BlockPermanents.MatchingThreshold

/-! The averaged original representative gives the permanent inequality
whenever each marked product has a nonnegative evaluation. -/
namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen Closures Equiv
open scoped BigOperators Matrix ComplexOrder
noncomputable section

def gap {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) :=
  (crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent

private theorem gram_permute {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (x : I→D→ℂ) (p : Perm I) :
    (crossGram (x ∘ p) (x ∘ p)).permanent = (crossGram x x).permanent := by
  change (((crossGram x x).submatrix p id).submatrix id p).permanent=_
  rw [Matrix.permanent_permute_rows,Matrix.permanent_permute_cols]

theorem gap_permute {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ) (p : G) : gap (x ∘ p) = gap x := by
  let q := p.prodCongr (Equiv.refl (Fin k))
  exact congrArg₂ (·-·) (gram_permute (Function.uncurry x) q) (gram_permute (fun i => packet (x i)) p)

theorem gap_of_marked {d k : ℕ} (x : Fin 3 → Fin k → Fin d → ℂ)
    (hm : ∀ p : G, 0 ≤ (quadratic (original d k) (data (x ∘ p))).re)
    (ht : ∀ y : Fin 3 → Fin k → Fin d → ℂ, quadratic (target d k) (data y) = gap y) :
    0 ≤ (gap x).re := by
  have h := congrArg Complex.re (sum_original x)
  simp only [ht,gap_permute,Complex.re_sum,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin,show (3:ℕ).factorial=6 by decide,nsmul_eq_mul] at h
  norm_num [Complex.mul_re] at h
  have h' := Finset.sum_nonneg (s:=Finset.univ) (fun p _ => hm p)
  linarith

theorem productData {d k : ℕ} (x : Fin 3→Fin k→Fin d→ℂ) :
    data x = product (product (packet (x 0)) (packet (x 1))) (packet (x 2)) := by
  funext w
  change (∏ i : Fin 3, packet (x i) ((tuple _ w) i)) = _
  rw [Fin.prod_univ_three]
  rfl

theorem packet_supported {d k : ℕ} (S : Finset (Fin d)) (x : Fin k → Fin d→ℂ)
    (hx : ∀ i j, j∉S → x i j=0) (w : Word d k) (hw : ∃ i, w i∉S) : packet x w=0 := by
  obtain ⟨i,hi⟩ := hw
  have hz (p : Perm (Fin k)) : pureWord (x ∘ p) w = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (hx (p i) (w i) hi)
  simp [packet,orderSum,hz]

end
end BlockPermanents.ThreeMarkedAverage
