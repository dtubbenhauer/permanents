import BlockPermanents.BalancedLastBubble
import BlockPermanents.ThreePlaneSpan
import BlockPermanents.OccupationBasis
import BlockPermanents.BendCoordinates
import BlockPermanents.BalancedPairTrace
import BlockPermanents.ThreePlaneWords

/-! The occupation spaces on the two turned cables are the dual symmetric
powers of the chosen planes. The two bases may be chosen independently. -/
namespace BlockPermanents.BalancedLast
open BalancedSupport Bend TensorCoordinates OccupationBasis ThreePlane BendCoordinates
open scoped Matrix
noncomputable section

private theorem count_word {k t : ℕ} (x : Word k t) (a : Fin k) :
    (occupation x).val.count a = occ x a := by
  simp [occupation, Multiset.count_sum', Multiset.count_singleton, occ,
    OccupationSplit.counts, eq_comm]

private theorem same_occupation {k t : ℕ} (x y : Word k t) :
    occupation x = occupation y ↔ occ x = occ y := by
  constructor
  · intro h
    funext a
    simp only [← count_word, h]
  · intro h
    apply Subtype.ext
    exact Multiset.ext' (fun a => by rw [count_word, count_word, h])

/-- The word-basis column of the clasp is constant on one occupation and
zero on the others; the nonzero coefficient is the occupation weight. -/
private theorem clasp_column {k t : ℕ} (x y : Word k t) :
    symClasp k t x y = if occupation x = occupation y
      then (OccupationBasis.weight (occ y) t : ℂ) else 0 := by
  rw [← kernel_word, kernel_eq, Fintype.card_fin]
  by_cases h : occupation x = occupation y
  · rw [if_pos h, if_pos ((same_occupation x y).mp h), (same_occupation x y).mp h]
  · rw [if_neg h, if_neg (fun q => h ((same_occupation x y).mpr q))]
    simp

private theorem embedded_column {d k : ℕ} (t : ℕ) (E : Matrix (Fin d) (Fin k) ℂ)
    (w : Word k t) :
    (power (Fin t) E * symClasp k t).col w =
      (OccupationBasis.weight (occ w) t : ℂ) • expand E (occupation w) := by
  funext v
  change (∑ f, _ * symClasp k t f w) = _ * expand E _ v
  simp only [clasp_column, expand, power, mul_ite, mul_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

open private realize from BlockPermanents.BalancedLastBubble in
/-- All occupation columns of a frame span exactly the image of its clasped
tensor power. This holds also for a rectangular map of deficient rank. -/
theorem space_range {d k : ℕ} (t : ℕ) (E : Matrix (Fin d) (Fin k) ℂ) :
    space t E = LinearMap.range (power (Fin t) E * symClasp k t).mulVecLin := by
  rw [Matrix.range_mulVecLin, space]
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨o, rfl⟩
    obtain ⟨w, rfl⟩ := realize o
    have h := Submodule.subset_span (R := ℂ)
      (s := Set.range (power (Fin t) E * symClasp k t).col) ⟨w, rfl⟩
    rw [embedded_column] at h
    have hp : (OccupationBasis.weight (occ w) t : ℂ) ≠ 0 := by
      exact_mod_cast (OccupationBasis.weight_pos (occ w) t).ne'
    simpa only [smul_smul, inv_mul_cancel₀ hp, one_smul] using
      (Submodule.span ℂ (Set.range (power (Fin t) E * symClasp k t).col)).smul_mem
        (OccupationBasis.weight (occ w) t : ℂ)⁻¹ h
  · rintro _ ⟨w, rfl⟩
    rw [embedded_column]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨occupation w,rfl⟩)

/-- On any actual plane, the span of its expanded occupations is the intrinsic
symmetric power spanned by packets with all atoms in that plane. -/
theorem space_symmetricPower {d : ℕ} (t : ℕ) (S : Submodule ℂ (FourPlaneBasis.Ambient d)) :
    space t (basisMatrix S) = symmetricPower t S :=
  (space_range t _).trans (symmetricPower_range t S)

private theorem star_mem {d k t : ℕ} (E : Matrix (Fin d) (Fin k) ℂ)
    {f : Word d t → ℂ} (hf : f ∈ space t E) :
    (fun w => star (f w)) ∈ space t (conjugate E) := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨o,rfl⟩ := h
    apply Submodule.subset_span
    refine ⟨o,?_⟩
    funext w
    simp only [expand, conjugate, star_sum, apply_ite star, star_prod, star_zero]
  | zero => simpa only [Pi.zero_apply, star_zero] using (space t (conjugate E)).zero_mem
  | add f g _ _ ih jh =>
    simpa only [Pi.add_apply, star_add] using (space t (conjugate E)).add_mem ih jh
  | smul a f _ ih =>
    simpa only [Pi.smul_apply, smul_eq_mul, star_mul'] using (space t (conjugate E)).smul_mem (star a) ih

/-- On a turned cable, a slice belongs to the conjugate frame space exactly
when its coefficientwise conjugate lies in the original symmetric power. -/
theorem dual_space_iff {d : ℕ} (t : ℕ) (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (f : Word d t → ℂ) :
    f ∈ space t (conjugate (basisMatrix S)) ↔
      (fun w => star (f w)) ∈ symmetricPower t S := by
  rw [← space_symmetricPower]
  constructor
  · intro h
    have he : conjugate (conjugate (basisMatrix S)) = basisMatrix S := by
      ext i j
      exact star_star _
    simpa only [he] using star_mem (t := t) (conjugate (basisMatrix S)) h
  · intro h
    simpa only [star_star] using star_mem (t := t) (basisMatrix S) h

/-- The dual orthonormal frame of an actual plane of the prescribed rank. -/
def turnedFrame {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) : Matrix (Fin d) (Fin k) ℂ :=
  fun i j => star (basisMatrix S i ((finCongr hS).symm j))

theorem turnedFrame_isometry {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) :
    (turnedFrame S hS)ᴴ * turnedFrame S hS = 1 := by
  subst k
  ext i j
  have h := congrArg star (congrFun (congrFun (basis_isometry S) i) j)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, turnedFrame, finCongr_refl,
    Equiv.refl_apply, star_sum, star_mul', Matrix.one_apply,
    apply_ite star, star_zero, star_one] using h

theorem turnedFrame_mem {d k : ℕ} (S : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (t : ℕ) (f : Word d t → ℂ) :
    f ∈ space t (turnedFrame S hS) ↔ (fun w => star (f w)) ∈ symmetricPower t S := by
  subst k
  exact dual_space_iff t S f

private theorem space_fixed {d k t : ℕ} (E : Matrix (Fin d) (Fin k) ℂ)
    {v : Word d t → ℂ} (h : v ∈ space t E) : v ∈ BalancedPairTrace.fixed d t := by
  rw [space_range] at h
  obtain ⟨a,rfl⟩ := h
  change (symClasp d t).mulVec ((power (Fin t) E * symClasp k t).mulVec a) -
    (power (Fin t) E * symClasp k t).mulVec a = 0
  rw [← Matrix.mulVec_mulVec]
  exact sub_eq_zero.mpr (power_symmetric E (PairBound.projected_symmetric k t a))

/-- Supported four-slot states can be tested using just the two ordinary
symmetric slots and the two intrinsic dual symmetric powers. -/
theorem supported_iff {d k : ℕ} (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (hS : Module.finrank ℂ S = k) (hT : Module.finrank ℂ T = k)
    (z : BalancedOpen.Boundary (Word d k) → ℂ) :
    BalancedPairTrace.Supported (turnedFrame S hS) (turnedFrame T hT) z ↔
      (∀ b c e, Symmetric (fun a => z ((a,b),(c,e)))) ∧
      (∀ a c e, Symmetric (fun b => z ((a,b),(c,e)))) ∧
      (∀ a b e, (fun c => star (z ((a,b),(c,e)))) ∈ symmetricPower k S) ∧
      (∀ a b c, (fun e => star (z ((a,b),(c,e)))) ∈ symmetricPower k T) := by
  have fix (u : Word d k → ℂ) : u ∈ BalancedPairTrace.fixed d k ↔ Symmetric u := by
    change (symClasp d k).mulVec u - u = 0 ↔ _
    exact sub_eq_zero
  constructor
  · intro hz
    exact ⟨fun b c e => (fix _).mp (hz.sym0 b c e), fun a c e => (fix _).mp (hz.sym1 a c e),
      fun a b e => (turnedFrame_mem S hS k _).mp (hz.plane2 a b e),
      fun a b c => (turnedFrame_mem T hT k _).mp (hz.plane3 a b c)⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    have p (a b e) := (turnedFrame_mem S hS k _).mpr (h₃ a b e)
    have q (a b c) := (turnedFrame_mem T hT k _).mpr (h₄ a b c)
    exact ⟨fun b c e => (fix _).mpr (h₁ b c e), fun a c e => (fix _).mpr (h₂ a c e),
      fun a b e => space_fixed _ (p a b e), fun a b c => space_fixed _ (q a b c), p, q⟩

end
end BlockPermanents.BalancedLast
