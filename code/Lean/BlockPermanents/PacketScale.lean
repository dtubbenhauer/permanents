import BlockPermanents.MatchingFine

/-! # Rescaling matrix packets at the permanent boundary -/
namespace BlockPermanents.PacketScale
open Closures Bend
open scoped BigOperators
noncomputable section

variable {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]

omit [Fintype D] in
/-- A scalar on each input strand factors out of the normalized clasp. -/
theorem packet_scale_atoms (u : I → ℂ) (x : I → D → ℂ) :
    packet (fun i j => u i * x i j) = fun w => (∏ i, u i) * packet x w := by
  classical
  funext w
  simp only [packet, orderSum, pureWord, Function.comp_apply, Finset.prod_mul_distrib,
    Equiv.prod_comp, ← Finset.mul_sum]
  ring

theorem gram_permanent_scale (u : I → ℂ) (x : I → D → ℂ) :
    (crossGram (fun i j => u i*x i j) (fun i j => u i*x i j)).permanent.re =
    Complex.normSq (∏ i, u i) * (crossGram x x).permanent.re := by
  rw [← packet_gram, packet_scale_atoms, bracket_scale, ← packet_gram,
    Coarse.bracket_self, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul]
  rfl

private theorem energy_nonneg {A : Type*} [Fintype A] (v : A → ℂ) : 0 ≤ energy v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem energy_scale {A : Type*} [Fintype A] (c : ℂ) (v : A → ℂ) :
    energy (fun i => c*v i) = Complex.normSq c * energy v := by
  simp [energy, Complex.normSq_mul, Finset.mul_sum]

/-- Both Gram permanents have the same multidegree. The first strand of a
nonzero packet absorbs its normalizing scalar. A zero packet kills the
coarse permanent, while the fine permanent is a squared norm. -/
theorem remove_unit {m k d : ℕ} (hk : 0 < k)
    (unit_case : ∀ x : Fin m → Fin k → Fin d → ℂ, (∀ i, energy (packet (x i)) = 1) →
      (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      MatchingFine.fine (Function.uncurry x))
    (x : Fin m → Fin k → Fin d → ℂ) :
    (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent.re ≤
      MatchingFine.fine (Function.uncurry x) := by
  classical
  by_cases hz : ∃ i, energy (packet (x i)) = 0
  · obtain ⟨i,hi⟩ := hz
    have zi (j) : packet (x i) j = 0 := by
      have h := Finset.single_le_sum (f := fun t => Complex.normSq (packet (x i) t))
        (fun t _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      change _ ≤ energy (packet (x i)) at h
      exact Complex.normSq_eq_zero.mp (le_antisymm (hi ▸ h) (Complex.normSq_nonneg _))
    have zp : (crossGram (fun j => packet (x j)) (fun j => packet (x j))).permanent = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [crossGram, bracket, zi])
    rw [zp, Complex.zero_re, MatchingFine.fine_eq_energy]
    exact energy_nonneg _
  have hp (i) : 0 < energy (packet (x i)) :=
    lt_of_le_of_ne (energy_nonneg _) (fun h => hz ⟨i,h.symm⟩)
  let c (i : Fin m) : ℂ := ((Real.sqrt (energy (packet (x i))))⁻¹ : ℝ)
  let z : Fin k := ⟨0,hk⟩
  let w (i : Fin m) (j : Fin k) : ℂ := if j=z then c i else 1
  have weights (i) : (∏ j, w i j) = c i := by simp [w]
  have nz (i) : c i ≠ 0 := by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hp i)).ne'
  let y i j t := w i j * x i j t
  have yp (i) : packet (y i) = fun j => c i * packet (x i) j := by
    rw [show y i = (fun j t => w i j * x i j t) from rfl, packet_scale_atoms, weights]
  have hy (i) : energy (packet (y i)) = 1 := by
    rw [yp, energy_scale]
    simp only [c, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (hp i).le,
      inv_mul_cancel₀ (hp i).ne']
  have he := unit_case y hy
  simp only [yp, gram_permanent_scale] at he
  change _ ≤ (crossGram (fun (ij : Fin m × Fin k) t => Function.uncurry w ij *
    Function.uncurry x ij t) (fun ij t => Function.uncurry w ij * Function.uncurry x ij t)).permanent.re at he
  rw [gram_permanent_scale, Fintype.prod_prod_type] at he
  simp only [Function.uncurry_apply_pair, weights] at he
  exact le_of_mul_le_mul_left he (Complex.normSq_pos.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => nz i)))

end
end BlockPermanents.PacketScale
