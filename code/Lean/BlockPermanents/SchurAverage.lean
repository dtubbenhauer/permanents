import BlockPermanents.SchurFibreCount
import BlockPermanents.SchurWireCriterion

/-! # Expanding the total clasp by the number of crossing wires -/

namespace BlockPermanents.SchurAverage
open Transfer WireSchur Bend
open scoped BigOperators
noncomputable section

variable {G H R L : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Ring R] [Algebra ℚ R]

private theorem full_clasp_sandwich (ρ : G →* R) (i : H →* G) :
    clasp (ρ.comp i) * clasp ρ * clasp (ρ.comp i) = clasp ρ := by
  have hc : (Fintype.card H : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have left : clasp (ρ.comp i) * clasp ρ = clasp ρ := by
    change ((Fintype.card H : ℚ)⁻¹ • ∑ h, (ρ.comp i) h) * clasp ρ = _
    simp only [smul_mul_assoc, Finset.sum_mul, MonoidHom.comp_apply, absorb_left,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]
  rw [left]
  change clasp ρ * ((Fintype.card H : ℚ)⁻¹ • ∑ h, (ρ.comp i) h) = _
  simp only [mul_smul_comm, Finset.mul_sum, MonoidHom.comp_apply, absorb_right,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]

/-- After sandwiching with the subgroup clasp, the full sum is constant on each
double coset. Its coefficient is the number of permutations in that coset. -/
theorem finite_average [Fintype L] [DecidableEq L] (ρ : G →* R) (i : H →* G)
    (idx : G → L) (rep : L → G)
    (factor : ∀ g, ∃ a b, g = i a * rep (idx g) * i b) :
    clasp ρ = (Fintype.card G : ℚ)⁻¹ • ∑ r,
      (Fintype.card {g // idx g = r} : ℚ) •
        (clasp (ρ.comp i) * ρ (rep r) * clasp (ρ.comp i)) := by
  classical
  let P := clasp (ρ.comp i)
  let F (g : G) := P * ρ g * P
  have eq (g : G) : F g = F (rep (idx g)) := by
    obtain ⟨a, b, h⟩ := factor g
    unfold F
    conv_lhs => rw [h, map_mul, map_mul]
    have left : P * ρ (i a) = P := absorb_right (ρ.comp i) a
    have right : ρ (i b) * P = P := absorb_left (ρ.comp i) b
    calc
      _ = (P * ρ (i a)) * ρ (rep (idx g)) * (ρ (i b) * P) := by simp only [mul_assoc]
      _ = _ := by rw [left, right]
  calc
    _ = P * clasp ρ * P := (full_clasp_sandwich ρ i).symm
    _ = (Fintype.card G : ℚ)⁻¹ • ∑ g, F g := by
      change P * ((Fintype.card G : ℚ)⁻¹ • ∑ g, ρ g) * P = _
      simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, F]
    _ = _ := by
      apply congrArg (fun x : R => (Fintype.card G : ℚ)⁻¹ • x)
      rw [← Finset.sum_fiberwise Finset.univ idx F]
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ∑ _g ∈ Finset.univ.filter (fun g => idx g = r), F (rep r) := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [eq g, (Finset.mem_filter.mp hg).2]
        _ = _ := by rw [Finset.sum_const, ← Fintype.card_subtype, Nat.cast_smul_eq_nsmul]

/-- Convert the two block factorials in a fibre size into the Schur coefficient. -/
private theorem choose_factorials (p q : ℕ) :
    ((p+q).choose p : ℚ) * ((p+q).factorial : ℚ)⁻¹ *
        (p.factorial * q.factorial : ℕ) = 1 := by
  have hc : ((p+q).choose p : ℚ) * (p.factorial : ℚ) * (q.factorial : ℚ) =
      ((p+q).factorial : ℚ) := by
    exact_mod_cast (show (p+q).choose p * p.factorial * q.factorial = (p+q).factorial by
      simpa using Nat.choose_mul_factorial_mul_factorial (n := p+q) (k := p) (Nat.le_add_right p q))
  have hn : ((p+q).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  linarith

/-- The double-coset decomposition gives the switch identity in any rational
algebra representation of the permutations of the two cables. -/
private theorem switch_of_fibres {p q : ℕ} (ρ : Equiv.Perm (Slots p q) →* R)
    (idx : Equiv.Perm (Slots p q) → CutIndex p q)
    (factor : ∀ g, ∃ a b : Equiv.Perm (Fin p) × Equiv.Perm (Fin q),
      g = a.1.sumCongr a.2 * exchangePerm p q (idx g) * b.1.sumCongr b.2)
    (count : ∀ r, Fintype.card {g // idx g = r} =
      p.factorial * q.factorial * p.choose r.val * q.choose r.val) :
    ((p+q).choose p : ℚ) • clasp ρ =
      ∑ r : CutIndex p q, (weight p q r : ℚ) •
        (clasp (ρ.comp (Equiv.Perm.sumCongrHom _ _)) * ρ (exchangePerm p q r) *
          clasp (ρ.comp (Equiv.Perm.sumCongrHom _ _))) := by
  classical
  have avg := finite_average ρ (Equiv.Perm.sumCongrHom (Fin p) (Fin q)) idx
    (exchangePerm p q) factor
  rw [avg, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul, count]
  congr 1
  simp only [Fintype.card_perm, Fintype.card_sum, Fintype.card_fin, Nat.cast_mul, weight]
  have c := choose_factorials p q
  push_cast at c
  calc
    _ = ((((p + q).choose p : ℚ) * ((p + q).factorial : ℚ)⁻¹ *
      ((p.factorial : ℚ) * q.factorial)) * (p.choose r.val * q.choose r.val)) := by ring
    _ = _ := by rw [c, one_mul]

/-- The Schur exchange identity for any rational-algebra representation of the
thin wires. The coefficients count the choices of crossing slots. -/
theorem representation_identity {p q : ℕ} (ρ : Equiv.Perm (Slots p q) →* R) :
    ((p+q).choose p : ℚ) • clasp ρ =
      ∑ r : CutIndex p q, (weight p q r : ℚ) •
        (clasp (ρ.comp (Equiv.Perm.sumCongrHom _ _)) * ρ (exchangePerm p q r) *
          clasp (ρ.comp (Equiv.Perm.sumCongrHom _ _))) := by
  apply switch_of_fibres ρ SchurClass.crossIndex
  · intro g
    obtain ⟨a,c,b,e,h⟩ := SchurClass.factorization g
    exact ⟨(a,b), (c,e), h⟩
  · intro r
    simpa only [Fintype.card_subtype, Fin.ext_iff, SchurClass.crossIndex] using
      SchurFibreCount.card_cross_fibre r

/-- The weighted wire identity in every dimension and at all cable thicknesses. -/
theorem wire_identity (d p q : ℕ) : SchurWireCriterion.OperatorIdentity d p q :=
  representation_identity (action d p q)

end
end BlockPermanents.SchurAverage
