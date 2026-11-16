import BlockPermanents.RawCycleClass

/-! Unordered matchings as the conjugacy class of disjoint transpositions. -/
namespace BlockPermanents.RawCycleSquares
open CycleMatching CycleComposition CyclePolynomial Matchings
open scoped BigOperators
noncomputable section

private def matchingPerm {q j k : ℕ} (e : Shape (Fin j) (Fin k) ≃ Fin q) : S q :=
  e.permCongr (((Equiv.refl (Fin j)).prodCongr (Equiv.swap (0 : Fin 2) 1)).sumCongr (Equiv.refl (Fin k)))

private theorem perm_left {q j k : ℕ} (e : Shape (Fin j) (Fin k) ≃ Fin q)
    (p : Fin j × Fin 2) :
    matchingPerm e (e (.inl p)) = e (.inl (p.1, Equiv.swap 0 1 p.2)) := by
  rcases p with ⟨n,b⟩
  simp [matchingPerm, Equiv.permCongr_apply]

private theorem perm_right {q j k : ℕ} (e : Shape (Fin j) (Fin k) ≃ Fin q) (t : Fin k) :
    matchingPerm e (e (.inr t)) = e (.inr t) := by
  simp [matchingPerm, Equiv.permCongr_apply]

private theorem perm_type {q j k : ℕ} (e : Shape (Fin j) (Fin k) ≃ Fin q) :
    (matchingPerm e).cycleType = Multiset.replicate j 2 := by
  let p := matchingPerm e
  have sq : p ^ 2 = 1 := by
    ext v
    obtain ⟨w,rfl⟩ := e.surjective v
    rcases w with ⟨a,b⟩ | t
    · simp [p, pow_two, perm_left]
    · simp [p, pow_two, perm_right]
  have lengths := Equiv.Perm.pow_prime_eq_one_iff.mp sq
  have typ : p.cycleType = Multiset.replicate p.cycleType.card 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, lengths⟩
  let a : Fin j × Fin 2 ↪ Fin q := Function.Embedding.inl.trans e.toEmbedding
  have supp : p.support = Finset.univ.map a := by
    ext v
    obtain ⟨w,rfl⟩ := e.surjective v
    rcases w with ⟨n,b⟩ | t
    · rw [Equiv.Perm.mem_support, Finset.mem_map]
      simp only [p, perm_left, Ne, e.injective.eq_iff, Sum.inl.injEq, Prod.mk.injEq, true_and]
      have h : ∃ i ∈ (Finset.univ : Finset (Fin j × Fin 2)), a i = e (.inl (n,b)) := ⟨(n,b), Finset.mem_univ _, rfl⟩
      simp only [h, iff_true]
      fin_cases b <;> decide
    · rw [Equiv.Perm.mem_support, Finset.mem_map]
      simp only [p, perm_right, ne_self_iff_false, false_iff, not_exists, not_and]
      intro i _
      exact fun h => Sum.inl_ne_inr (e.injective h)
  have hc := p.sum_cycleType
  rw [typ, supp] at hc
  simp only [Multiset.sum_replicate, smul_eq_mul, Finset.card_map, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] at hc
  change p.cycleType = _
  rwa [show j = p.cycleType.card by omega]

private theorem perm_mean {q j k : ℕ} (e : Shape (Fin j) (Fin k) ≃ Fin q)
    (g : Gram q) (hg : UnitGram g) : mean g (matchingPerm e) = (Z g j : ℂ) := by
  let a : Fin j × Fin 2 ↪ Fin q := Function.Embedding.inl.trans e.toEmbedding
  have circuit_value (σ : S q) :
      circuit g (matchingPerm e) σ = (∏ n, sqEdge g (σ (a (n,0))) (σ (a (n,1))) : ℝ) := by
    unfold circuit
    rw [← e.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
    simp only [perm_left, perm_right, hg.diag, Finset.prod_const_one, mul_one,
      Fin.prod_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro n _
    change g _ _ * g _ _ = (Complex.normSq (g _ _) : ℂ)
    rw [Complex.normSq_eq_conj_mul_self]
    rw [← hg.herm (σ (e (.inl (n,0)))) (σ (e (.inl (n,1))))]
    rfl
  rw [mean_real g hg.herm, mean, re_complexAverage]
  simp_rw [circuit_value, Complex.ofReal_re]
  exact congrArg (fun x : ℝ => (x : ℂ)) (by simpa using mean_edges g a)

private theorem matching_card {q j : ℕ} (h : 2*j ≤ q) :
    (((Finset.univ.filter (fun τ : S q => τ.cycleType = Multiset.replicate j 2)).card : ℝ) *
      ((2:ℝ)^j * (j.factorial : ℝ) * (q-2*j).factorial)) = q.factorial := by
  let M := Multiset.replicate j 2
  have mem (a : ℕ) (ha : a ∈ M) : a = 2 := (Multiset.eq_of_mem_replicate ha)
  have cond : M.sum ≤ Fintype.card (Fin q) ∧ ∀ a ∈ M, 2 ≤ a := by
    refine ⟨?_,fun a ha => (mem a ha).ge⟩
    simpa [M, mul_comm] using h
  have sum : M.sum = 2*j := by simp [M, mul_comm]
  have prod : M.prod = 2^j := by simp [M]
  have multiplicity : (∏ n ∈ M.toFinset, (M.count n).factorial) = j.factorial := by
    cases j with
    | zero => simp [M]
    | succ n =>
      have single : M.toFinset = {2} := by
        ext v
        simp only [M, Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton,
          show n + 1 ≠ 0 by omega, not_false_eq_true, true_and]
        omega
      rw [single, Finset.prod_singleton]
      exact congrArg Nat.factorial (Multiset.count_replicate_self 2 (n+1))
  have hc := Equiv.Perm.card_of_cycleType_mul_eq (Fin q) M
  rw [if_pos cond, sum, prod, multiplicity, Fintype.card_fin] at hc
  simpa [M, mul_comm, mul_left_comm, mul_assoc] using
    (show (({τ : S q | τ.cycleType = M} : Finset _).card : ℝ) *
      ((q-2*j).factorial * (2:ℝ)^j * (j.factorial : ℝ)) = q.factorial by exact_mod_cast hc)

/-- M_j sums the closed monomials of the actual j-edge matchings. Each
permutation in the summation has j disjoint transpositions and fixes all
remaining labels. -/
def matchingMass {q : ℕ} (g : Gram q) (j : ℕ) : ℝ :=
  (classSum g (Multiset.replicate j 2)).re

/-- The relabelled matching mean converted to the unordered matching sum. -/
theorem matching_class_sum {q : ℕ} (g : Gram q) (hg : UnitGram g) (j : ℕ) (h : 2*j ≤ q) :
    classSum g (Multiset.replicate j 2) =
      (((q.factorial : ℝ) / (2^j * j.factorial * (q-2*j).factorial) * Z g j : ℝ) : ℂ) := by
  let e : Shape (Fin j) (Fin (q-2*j)) ≃ Fin q := Fintype.equivOfCardEq (by
    simp only [Shape,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega)
  have ha := class_average g (matchingPerm e)
  rw [perm_type,perm_mean e g hg] at ha
  have hc : ((classSet q (Multiset.replicate j 2)).card : ℝ) =
      (q.factorial : ℝ) / (2^j * j.factorial * (q-2*j).factorial) :=
    (eq_div_iff (by positivity)).mpr (matching_card h)
  rw [← hc, Complex.ofReal_mul]
  exact ha

theorem matchingMass_eq {q : ℕ} (g : Gram q) (hg : UnitGram g) (j : ℕ) (h : 2*j ≤ q) :
    matchingMass g j = (q.factorial : ℝ) / (2^j * j.factorial * (q-2*j).factorial) * Z g j := by
  rw [matchingMass, matching_class_sum g hg j h, Complex.ofReal_re]

theorem matching_class_outside {q : ℕ} (g : Gram q) (j : ℕ) (h : q < 2*j) :
    classSum g (Multiset.replicate j 2) = 0 := by
  have empty : classSet q (Multiset.replicate j 2) = ∅ := by
    apply Finset.card_eq_zero.mp
    apply (Equiv.Perm.card_of_cycleType_eq_zero_iff (Fin q)).mpr
    rintro ⟨hc,_⟩
    simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hc
    omega
  simp [classSum, empty]

theorem matchingMass_outside {q : ℕ} (g : Gram q) (j : ℕ) (h : q < 2*j) :
    matchingMass g j = 0 := by simp [matchingMass,matching_class_outside g j h]

end
end BlockPermanents.RawCycleSquares
