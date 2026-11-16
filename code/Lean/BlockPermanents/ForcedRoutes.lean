import BlockPermanents.MarkedEdges

/-! # Factoring the constrained thin-permutation sum

Order the prescribed source and target packet pairs first, in matching
order. Their positions then have the common label set I.  Every constrained
thin permutation acts independently inside their two-slot fibers and on
the remaining thin slots.
-/
namespace BlockPermanents.ForcedRoutes
noncomputable section
open scoped BigOperators
abbrev Slots (I R : Type*) := (I × Fin 2) ⊕ R

variable {I R D : Type*}

def preserves (p : Equiv.Perm (Slots I R)) : Prop :=
  ∀ i t, ∃ u, p (.inl (i,t)) = .inl (i,u)

def assemble (f : I → Equiv.Perm (Fin 2)) (q : Equiv.Perm R) : Equiv.Perm (Slots I R) :=
  (Equiv.prodCongrRight f).sumCongr q

private theorem assemble_inl (f : I → Equiv.Perm (Fin 2)) (q : Equiv.Perm R) (i t) :
    assemble f q (.inl (i,t)) = .inl (i,f i t) := rfl
private theorem assemble_inr (f : I → Equiv.Perm (Fin 2)) (q : Equiv.Perm R) (t) :
    assemble f q (.inr t) = .inr (q t) := rfl

/-- The full fiber over a partial matching, including both internal
orders for every forced quadratic packet. -/
def fiber [Finite R] :
    ((I → Equiv.Perm (Fin 2)) × Equiv.Perm R) ≃ {p : Equiv.Perm (Slots I R) // preserves p} := by
  let pack (u : (I → Equiv.Perm (Fin 2)) × Equiv.Perm R) :
      {p : Equiv.Perm (Slots I R) // preserves p} :=
    ⟨assemble u.1 u.2, fun i t => ⟨u.1 i t,rfl⟩⟩
  apply Equiv.ofBijective pack
  constructor
  · rintro ⟨f,q⟩ ⟨g,p⟩ h
    have he := congrArg Subtype.val h
    apply Prod.ext
    · funext i
      apply Equiv.ext
      intro t
      exact congrArg Prod.snd (Sum.inl.inj (congrArg (fun v : Equiv.Perm _ => v (.inl (i,t))) he))
    · ext t
      exact Sum.inr.inj (congrArg (fun v : Equiv.Perm _ => v (.inr t)) he)
  · rintro ⟨p,h⟩
    have hw := h
    choose f hf using hw
    have hfi (i) : Function.Injective (f i) := by
      intro a b hab
      have he := p.injective ((hf i a).trans ((congrArg (fun u => Sum.inl (i,u)) hab).trans (hf i b).symm))
      exact congrArg Prod.snd (Sum.inl.inj he)
    let g (i) := Equiv.ofBijective (f i) ⟨hfi i, Finite.surjective_of_injective (hfi i)⟩
    have hr (t : R) : ∃ u, p (.inr t) = .inr u := by
      cases he : p (.inr t) with
      | inr u => exact ⟨u,rfl⟩
      | inl jt =>
          obtain ⟨j,s⟩ := jt
          obtain ⟨a,ha⟩ := (g j).surjective s
          have hfa : f j a = s := ha
          have he' : p (.inl (j,a)) = p (.inr t) := by rw [hf, hfa, he]
          exact (Sum.inl_ne_inr (p.injective he')).elim
    choose b hb using hr
    have hbi : Function.Injective b := by
      intro t u htu
      exact Sum.inr.inj (p.injective ((hb t).trans ((congrArg Sum.inr htu).trans (hb u).symm)))
    let q := Equiv.ofBijective b ⟨hbi, Finite.surjective_of_injective hbi⟩
    refine ⟨(g,q),Subtype.ext ?_⟩
    ext t
    rcases t with ⟨i,a⟩|a
    · exact (hf i a).symm
    · exact (hb a).symm

/-- Tensor product before the gluing, with all unchanged factors grouped
in the residual tensor. -/
def tensor [Fintype I] (x : I → (Fin 2 → D) → ℚ) (a : (R → D) → ℚ) (w : Slots I R → D) : ℚ :=
  (∏ i, x i (fun t => w (.inl (i,t)))) * a (w ∘ Sum.inr)

def contraction {K : Type*} [Fintype K] [DecidableEq K] [Fintype D]
    (a b : (K → D) → ℚ) (p : Equiv.Perm K) : ℚ := ∑ w, a w * b (w ∘ p)

private def words : ((I → Fin 2 → D) × (R → D)) ≃ (Slots I R → D) where
  toFun u := Sum.elim (Function.uncurry u.1) u.2
  invFun w := (fun i j => w (.inl (i,j)),fun r => w (.inr r))
  left_inv := by rintro ⟨x,y⟩; rfl
  right_inv := by intro w; funext i; rcases i with ⟨i,j⟩|r <;> rfl

variable [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Fintype D]

/-- Cut the orthonormal binary words on the prescribed blocks before
summing the residual permutation. -/
theorem contraction_assemble (x y : I → (Fin 2 → D) → ℚ) (a b : (R → D) → ℚ)
    (hy : ∀ i w (p : Equiv.Perm (Fin 2)), y i (w ∘ p) = y i w)
    (f : I → Equiv.Perm (Fin 2)) (q : Equiv.Perm R) :
    contraction (tensor x a) (tensor y b) (assemble f q) =
      (∏ i, ∑ w, x i w*y i w) * contraction a b q := by
  unfold contraction
  rw [← words.sum_comp (fun w => tensor x a w * tensor y b (w ∘ assemble f q)),Fintype.sum_prod_type]
  change (∑ v : I → Fin 2 → D, ∑ w : R → D,
    ((∏ i, x i (v i))*a w) * ((∏ i, y i (v i ∘ f i))*b (w ∘ q))) = _
  simp_rw [hy]
  rw [Fintype.prod_sum (fun i w => x i w*y i w), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum,Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- Each two-way fiber absorbs one factor 2 in the fine normalization.
The residual normalization may be chosen for any number of unforced packets. -/
theorem forced_factor (x y : I → (Fin 2 → D) → ℚ) (a b : (R → D) → ℚ)
    (hy : ∀ i w (p : Equiv.Perm (Fin 2)), y i (w ∘ p) = y i w) (remaining : ℕ) :
    letI := Classical.decPred (@preserves I R)
    (∑ p : {p : Equiv.Perm (Slots I R) // preserves p}, contraction (tensor x a) (tensor y b) p.1) /
      2^(Fintype.card I+remaining) = (∏ i, ∑ w, x i w*y i w) *
        ((∑ q : Equiv.Perm R, contraction a b q)/2^remaining) := by
  classical
  rw [← fiber.sum_comp (fun p => contraction (tensor x a) (tensor y b) p.1),Fintype.sum_prod_type]
  change (∑ f, ∑ q, contraction (tensor x a) (tensor y b) (assemble f q))/_ = _
  simp only [contraction_assemble x y a b hy,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  norm_num [Nat.factorial,pow_add]
  field_simp
  ring

end
end BlockPermanents.ForcedRoutes
