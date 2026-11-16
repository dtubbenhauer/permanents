import BlockPermanents.FaceMeans
import BlockPermanents.FaceCounts
import Mathlib.Data.Fintype.CardEmbedding

/-! The unordered four-set and spectator matching in (AA.4).
Each edge is the two-element finset of its endpoints. -/
namespace BlockPermanents.RawFaceMeans
open FaceMeans FaceSampling
noncomputable section
open scoped BigOperators

abbrev Config (m : ℕ) := Finset (Fin m) × Finset (Finset (Fin m))
abbrev Ordered (m r : ℕ) := Roles r 4 ↪ Fin m

private def ran {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) :=
  Finset.univ.image f

private theorem mem_ran {A B : Type*} [Fintype A] [DecidableEq B] {f : A → B} {b : B} :
    b ∈ ran f ↔ ∃ a, f a = b := by simp [ran]

private theorem ran_perm {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (p : Equiv.Perm A) : ran (fun i => f (p i)) = ran f := by
  ext b
  simp only [mem_ran]
  exact ⟨fun ⟨i,h⟩ => ⟨p i,h⟩, fun ⟨i,h⟩ => ⟨p.symm i, by simpa using h⟩⟩

private theorem perm_of_ran {A B : Type*} [Fintype A] [DecidableEq B]
    {f g : A → B} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ran f = ran g) : ∃ p : Equiv.Perm A, ∀ i, g i = f (p i) := by
  let a : A ↪ B := ⟨f,hf⟩
  let b : A ↪ B := ⟨g,hg⟩
  have hr : Set.range b = Set.range a := by
    ext i
    change (∃ t, g t = i) ↔ ∃ t, f t = i
    rw [← mem_ran, ← mem_ran, h]
  let c := b.toEquivRange.trans (Equiv.setCongr hr)
  refine ⟨c.trans a.toEquivRange.symm, fun i => ?_⟩
  exact (congrArg Subtype.val (a.toEquivRange.apply_symm_apply (c i))).symm

def edge {m r : ℕ} (v : Roles r 4 → Fin m) (i : Fin r) : Finset (Fin m) :=
  ran (fun t : Fin 2 => v (.inl (i,t)))

def forget {m r : ℕ} (v : Roles r 4 → Fin m) : Config m :=
  (ran (fun t => v (.inr t)), ran (edge v))

def configs (m r : ℕ) : Finset (Config m) :=
  Finset.univ.image (fun e : Ordered m r => forget e)

private theorem edge_inj {m r : ℕ} (e : Ordered m r) : Function.Injective (edge e) := by
  intro i j h
  have hp : e (.inl (i,0)) ∈ edge e i := mem_ran.mpr ⟨0,rfl⟩
  rw [h] at hp
  obtain ⟨t, ht⟩ := mem_ran.mp hp
  exact (congrArg Prod.fst (Sum.inl.inj (e.injective ht))).symm

abbrev Orders (r : ℕ) := Equiv.Perm (Fin 4) × Equiv.Perm (Fin r) × (Fin r → Equiv.Perm (Fin 2))

private def rename {r : ℕ} (g : Orders r) : Equiv.Perm (Roles r 4) :=
  Equiv.sumCongr ((Equiv.prodCongrRight g.2.2).trans (Equiv.prodCongr g.2.1 (Equiv.refl _))) g.1

private def reorder {m r : ℕ} (e : Ordered m r) (g : Orders r) : Ordered m r :=
  (rename g).toEmbedding.trans e

@[simp] private theorem reorder_active {m r} (e : Ordered m r) (g : Orders r) (i : Fin 4) :
    reorder e g (.inr i) = e (.inr (g.1 i)) := rfl

@[simp] private theorem reorder_pair {m r} (e : Ordered m r) (g : Orders r) (i : Fin r) (t : Fin 2) :
    reorder e g (.inl (i,t)) = e (.inl (g.2.1 i,g.2.2 i t)) := rfl

private theorem forget_reorder {m r} (e : Ordered m r) (g : Orders r) :
    forget (reorder e g) = forget e := by
  refine Prod.ext (ran_perm (fun i => e (.inr i)) g.1) ?_
  have h : edge (reorder e g) = fun i => edge e (g.2.1 i) := by
    funext i
    exact ran_perm (fun t => e (.inl (g.2.1 i,t))) (g.2.2 i)
  simp only [forget, h]
  exact ran_perm (edge e) g.2.1

private theorem reorder_inj {m r} (e : Ordered m r) : Function.Injective (reorder e) := by
  intro g h eq
  have he (i : Roles r 4) := e.injective (DFunLike.congr_fun eq i)
  have act (i : Fin 4) : g.1 i = h.1 i := Sum.inr.inj (he (.inr i))
  have pair (i : Fin r) (t : Fin 2) : (g.2.1 i,g.2.2 i t) = (h.2.1 i,h.2.2 i t) :=
    Sum.inl.inj (he (.inl (i,t)))
  refine Prod.ext (Equiv.ext act) (Prod.ext (Equiv.ext (fun i => ?_)) (funext (fun i => Equiv.ext (fun t => ?_))))
  · exact congrArg Prod.fst (pair i 0)
  · exact congrArg Prod.snd (pair i t)

private theorem exists_reorder {m r} (e f : Ordered m r) (h : forget e = forget f) :
    ∃ g : Orders r, reorder e g = f := by
  obtain ⟨a, ha⟩ := perm_of_ran
    (fun i j h => Sum.inr.inj (e.injective h)) (fun i j h => Sum.inr.inj (f.injective h))
    (congrArg Prod.fst h)
  obtain ⟨p, hp⟩ := perm_of_ran (edge_inj e) (edge_inj f) (congrArg Prod.snd h)
  have single (i : Fin r) : ∃ b : Equiv.Perm (Fin 2), ∀ t,
      f (.inl (i,t)) = e (.inl (p i,b t)) := by
    apply perm_of_ran _ _ (hp i).symm
    · intro j k h; exact congrArg Prod.snd (Sum.inl.inj (e.injective h))
    · intro j k h; exact congrArg Prod.snd (Sum.inl.inj (f.injective h))
  choose b hb using single
  refine ⟨(a,p,b), Function.Embedding.ext (fun t => ?_)⟩
  rcases t with ⟨i,j⟩ | i
  · exact (hb i j).symm
  · exact (ha i).symm

/-- Every unordered pair (J,L) has 4! r! 2^r internal orderings. -/
theorem fiber_card {m r} {c : Config m} (hc : c ∈ configs m r) :
    (Finset.univ.filter (fun f : Ordered m r => forget f = c)).card =
      24 * 2^r * r.factorial := by
  classical
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hc
  have he : Finset.univ.filter (fun f : Ordered m r => forget f = forget e) =
      Finset.univ.image (reorder e) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun h => exists_reorder e f h.symm, fun ⟨g,h⟩ => h ▸ forget_reorder e g⟩
  rw [he, Finset.card_image_of_injective _ (reorder_inj e), Finset.card_univ]
  simp [Orders,Fintype.card_perm, Nat.factorial, Nat.mul_right_comm, Nat.mul_assoc]

private theorem card_orders (m r : ℕ) :
    (Fintype.card (Ordered m r) : ℝ) =
      (24 * 2^r * r.factorial) * FaceCounts.multiplicity m r := by
  rw [Fintype.card_embedding_eq]
  simp only [Roles, Fintype.card_fin, Fintype.card_sum, Fintype.card_prod]
  rw [show r * 2 + 4 = 4+2*r by omega, FaceCounts.multiplicity]
  split_ifs with fit
  · have h : ((m-(4+2*r)).factorial : ℝ) * m.descFactorial (4+2*r) = m.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial fit
    rw [← h]
    field_simp
    ring
  · simp [Nat.descFactorial_of_lt (lt_of_not_ge fit)]

private theorem embed_sum_sample {A : Type*} [Fintype A] (m : ℕ) (F : (A → Fin m) → ℝ) :
    (∑ e : A ↪ Fin m, F e) = (Fintype.card (A ↪ Fin m) : ℝ) * sample m F := by
  classical
  have h (σ : Equiv.Perm (Fin m)) : (∑ e : A ↪ Fin m, F (σ ∘ e)) = ∑ e : A ↪ Fin m, F e :=
    ((Equiv.refl A).embeddingCongr σ).sum_comp (fun e => F e)
  calc
    _ = Matchings.average m (fun _ => ∑ e : A ↪ Fin m, F e) := (Matchings.average_const _ _).symm
    _ = Matchings.average m (fun σ => ∑ e : A ↪ Fin m, F (σ ∘ e)) := by simp_rw [h]
    _ = ∑ e : A ↪ Fin m, Matchings.average m (fun σ => F (σ ∘ e)) := Matchings.average_sum _ _
    _ = _ := by simp_rw [← sample_eq]; simp

/-- Replacing the uniform role sample by the sum over actual distinct four-sets
and their disjoint spectator matchings introduces precisely d(m,r) from (AA.4). -/
theorem sum_eq (m r : ℕ) (F : Config m → ℝ) :
    (∑ c ∈ configs m r, F c) = FaceCounts.multiplicity m r *
      sample m (fun v : Roles r 4 → Fin m => F (forget v)) := by
  classical
  let k : ℝ := 24*2^r*r.factorial
  have hk : k ≠ 0 := by dsimp [k]; positivity
  apply (mul_right_inj' hk).mp
  rw [Finset.mul_sum, ← mul_assoc, ← card_orders, ← embed_sum_sample]
  have hs : ∀ e ∈ (Finset.univ : Finset (Ordered m r)), forget e ∈ configs m r :=
    fun e he => Finset.mem_image_of_mem _ he
  rw [← Finset.sum_fiberwise_of_maps_to' hs F]
  apply Finset.sum_congr rfl
  intro c hc
  simp [fiber_card hc, k]

/-- Intrinsic conditions on the unordered sets appearing in (AA.4). -/
structure Valid {m : ℕ} (r : ℕ) (c : Config m) : Prop where
  four : c.1.card = 4
  size : c.2.card = r
  endpoints : ∀ E ∈ c.2, E.card = 2
  off : ∀ E ∈ c.2, Disjoint c.1 E
  matching : ∀ E ∈ c.2, ∀ D ∈ c.2, E ≠ D → Disjoint E D

private theorem valid_forget {m r} (e : Ordered m r) : Valid r (forget e) := by
  have ha : Function.Injective (fun i : Fin 4 => e (.inr i)) :=
    fun i j h => Sum.inr.inj (e.injective h)
  have ht (i : Fin r) : Function.Injective (fun t : Fin 2 => e (.inl (i,t))) :=
    fun j k h => congrArg Prod.snd (Sum.inl.inj (e.injective h))
  constructor
  · simp [forget,ran, Finset.card_image_of_injective _ ha]
  · simp [forget,ran, Finset.card_image_of_injective _ (edge_inj e)]
  · intro E hE
    obtain ⟨i,rfl⟩ := mem_ran.mp hE
    simp [edge,ran, Finset.card_image_of_injective _ (ht i)]
  · intro E hE
    obtain ⟨i,rfl⟩ := mem_ran.mp hE
    apply Finset.disjoint_left.mpr
    intro t ht₁ ht₂
    obtain ⟨j,rfl⟩ := mem_ran.mp ht₁
    obtain ⟨k,hk⟩ := mem_ran.mp ht₂
    exact Sum.inl_ne_inr (e.injective hk)
  · intro E hE D hD hED
    obtain ⟨i,rfl⟩ := mem_ran.mp hE
    obtain ⟨j,rfl⟩ := mem_ran.mp hD
    apply Finset.disjoint_left.mpr
    intro t hx hy
    obtain ⟨a,rfl⟩ := mem_ran.mp hx
    obtain ⟨b,hb⟩ := mem_ran.mp hy
    have hij := congrArg Prod.fst (Sum.inl.inj (e.injective hb))
    exact hED (congrArg (edge e) hij.symm)

/-- The role image enumerates every four-set and every matching on its
complement, with no extra restrictions. -/
theorem mem_configs {m r} {c : Config m} : c ∈ configs m r ↔ Valid r c := by
  classical
  constructor
  · rintro hc
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hc
    exact valid_forget e
  · intro h
    let a : Fin 4 ≃ c.1 := (Fintype.equivFinOfCardEq (by simpa using h.four)).symm
    let p : Fin r ≃ c.2 := (Fintype.equivFinOfCardEq (by simpa using h.size)).symm
    let b (i : Fin r) : Fin 2 ≃ (p i).val :=
      (Fintype.equivFinOfCardEq (by simpa using h.endpoints _ (p i).property)).symm
    let v : Roles r 4 → Fin m := Sum.elim (fun z => (b z.1 z.2).val) (fun t => (a t).val)
    have ev (i j : Fin r) (s t : Fin 2) (he : (b i s).val = (b j t).val) : i = j := by
      by_contra hn
      have hne : (p i).val ≠ (p j).val :=
        fun hij => hn (p.injective (Subtype.ext hij))
      exact Finset.disjoint_left.mp (h.matching _ (p i).property _ (p j).property hne)
        (b i s).property (he ▸ (b j t).property)
    have off (i : Fin r) (s : Fin 2) (t : Fin 4) : (b i s).val ≠ (a t).val := by
      intro he
      exact Finset.disjoint_left.mp (h.off _ (p i).property) (a t).property (he ▸ (b i s).property)
    have hv : Function.Injective v := by
      rintro (⟨i,s⟩ | t) (⟨j,u⟩ | k) he
      · obtain rfl := ev i j s u he
        have hs : s = u := (b i).injective (Subtype.ext he)
        rw [hs]
      · exact (off i s k he).elim
      · exact (off j u t he.symm).elim
      · exact congrArg Sum.inr (a.injective (Subtype.ext he))
    let e : Ordered m r := ⟨v,hv⟩
    refine Finset.mem_image.mpr ⟨e,Finset.mem_univ _,Prod.ext ?_ ?_⟩
    · ext t
      rw [show (forget e).1 = ran (fun k => (a k).val) from rfl, mem_ran]
      exact ⟨fun ⟨k,hk⟩ => hk ▸ (a k).property,
        fun ht => ⟨a.symm ⟨t,ht⟩, congrArg Subtype.val (a.apply_symm_apply _)⟩⟩
    · have he (i : Fin r) : edge e i = (p i).val := by
        ext t
        rw [show edge e i = ran (fun k => (b i k).val) from rfl, mem_ran]
        exact ⟨fun ⟨k,hk⟩ => hk ▸ (b i k).property,
          fun ht => ⟨(b i).symm ⟨t,ht⟩, congrArg Subtype.val ((b i).apply_symm_apply _)⟩⟩
      ext E
      rw [show (forget e).2 = ran (edge e) from rfl, mem_ran]
      simp_rw [he]
      exact ⟨fun ⟨k,hk⟩ => hk ▸ (p k).property,
        fun hE => ⟨p.symm ⟨E,hE⟩, congrArg Subtype.val (p.apply_symm_apply _)⟩⟩

/-- The factorial expression d(m,r) counts the unordered configurations themselves. -/
theorem card_configs (m r : ℕ) : ((configs m r).card : ℝ) = FaceCounts.multiplicity m r := by
  have h := sum_eq m r (fun _ => (1 : ℝ))
  by_cases fit : 4+2*r ≤ m
  · have e := positions (m := m) (r := r) (q := 4) (by omega)
    simpa [sample_eq e, Matchings.average_const] using h
  · simpa [FaceCounts.multiplicity, fit] using h

end
end BlockPermanents.RawFaceMeans
