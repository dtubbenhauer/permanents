import BlockPermanents.OccupationBasis

/-! The multicolour coefficient of a routed cap, Appendix B. Every
positive cable has named cap slots. The independent clasp permutations
produce the distribution of their joint colour occupation. -/
namespace BlockPermanents.OccupationCoefficient
open OccupationSplit OccupationBasis
open scoped BigOperators
noncomputable section

abbrev Profile (d r : ℕ) := {a : Fin d → Fin (r+1) // ∑ j,(a j).val=r}

def profile {n d : ℕ} (x : Fin n → Fin d) (s : Finset (Fin n)) : Profile d s.card :=
  ⟨fun j => ⟨counts x s j,by have h := Finset.card_filter_le s (fun i => x i=j); exact Nat.lt_succ_of_le h⟩,
   sum_counts x s⟩

private theorem profile_eq {n d : ℕ} (x : Fin n → Fin d) (s : Finset (Fin n)) (a : Profile d s.card) :
    profile x s=a ↔ counts x s=fun j => (a.val j).val := by
  constructor
  · intro h;exact funext fun j => congrArg (fun b : Profile d s.card => (b.val j).val) h
  · intro h;apply Subtype.ext;funext j;apply Fin.ext;exact congrFun h j

def ratio {d n : ℕ} (x : Fin n → Fin d) (s : Finset (Fin n)) (a : Profile d s.card) : ℚ :=
  ((∏ j,(occ x j).choose (a.val j).val : ℕ):ℚ) / n.choose s.card

private theorem one_cable {d n : ℕ} (x : Fin n → Fin d) (s : Finset (Fin n)) (a : Profile d s.card) :
    (∑ p : Equiv.Perm (Fin n), if profile (x ∘ p) s = a then (1:ℚ) else 0) / n.factorial =
      ratio x s a := by
  simp_rw [profile_eq]
  exact perm_probability x s _ a.prop

theorem independent {H : Type*} [Fintype H] [DecidableEq H] {A B : H → Type*}
    [∀ i,Fintype (A i)] [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]
    (f : (i : H) → A i → B i) (g : ((i : H) → B i) → ℚ) :
    (∑ p : (i : H)→A i, g (fun i => f i (p i))) / ∏ i,(Fintype.card (A i):ℚ) =
    ∑ b : (i : H)→B i, g b *
      ∏ i, ((∑ p : A i, if f i p=b i then (1:ℚ) else 0)/(Fintype.card (A i):ℚ)) := by
  classical
  simp only [Finset.prod_div_distrib,← mul_div_assoc,← Finset.sum_div]
  congr 1
  simp_rw [Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  let v := fun i => f i (p i)
  have ind (b : (i : H)→B i) : (∏ i,if f i (p i)=b i then (1:ℚ) else 0) =
      if v=b then 1 else 0 := by
    by_cases hb : v=b
    · subst b;simp [v]
    · have h : ∃ i,v i ≠ b i := not_forall.mp (fun he => hb (funext he))
      obtain ⟨i,hi⟩ := h
      rw [if_neg hb,Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
  simp only [ind,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rfl

variable {H : Type*} [Fintype H] [DecidableEq H] {d : ℕ} {n : H→ℕ}
def capOccupation (s : (i : H) → Finset (Fin (n i))) (a : (i : H) → Profile d (s i).card)
    (j : Fin d) := ∑ i, ((a i).val j).val

def assignments (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (b : Fin d→ℕ) : ℚ :=
  ∑ a : (i : H) → Profile d (s i).card,
    if capOccupation s a=b then ∏ i,ratio (x i) (s i) (a i) else 0

/-- Fraction of all independent positive cable permutations producing
the marked occupation. Impossible binomial choices contribute zero. -/
theorem positive_splits (x : (i : H) → Fin (n i) → Fin d)
    (s : (i : H) → Finset (Fin (n i))) (b : Fin d→ℕ) :
    (∑ p : (i : H)→Equiv.Perm (Fin (n i)),
      if capOccupation s (fun i => profile (x i ∘ p i) (s i))=b then (1:ℚ) else 0) /
      ∏ i,((n i).factorial : ℚ) = assignments x s b := by
  have h := independent (fun i (p : Equiv.Perm (Fin (n i))) => profile (x i ∘ p) (s i))
    (fun a => if capOccupation s a=b then (1:ℚ) else 0)
  simpa only [Fintype.card_perm,Fintype.card_fin,one_cable,ite_mul,one_mul,zero_mul,assignments] using h
/-- Capped slots, kept in their cable and within-cable order. -/
abbrev Ports (s : (i : H) → Finset (Fin (n i))) := Σ i, (s i : Type)
def survivors (s : (i : H) → Finset (Fin (n i))) := fun i => (s i)ᶜ
def read (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (p : (i : H) → Equiv.Perm (Fin (n i))) (a : Ports s) : Fin d := x a.1 (p a.1 a.2.val)

omit [DecidableEq H] in
private theorem read_occ (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (p : (i : H) → Equiv.Perm (Fin (n i))) (j : Fin d) :
    occ (read x s p) j = ∑ i, counts (x i ∘ p i) (s i) j := by
  simp only [occ,counts,Finset.card_filter,Fintype.sum_sigma,read]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_coe_sort (s i) (fun a => if x i (p i a)=j then (1:ℕ) else 0)

omit [DecidableEq H] in
private theorem total_counts (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (p : (i : H) → Equiv.Perm (Fin (n i))) (j : Fin d) :
    occ (read x (survivors s) p) j + occ (read x s p) j = ∑ i,occ (x i) j := by
  rw [read_occ,read_occ,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [survivors,occ,counts,Finset.card_filter]
  rw [add_comm,Finset.sum_add_sum_compl]
  exact Equiv.sum_comp (p i) (fun a => if x i a=j then (1:ℕ) else 0)

/-- Coordinate of the routed contraction of the normalized occupation
vectors. Each positive cable is averaged independently. The marked word
is paired at its cap slots, and the survivors pass through the output clasp. -/
def routed (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (b : Ports s→Fin d) (o : Ports (survivors s)→Fin d) : ℚ :=
  (∑ p : (i : H)→Equiv.Perm (Fin (n i)),
    kernel b (read x s p) * kernel o (read x (survivors s) p)) / ∏ i,((n i).factorial : ℚ)

/-- The manuscript's D coefficient, including the norm of the marked occupation. -/
def Dcoeff (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (b : Ports s → Fin d) : ℚ := weight (occ b) (Fintype.card (Ports s)) * assignments x s (occ b)

/-- Evaluation of the actual permutation-word contraction on all output words.
Here the occupation of u is the paper's surviving occupation n. -/
theorem routed_eq (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (b : Ports s→ Fin d) (u : Ports (survivors s)→Fin d)
    (balance : ∀ j, ∑ i,occ (x i) j = occ u j + occ b j) (o : Ports (survivors s)→Fin d) :
    routed x s b o = Dcoeff x s b * kernel o u := by
  let value := weight (occ b) (Fintype.card (Ports s)) * kernel o u
  have localTerm (p : (i : H)→Equiv.Perm (Fin (n i))) :
      kernel b (read x s p) * kernel o (read x (survivors s) p) =
      (if capOccupation s (fun i => profile (x i ∘ p i) (s i))=occ b then (1:ℚ) else 0) * value := by
    have hvar : capOccupation s (fun i => profile (x i ∘ p i) (s i)) = occ (read x s p) :=
      funext fun j => (read_occ x s p j).symm
    rw [hvar]
    by_cases hcap : occ (read x s p)=occ b
    · have ho : occ (read x (survivors s) p)=occ u := by
        funext j
        have h := (total_counts x s p j).trans (balance j)
        rw [hcap] at h
        omega
      simp only [if_pos hcap,one_mul,value,kernel_eq,ho,hcap,if_true]
    · simp [kernel_eq,hcap,Ne.symm hcap]
  simp only [routed,localTerm,← Finset.sum_mul,Dcoeff]
  rw [← positive_splits x s (occ b)]
  unfold value
  ring

/-- The same entry vanishes unless the input and output occupations balance. -/
theorem routed_entry (x : (i : H) → Fin (n i) → Fin d) (s : (i : H) → Finset (Fin (n i)))
    (b : Ports s→ Fin d) (o : Ports (survivors s)→Fin d) :
    routed x s b o = if ∀ j,∑ i,occ (x i) j = occ o j+occ b j
      then Dcoeff x s b * weight (occ o) (Fintype.card (Ports (survivors s))) else 0 := by
  classical
  split_ifs with h
  · simpa only [kernel_eq,if_true] using routed_eq x s b o h o
  · unfold routed
    rw [Finset.sum_eq_zero,zero_div]
    intro p _
    rw [kernel_eq,kernel_eq]
    split_ifs with h₁ h₂ <;> try simp
    exfalso
    exact h (fun j => by rw [← total_counts x s p j,← h₁,← h₂])

end
end BlockPermanents.OccupationCoefficient
