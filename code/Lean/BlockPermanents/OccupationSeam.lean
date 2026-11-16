import BlockPermanents.OccupationCoefficient

/-! The occupation Gram seam in the ordinary orthonormal word coordinates.
Quotienting independent inputs by their colour occupations supplies precisely
the inverse input norm factors in the manuscript. -/
namespace BlockPermanents.OccupationSeam
open OccupationBasis OccupationCoefficient
open scoped BigOperators
noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Distinct occupations available on a cable, with every word multiplicity included
only during the subsequent contraction. -/
def classes (I D : Type*) [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D] : Finset (D → ℕ) :=
  Finset.univ.image (occ (I:=I) (D:=D))

abbrev Class (I D : Type*) [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D] := ↥(classes I D)

def classify {I : Type*} [Fintype I] [DecidableEq I] (x : I → D) : Class I D :=
  ⟨occ x, Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩

private theorem multiplicity {I : Type*} [Fintype I] [DecidableEq I] (a : Class I D) :
    (∑ w : I → D,if classify w = a then (1:ℚ) else 0) =
      (weight a.val (Fintype.card I))⁻¹ := by
  obtain ⟨z,_,hz⟩ := Finset.mem_image.mp a.prop
  have he (w : I → D) : kernel w z =
      (if classify w=a then (1:ℚ) else 0) * weight a.val (Fintype.card I) := by
    rw [kernel_eq,hz]
    have hi : classify w=a ↔ occ w=a.val := Subtype.ext_iff
    by_cases h : classify w=a
    · simp [h,hi.mp h]
    · have hh : occ w ≠ a.val := fun he => h (hi.mpr he)
      simp [h,hh]
  have h := column_sum z
  simp only [he,← Finset.sum_mul] at h
  exact (eq_inv_of_mul_eq_one_left h)

private theorem class_sum {I : Type*} [Fintype I] [DecidableEq I] (f : Class I D→ℚ) :
    ∑ z : I→D, f (classify z) =
    ∑ a, f a / weight a.val (Fintype.card I) := by
  calc
    _ = ∑ z : I→D, ∑ a : Class I D, f a*(if classify z=a then 1 else 0) := by
      simp [mul_ite]
    _ = ∑ a : Class I D, f a * ∑ z : I→D, (if classify z=a then 1 else 0) := by
      rw [Finset.sum_comm];simp only [Finset.mul_sum]
    _ = _ := by simp only [multiplicity,div_eq_mul_inv]

private theorem class_product_sum {H : Type*} [Fintype H] [DecidableEq H]
    {T : H→Type*} [∀ i,Fintype (T i)] [∀ i,DecidableEq (T i)]
    (f : ((i:H)→Class (T i) D) → ℚ) :
    (∑ x : (i:H) → T i → D, f (fun i => classify (x i))) =
      ∑ a : (i:H)→Class (T i) D, f a / ∏ i,weight (a i).val (Fintype.card (T i)) := by
  classical
  have h := independent (fun i (w:T i →D) => classify w) f
  simp only [multiplicity,Finset.prod_div_distrib,← mul_div_assoc,← Finset.sum_div] at h
  by_cases hn : (∏ i,(Fintype.card (T i→D):ℚ))=0
  · have hz : IsEmpty ((i:H)→T i→D) := by
      apply Fintype.card_eq_zero_iff.mp
      have hc : (Fintype.card ((i:H)→T i→D):ℚ) = 0 := by rwa [Fintype.card_pi,Nat.cast_prod]
      exact_mod_cast hc
    letI := hz
    have hz' : IsEmpty ((i:H)→Class (T i) D) := ⟨fun a => hz.false
      (fun i => Classical.choose (Finset.mem_image.mp (a i).prop))⟩
    letI := hz'
    simp
  · have he := (div_left_inj' hn).mp h
    simpa only [Finset.prod_inv_distrib,div_eq_mul_inv] using he

omit [Fintype D] in
theorem occ_equiv {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) (w : J → D) :
    occ (w ∘ e) = occ w := by
  funext j
  simp only [occ,OccupationSplit.counts,Finset.card_filter]
  exact e.sum_comp (fun t => if w t=j then (1:ℕ) else 0)
variable {H J Z : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Fintype Z] [DecidableEq Z] {d : ℕ} {n : H→ℕ}

/-- The attachment of the cap strands to the marked cable, and of the
uncontracted strands to the output cable. The same external slot types
are used to compare different routings. -/
structure Route (n : H→ℕ) (J Z : Type*) where
  slots : (i : H) → Finset (Fin (n i))
  marked : Ports slots ≃ J
  output : Ports (survivors slots) ≃ Z

abbrev Atom (n : H→ℕ) (d : ℕ) := (i:H)→Fin (n i)→Fin d
abbrev Data (n : H→ℕ) (d : ℕ) := (i:H)→Class (Fin (n i)) (Fin d)

def value (r : Route n J Z) (a : Data n d) (b : Class J (Fin d)) : ℚ :=
  weight b.val (Fintype.card J) *
    ∑ v : (i:H)→Profile d (r.slots i).card, if capOccupation r.slots v=b.val then
      ∏ i, ((∏ j, ((a i).val j).choose (((v i).val j).val) : ℕ):ℚ) /
        (n i).choose (r.slots i).card else 0

/-- A routed cap as an actual matrix in the standard word bases.
The word columns include the individual cable clasps. -/
def operator (r : Route n J Z) : Matrix (Z→Fin d) (Atom n d × (J→Fin d)) ℚ :=
  fun w x => routed x.1 r.slots (x.2 ∘ r.marked) (w ∘ r.output)

def balances (a : Data n d) (b : Class J (Fin d)) (w : Z → Fin d) : Prop :=
  ∀ j, ∑ i,(a i).val j = occ w j + b.val j

instance (a : Data n d) (b : Class J (Fin d)) (w : Z → Fin d) : Decidable (balances a b w) :=
  inferInstanceAs (Decidable (∀ j, ∑ i,(a i).val j=occ w j+b.val j))

omit [DecidableEq Z] in
private theorem operator_entry (r : Route n J Z) (x : Atom n d) (b : J→Fin d) (o : Z→Fin d) :
    operator r o (x,b) =
      if balances (fun i => classify (x i)) (classify b) o then
        value r (fun i => classify (x i)) (classify b) * weight (occ o) (Fintype.card Z) else 0 := by
  simp only [operator,routed_entry,occ_equiv,Dcoeff,assignments,ratio,value,
    Fintype.card_congr r.marked,Fintype.card_congr r.output,balances,classify]

/-- Diagonal entry of the actual glued word matrix, divided by the squared
norm of the output occupation as in the manuscript. Each orthonormal word
at the input seam appears exactly once. -/
def gram (r t : Route n J Z) (o : Z → Fin d) : ℚ :=
  (operator r * (operator t).transpose : Matrix (Z→Fin d) (Z→Fin d) ℚ) o o /
    weight (occ o) (Fintype.card Z)

private theorem aggregate (f : Data n d → Class J (Fin d) → ℚ) :
    (∑ x : Atom n d,∑ b : J→Fin d, f (fun i => classify (x i)) (classify b)) =
      ∑ a : Data n d,∑ b : Class J (Fin d), f a b /
        (weight b.val (Fintype.card J)*∏ i,weight (a i).val (n i)) := by
  simp_rw [class_sum]
  have h := class_product_sum (fun a : Data n d => ∑ b : Class J (Fin d),
    f a b / weight b.val (Fintype.card J))
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_div,div_div,Fintype.card_fin]

omit [DecidableEq Z] in
/-- Appendix B.1, the weighted seam formula. The sum is over distinct
positive and marked occupations on the common boundary of the two caps. -/
theorem gram_eq (r t : Route n J Z) (o : Z → Fin d) :
    gram r t o = weight (occ o) (Fintype.card Z) *
      ∑ a : Data n d, ∑ b : Class J (Fin d),
        (if balances a b o then value r a b * value t a b else 0) /
        (weight b.val (Fintype.card J)*∏ i,weight (a i).val (n i)) := by
  let w := weight (occ o) (Fintype.card Z)
  let f (a : Data n d) (b : Class J (Fin d)) := if balances a b o then value r a b*value t a b else 0
  have each (x : Atom n d) (b : J→Fin d) : operator r o (x,b) * operator t o (x,b) =
      w^2 * f (fun i=>classify (x i)) (classify b) := by
    rw [operator_entry,operator_entry]
    dsimp only [f,w]
    split_ifs <;> ring
  simp only [gram,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,each,← Finset.mul_sum]
  rw [aggregate f]
  change w^2*_ / w = w*_
  have hw : w≠0 := (weight_pos _ _).ne'
  field_simp
  ring
def allowed (S : Finset (Fin d)) (b : Fin d→ℕ) : Prop := ∀ j,j∉S → b j=0
instance (S : Finset (Fin d)) (b : Fin d→ℕ) : Decidable (allowed S b) :=
  inferInstanceAs (Decidable (∀ j,j∉S → b j=0))

omit [DecidableEq J] in
theorem allowed_word (S : Finset (Fin d)) (w : J → Fin d) :
    allowed S (occ w) ↔ ∀ i,w i∈S := by
  constructor
  · intro h i
    by_contra hi
    have he := h (w i) hi
    have hp : 0 < (Finset.univ.filter (fun j => w j=w i)).card :=
      Finset.card_pos.mpr ⟨i,by simp⟩
    exact hp.ne' he
  · intro h j hj
    apply Finset.card_eq_zero.mpr
    simp only [Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies]
    exact fun i he => hj (he ▸ h i)

/-- Extend by zero on any marked word which uses an excluded colour. -/
def supportedOperator (S : Finset (Fin d)) (r : Route n J Z) :
    Matrix (Z→Fin d) (Atom n d × (J→Fin d)) ℚ := fun w x =>
  if allowed S (occ x.2) then operator r w x else 0

def glued (S : Finset (Fin d)) (r t : Route n J Z) :
    Matrix (Z→Fin d) (Z→Fin d) ℚ := supportedOperator S r * (supportedOperator S t).transpose

/-- Normalized matrix element on the actual output occupation vector. -/
def tested (S : Finset (Fin d)) (r t : Route n J Z) (o : Z→Fin d) : ℚ :=
  (∑ a,∑ b,kernel a o * glued S r t a b * kernel b o) / weight (occ o) (Fintype.card Z)

omit [DecidableEq Z] in
private theorem same_row {u v : Z→Fin d} (h : occ u=occ v) (S : Finset (Fin d))
    (r : Route n J Z) (i : Atom n d × (J→Fin d)) :
    supportedOperator S r u i=supportedOperator S r v i := by
  obtain ⟨x,b⟩ := i
  simp only [supportedOperator,operator_entry,balances,h]

private theorem tested_entry (S : Finset (Fin d)) (r t : Route n J Z) (o : Z→Fin d) :
    tested S r t o = glued S r t o o / weight (occ o) (Fintype.card Z) := by
  unfold tested
  congr 1
  have he (a b : Z→Fin d) : kernel a o * glued S r t a b * kernel b o =
      kernel a o * (kernel b o * glued S r t o o) := by
    by_cases ha : occ a=occ o
    · by_cases hb : occ b=occ o
      · have hg : glued S r t a b=glued S r t o o := by
          simp only [glued,Matrix.mul_apply,Matrix.transpose_apply, same_row ha,same_row hb]
        rw [hg];ring
      · simp [kernel_eq,hb]
    · simp [kernel_eq,ha]
  simp only [he,← Finset.mul_sum,← Finset.sum_mul,column_sum,one_mul]

/-- Gram seam on a chosen marked coordinate support. The value uses the
norms of all three kinds of occupation: output, marked, and ordinary cables. -/
theorem supported_gram (S : Finset (Fin d)) (r t : Route n J Z) (o : Z→Fin d) :
    tested S r t o = weight (occ o) (Fintype.card Z) *
      ∑ a : Data n d, ∑ b : Class J (Fin d),
        (if allowed S b.val ∧ balances a b o then value r a b * value t a b else 0) /
        (weight b.val (Fintype.card J)*∏ i,weight (a i).val (n i)) := by
  let w := weight (occ o) (Fintype.card Z)
  let f (a : Data n d) (b : Class J (Fin d)) :=
    if allowed S b.val ∧ balances a b o then value r a b*value t a b else 0
  have each (x : Atom n d) (b : J→Fin d) :
      supportedOperator S r o (x,b) * supportedOperator S t o (x,b) =
        w^2 * f (fun i=>classify (x i)) (classify b) := by
    simp only [supportedOperator,operator_entry]
    change _=w^2*(if allowed S (occ b) ∧ balances (fun i=>classify (x i)) (classify b) o
      then value r (fun i=>classify (x i)) (classify b)*value t (fun i=>classify (x i)) (classify b) else 0)
    by_cases a : allowed S (occ b) <;> by_cases z : balances (fun i=>classify (x i)) (classify b) o <;>
      simp [a,z,w]
    ring
  rw [tested_entry]
  simp only [glued,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,each,← Finset.mul_sum]
  rw [aggregate f]
  change w^2*_ / w = w*_
  have hw : w≠0 := (weight_pos _ _).ne'
  field_simp
  ring

end
end BlockPermanents.OccupationSeam
