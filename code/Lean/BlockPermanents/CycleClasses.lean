import BlockPermanents.CycleTen

/-! # Positive partitions and the multiplicities of their permutation classes -/
namespace BlockPermanents.CycleClasses
open CycleCoefficients CycleTen
open scoped BigOperators

private def raise : List ℕ → Option (List ℕ)
  | [] => none
  | a::t => some ((a+1)::t)

theorem composition_data {m : ℕ} {l : List ℕ} (h : l ∈ compositions m) :
    (∀ x ∈ l, 0<x) ∧ l.sum=m := by
  induction m generalizing l with
  | zero => simp [compositions] at h; subst l; simp
  | succ m ih =>
    change l ∈ (compositions m).map (1 :: ·) ++ (compositions m).filterMap raise at h
    rcases List.mem_append.mp h with h|h
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      obtain ⟨hp,hs⟩ := ih ht
      simp [hs,Nat.add_comm];exact hp
    · obtain ⟨t,ht,he⟩ := List.mem_filterMap.mp h
      obtain ⟨hp,hs⟩ := ih ht
      cases t with
      | nil => simp [raise] at he
      | cons a t =>
        simp [raise] at he
        subst l
        have sp : ∀ x ∈ t, 0<x := fun x hx => hp x (by simp [hx])
        simp only [List.sum_cons] at hs
        exact ⟨by simp;exact sp,by simp [List.sum_cons];omega⟩

theorem partition_data {m : ℕ} {l : List ℕ} (h : l ∈ partitions m) :
    (∀ x ∈ l, 0<x) ∧ l.sum=m :=
  composition_data (List.mem_filter.mp h).1

theorem compositions_nodup (m : ℕ) : (compositions m).Nodup := by
  induction m with
  | zero => simp [compositions]
  | succ m ih =>
    change ((compositions m).map (1 :: ·) ++ (compositions m).filterMap raise).Nodup
    apply List.nodup_append.mpr
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2),ih.filterMap ?_,?_⟩
    · intro a a' b h h'
      cases a <;> cases a' <;> simp [raise] at h h' ⊢
      grind
    · apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
      obtain ⟨u,hu,he⟩ := List.mem_filterMap.mp hy
      cases u with
      | nil => simp [raise] at he
      | cons a u =>
        have h := (composition_data hu).1 a (by simp)
        simp [raise] at he
        omega

theorem partitions_nodup (m : ℕ) : (partitions m).Nodup := (compositions_nodup m).filter _

private theorem erase_loop (l b : List ℕ) (hb : b.Nodup) :
    (List.eraseDups.loop l b).Nodup ∧
    (List.eraseDups.loop l b).toFinset=l.toFinset ∪ b.toFinset := by
  induction l generalizing b with
  | nil => simp [List.eraseDups.loop,hb]
  | cons a t ih =>
    by_cases h : a ∈ b
    · simp only [List.eraseDups.loop,show b.elem a = true by simpa using h,Bool.true_eq]
      refine ⟨(ih b hb).1, (ih b hb).2.trans ?_⟩
      ext x; simp; grind
    · simp only [List.eraseDups.loop,show b.elem a = false by simpa using h,Bool.false_eq]
      have he := ih (a::b) (by simp [hb,h])
      refine ⟨he.1,he.2.trans ?_⟩
      ext x; simp

private theorem denominator (l : List ℕ) :
    (l.eraseDups.map (fun d => d^(l.count d) * (l.count d).factorial)).prod =
      l.prod * ∏ d ∈ l.toFinset, (l.count d).factorial := by
  obtain ⟨hn,hs⟩ := erase_loop l [] (by simp)
  change l.eraseDups.Nodup at hn
  change l.eraseDups.toFinset=l.toFinset ∪ ([]:List ℕ).toFinset at hs
  simp only [List.toFinset_nil,Finset.union_empty] at hs
  rw [← List.prod_toFinset _ hn,hs,Finset.prod_mul_distrib,← Finset.prod_list_count]

theorem class_count {m : ℕ} {l : List ℕ} (hl : l ∈ partitions m) :
    classCard m l = classSize m l := by
  classical
  obtain ⟨pos,sm⟩ := partition_data hl
  let S := nontriv l
  let L := (l : Multiset ℕ)
  have filt : S = L.filter (1 < ·) := by simp [S,L,nontriv]
  have split : S + Multiset.replicate (l.count 1) 1 = L := by
    have h := Multiset.filter_add_not (1 < ·) L
    have hf : L.filter (fun x => ¬1<x) = L.filter (·=1) :=
      Multiset.filter_congr (fun x hx => by have := pos x hx;omega)
    rw [hf,Multiset.filter_eq',Multiset.coe_count] at h
    exact filt ▸ h
  have hs : S.sum + l.count 1 = m := by
    have h := congrArg Multiset.sum split
    simpa [L,sm] using h
  have hprod : S.prod=l.prod := by
    have h := congrArg Multiset.prod split
    simpa [L] using h
  have hp (d : ℕ) (hd : d ∈ S) : 2 ≤ d := (Multiset.mem_filter.mp (filt ▸ hd)).2
  have hc (d : ℕ) (hd : d ∈ S.toFinset) : S.count d=l.count d := by
    rw [filt,Multiset.count_filter_of_pos (p:=fun x => 1<x) (hp d (Multiset.mem_toFinset.mp hd))]
    exact Multiset.coe_count d l
  have he : S.toFinset = l.toFinset.erase 1 := by
    ext d; rw [Multiset.mem_toFinset,filt,Multiset.mem_filter,Finset.mem_erase,List.mem_toFinset]
    change (d ∈ l ∧ 1<d) ↔ (d≠1 ∧ d ∈ l)
    constructor
    · rintro ⟨hm,h⟩;exact ⟨by omega,hm⟩
    · rintro ⟨h,hm⟩;exact ⟨hm,by have := pos d hm;omega⟩
  have hf : (l.count 1).factorial * ∏ d ∈ S.toFinset,(S.count d).factorial =
      ∏ d ∈ l.toFinset, (l.count d).factorial := by
    rw [Finset.prod_congr rfl (fun d hd => congrArg Nat.factorial (hc d hd)),he]
    by_cases h : 1 ∈ l.toFinset
    · exact Finset.mul_prod_erase _ (fun d => (l.count d).factorial) h
    · have one : l.count 1=0 := List.count_eq_zero.mpr (fun he => h (List.mem_toFinset.mpr he))
      simp [one,Finset.erase_eq_of_not_mem h]
  change (if S.sum ≤ m ∧ ∀ a ∈ S, 2≤a then _ else _) = _
  rw [if_pos ⟨by omega,hp⟩, classSize,denominator]
  change m.factorial / ((m - S.sum).factorial*S.prod*_) = _
  rw [show m-S.sum=l.count 1 by omega,hprod,← hf]
  ring_nf
  rfl

end BlockPermanents.CycleClasses
