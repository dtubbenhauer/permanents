import BlockPermanents.CycleClasses

/-! # Allocating the fixed points among odd cycles of any partition -/
namespace BlockPermanents.CycleAllocation
open CyclePlans CycleCoefficients CycleClasses
open scoped BigOperators

private theorem pieces {T : Type*} (f : T → Piece) (degree extra : T → ℕ) (t : List T)
    (h : ∀ x ∈ t, (f x).parts = [degree x] ∧ (f x).size = degree x + extra x) :
    planParts (t.map f) = t.map degree ∧
    planSize (t.map f) = (t.map degree).sum + (t.map extra).sum := by
  induction t with
  | nil => simp [planParts,planSize]
  | cons x t ih =>
    obtain ⟨hp,hs⟩ := h x (by simp)
    obtain ⟨rp,rs⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [planParts,planSize,List.map_cons,List.flatMap_cons,List.sum_cons] at rp rs ⊢
    rw [hp,hs,rp,rs]
    simp;omega

private theorem shares (O : List ℕ) (f : ℕ) (hp : 0 < O.length) :
    (O.zipIdx.map (fun t => f/O.length + if t.2<f%O.length then 1 else 0)).sum = f := by
  let a := O.length
  have hmap : O.zipIdx.map (fun t => if t.2<f%a then 1 else 0) =
      (List.range a).map (fun z => if z<f%a then 1 else 0) := by
    rw [List.range_eq_range',← List.zipIdx_map_snd 0 O,List.map_map]
    rfl
  have filter : (Finset.range a).filter (·<f%a) = Finset.range (f%a) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_range]
    have hm : f%a<a := Nat.mod_lt f hp
    omega
  have hf : ((List.range a).map (fun z => if z<f%a then 1 else 0)).sum = f%a := by
    rw [← List.sum_toFinset _ (List.nodup_range (n:=a))]
    rw [show (List.range a).toFinset=Finset.range a by ext z; simp]
    rw [Finset.sum_boole,filter,Finset.card_range,Nat.cast_id]
  change (O.zipIdx.map (fun t => f/a + if t.2<f%a then 1 else 0)).sum = f
  rw [List.sum_map_add,hmap,hf,List.map_const',List.sum_replicate,List.length_zipIdx]
  exact (Nat.div_add_mod f a)

private def evenL (l : List ℕ) := l.filter (fun d => d%2 == 0)
private def oddL (l : List ℕ) := l.filter (fun d => decide (1 < d) && d%2 == 1)

private theorem split (l : List ℕ) (pos : ∀ x ∈ l, 0<x) :
    (evenL l : Multiset ℕ) + ↑(oddL l) = ↑(l.filter (· > 1)) ∧
    (evenL l).sum + (oddL l).sum + l.count 1 = l.sum := by
  induction l with
  | nil => simp [evenL,oddL]
  | cons d l ih =>
    have hd := pos d (by simp)
    obtain ⟨hm,hs⟩ := ih (fun x hx => pos x (by simp [hx]))
    by_cases ho : d=1
    · subst d; simp [evenL,oddL] at hm hs ⊢;exact ⟨hm,by omega⟩
    by_cases he : d%2=0
    · have hn : d%2≠1 := by omega
      simp [evenL,oddL,he,show 1<d by omega,ho,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] at hm hs ⊢
      exact ⟨hm,hs⟩
    · have hv : d%2=1 := by omega
      simp [evenL,oddL,hv,show 1<d by omega,ho,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] at hm hs ⊢
      exact ⟨List.perm_middle.trans (hm.cons d),hs⟩

/-- The plan uses each ordinary label exactly once, preserves every nontrivial cycle length,
and apportions the fixed points by quotient and remainder. -/
theorem plan_data (l : List ℕ) (hl : ∀ x ∈ l, 0<x) :
    planSize (plan l) = l.sum ∧ (planParts (plan l) : Multiset ℕ) = ↑(l.filter (· > 1)) := by
  let E := evenL l
  let O := oddL l
  let s := l.count 1
  let a := O.length
  let f (d : ℕ) := Piece.even ((d-2)/2)
  let extra (t : ℕ × ℕ) := s/a + if t.2<s%a then 1 else 0
  let odd (t : ℕ × ℕ) := Piece.odd ((t.1-3)/2) (extra t)
  obtain ⟨ep,es⟩ := pieces f id (fun _ => 0) E (by
    intro d hd
    have he := (List.mem_filter.mp hd).2
    have hp := hl d (List.mem_filter.mp hd).1
    change (d%2==0)=true at he
    simp at he
    have eq : 2*((d-2)/2)+2 = d := by omega
    simp [f,Piece.parts,Piece.size,eq])
  obtain ⟨op,os⟩ := pieces odd Prod.fst extra O.zipIdx (by
    intro t ht
    have ho := (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx ht)).2
    change (decide (1<t.1) && t.1%2==1)=true at ho
    simp at ho
    have eq : 2*((t.1-3)/2)+3 = t.1 := by omega
    simp [odd,Piece.parts,Piece.size,eq])
  simp only [List.map_id_fun,id_eq,List.map_id,List.zipIdx_map_fst,List.map_const',List.sum_replicate,
    smul_zero,add_zero] at ep es op os
  obtain ⟨parts,total⟩ := split l hl
  change (E : Multiset ℕ) + ↑O = _ at parts
  change E.sum + O.sum + s = _ at total
  have both (v w : List Piece) :
      planSize (v++w) = planSize v + planSize w ∧ planParts (v++w)=planParts v ++ planParts w := by
    simp [planSize,planParts]
  change planSize (E.map f ++ O.zipIdx.map odd ++ (if a=0 then [Piece.fixed s] else [])) = _ ∧
    (planParts (E.map f ++ O.zipIdx.map odd ++ (if a=0 then [Piece.fixed s] else [])) : Multiset ℕ) = _
  simp only [(both _ _).1,(both _ _).2,es,ep,os,op]
  by_cases ha : a=0
  · have hO : O=[] := List.length_eq_zero_iff.mp ha
    simp [ha,hO,planSize,planParts,Piece.size,Piece.parts] at total parts ⊢
    exact ⟨total,parts⟩
  · have sh : (O.zipIdx.map extra).sum=s := shares O s (Nat.pos_of_ne_zero ha)
    simp [ha,sh,planSize,planParts,Nat.add_assoc] at total parts ⊢
    exact ⟨total,parts⟩

end BlockPermanents.CycleAllocation
