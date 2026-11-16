import BlockPermanents.RoutingOperators
import Mathlib.GroupTheory.Perm.Finite

/-! # Inserting or removing one whole spectator packet -/
namespace BlockPermanents.RoutingFibres
open Routings Equiv
open scoped BigOperators
noncomputable section

variable {n k : ℕ}

def layout (i : Fin (n+1)) : Slot (n+1) k ≃ (Fin k ⊕ Slot n k) where
  toFun x := ((finSuccEquiv' i) x.1).elim (.inl x.2) (fun a => .inr (a,x.2))
  invFun := Sum.elim (fun t => (i,t)) (fun y => (i.succAbove y.1,y.2))
  left_inv := by
    rintro ⟨a,t⟩
    by_cases h : a=i
    · subst a;simp
    · obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq h
      simp
  right_inv := by rintro (t|⟨a,t⟩) <;> simp

@[simp] theorem layout_at (i : Fin (n+1)) (t : Fin k) : layout i (i,t) = .inl t := by simp [layout]
@[simp] theorem layout_old (i : Fin (n+1)) (l : Fin n) (t : Fin k) :
    layout i (i.succAbove l,t) = .inr (l,t) := by simp [layout]

def insertWire (i j : Fin (n+1)) (u : Perm (Fin k)) (p : Wire n k) : Wire (n+1) k :=
  (layout i).trans ((u.sumCongr p).trans (layout j).symm)

@[simp] theorem insert_at (i j : Fin (n+1)) (u : Perm (Fin k)) (p : Wire n k) (t : Fin k) :
    insertWire i j u p (i,t) = (j,u t) := by simp [insertWire,layout]
@[simp] theorem insert_old (i j : Fin (n+1)) (u : Perm (Fin k)) (p : Wire n k) (l : Fin n) (t : Fin k) :
    insertWire i j u p (i.succAbove l,t) = (j.succAbove (p (l,t)).1,(p (l,t)).2) := by simp [insertWire,layout]

theorem edge_iff {m : ℕ} (q : Wire m k) (i j : Fin m) :
    (table q).entries i j = k ↔ ∀ t, (q (i,t)).1=j := by
  change Fintype.card {t : Fin k // (q (i,t)).1=j} = k ↔ _
  rw [Fintype.card_subtype]
  simpa only [Finset.card_univ,Fintype.card_fin,Finset.mem_univ,true_implies] using
    (Finset.card_filter_eq_iff (s := Finset.univ) (p := fun t : Fin k => (q (i,t)).1=j))

/-- The full fiber of a forced input-output edge consists independently
of one permutation of its k strands and one permutation of the remaining
nk strands. Both endpoint labels are arbitrary. -/
def edgeFibre (i j : Fin (n+1)) :
    Perm (Fin k) × Wire n k ≃ {q : Wire (n+1) k // (table q).entries i j = k} := by
  let f := fun y : Perm (Fin k) × Wire n k =>
    (⟨insertWire i j y.1 y.2, (edge_iff _ i j).mpr (fun t => by simp)⟩ :
      {q : Wire (n+1) k // (table q).entries i j=k})
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨a,p⟩ ⟨b,q⟩ he
    apply Prod.ext
    · apply Equiv.ext;intro t
      have h := congrArg (fun z : {q : Wire (n+1) k // (table q).entries i j=k} => z.val (i,t)) he
      simpa [f] using congrArg Prod.snd h
    · apply Equiv.ext;rintro ⟨l,t⟩
      have h := congrArg (fun z : {q : Wire (n+1) k // (table q).entries i j=k} => z.val (i.succAbove l,t)) he
      simp [f] at h
      exact Prod.ext h.1 h.2
  · rintro ⟨q,hq⟩
    let e := (layout i).symm.trans (q.trans (layout j))
    have hm : Set.MapsTo e (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨t,rfl⟩
      change layout j (q (i,t)) ∈ _
      have hi : q (i,t)=(j,(q (i,t)).2) := Prod.ext ((edge_iff q i j).mp hq t) rfl
      rw [hi,layout_at]; exact ⟨_,rfl⟩
    obtain ⟨y,hy⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    refine ⟨y,Subtype.ext (Equiv.ext fun x => ?_)⟩
    change (layout j).symm ((y.1.sumCongr y.2) (layout i x)) = q x
    change y.1.sumCongr y.2 = e at hy
    rw [hy]; simp [e]

theorem split_mem {m k : ℕ} (M : Routing m k) (i : Fin m) :
    i ∈ M.splitInputs ↔ ∀ j, M.entries i j≠k := by
  simp only [Routing.splitInputs,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro h j he;exact h ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  · intro h;rintro ⟨⟨i',j⟩,he,rfl⟩;exact h j (Finset.mem_filter.mp he).2

/-- Removal of the prescribed edge preserves the set of split remaining
inputs, up to the canonical insertion of the skipped label. -/
theorem split_insert (i j : Fin (n+1)) (u : Perm (Fin k)) (p : Wire n k) (hk : 0 < k) :
    (table (insertWire i j u p)).splitInputs = (table p).splitInputs.map i.succAboveEmb := by
  ext a
  by_cases ha : a=i
  · subst a
    have hf := (edge_iff (insertWire i j u p) i j).mpr (fun t => by simp)
    simp [split_mem,Fin.succAbove_ne];exact ⟨j,hf⟩
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq ha
    rw [Finset.mem_map]
    have mem : (∃ a ∈ (table p).splitInputs, i.succAboveEmb a = i.succAbove l) ↔ l ∈ (table p).splitInputs := by simp
    rw [mem,split_mem,split_mem]
    have old (b : Fin n) : (table (insertWire i j u p)).entries (i.succAbove l) (j.succAbove b) =
        (table p).entries l b := by
      change Fintype.card {t : Fin k // (insertWire i j u p (i.succAbove l,t)).1=j.succAbove b} = Fintype.card {t : Fin k // (p (l,t)).1=b}
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro t
      change (insertWire i j u p (i.succAbove l,t)).1=j.succAbove b ↔ _
      rw [insert_old]; exact Fin.succAbove_right_injective.eq_iff
    constructor
    · intro h b;exact old b ▸ h (j.succAbove b)
    · intro h b
      by_cases hb : b=j
      · subst b
        intro he
        have ht := (edge_iff _ _ _).mp he (⟨0,hk⟩ : Fin k)
        rw [insert_old] at ht;exact Fin.succAbove_ne _ _ ht
      · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq hb
        rw [old];exact h b

theorem split_count_insert (i j : Fin (n+1)) (u : Perm (Fin k)) (p : Wire n k) (hk : 0<k) :
    (table (insertWire i j u p)).splitInputs.card = (table p).splitInputs.card := by rw [split_insert _ _ _ _ hk,Finset.card_map]

end
end BlockPermanents.RoutingFibres
