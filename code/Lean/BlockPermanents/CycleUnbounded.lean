import BlockPermanents.CyclePlans

/-! # Consecutive cycle cuts of every length in Appendix A -/
namespace BlockPermanents.CycleUnbounded
open CycleMatching CyclePolynomial CycleCuts CyclePlans
open scoped BigOperators
noncomputable section

/-- An ordinary step, the wrapping step, and the fixed remainder of a consecutive cycle. -/
private theorem step {d s : ℕ} (hd : 2 ≤ d) (i : Fin (d+s)) :
    (localPerm d s i).val =
      if i.val+1<d then i.val+1 else if i.val<d then 0 else i.val := by
  haveI : NeZero (d+s) := ⟨by omega⟩
  rw [localPerm,dif_pos (by omega)]
  split_ifs with h h'
  · apply Fin.coe_cycleRange_of_lt
    change i.val < d-1;omega
  · rw [Fin.cycleRange_of_eq (by apply Fin.ext; change i.val=d-1;omega)]
    rfl
  · rw [Fin.cycleRange_of_gt (by change d - 1 < i.val; omega)]

private def inside {d s : ℕ} : Fin d ↪ Fin (d+s) :=
  ⟨Fin.castAdd s,fun _ _ h => Fin.ext (congrArg (Fin.val (n:=d+s)) h)⟩

private theorem wires {d s : ℕ} (hd : 2 ≤ d) :
    wiring (localPerm d s) = Finset.univ.val.map (fun i : Fin d =>
      (localPerm d s (inside i),inside i)) := by
  have h : Finset.univ.filter (fun i => localPerm d s i ≠ i) =
      Finset.univ.map (inside (d:=d) (s:=s)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    have eq : localPerm d s i ≠ i ↔ i.val<d := by
      rw [ne_eq,Fin.ext_iff,step hd];split_ifs <;> omega
    rw [eq]
    constructor
    · intro h
      exact ⟨⟨_,h⟩,rfl⟩
    · rintro ⟨j,rfl⟩;exact j.isLt
  simp only [wiring,h,Finset.map_val,Multiset.map_map];rfl

private theorem chart {I : Type} [Fintype I] {d s} (hd : 2≤d) (f : I → Fin d)
    (hi : Function.Injective f) (hc : Fintype.card I=d) :
    wiring (localPerm d s) = Finset.univ.val.map (fun i : I =>
      (localPerm d s (inside (f i)),inside (f i))) := by
  have bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hi,by simpa using hc⟩
  have b := (Multiset.bijective_iff_map_univ_eq_univ f).mp bij
  rw [wires hd,← b,Multiset.map_map];rfl

private theorem chart_sum {I J T : Type} [Fintype I] [Fintype J] (f : I⊕J → T) :
    Finset.univ.val.map f = Finset.univ.val.map (fun i => f (.inl i)) +
      Finset.univ.val.map (fun i => f (.inr i)) :=
  Multiset.map_disjSum f

private def upper {r m : ℕ} (h : 2*r ≤ m) : Fin r × Fin 2 ↪ Fin m where
  toFun p := ⟨2*p.1.val+p.2.val,by have := p.1.isLt;have := p.2.isLt;omega⟩
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h'
    have e := congrArg Fin.val h'
    change 2*i.val+a.val=2*j.val+b.val at e
    have := a.isLt;have := b.isLt
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

private def lower {d s r : ℕ} (h : 2*r ≤ d+s) : Fin r × Fin 2 ↪ Fin (d+s) :=
  (((Equiv.refl (Fin r)).prodCongr (Equiv.swap 0 1)).toEmbedding.trans
      (upper h)).trans (localPerm d s).toEmbedding

private theorem up_val {r m : ℕ} (h : 2*r ≤ m) (p : Fin r) (i : Fin 2) :
    (upper h (p,i)).val = 2*p.val+i.val := rfl

private theorem low_val {d s r : ℕ} (hd : 2≤d) (h : 2*r≤d+s) (p : Fin r) (i : Fin 2) :
    (lower (d:=d) (s:=s) h (p,i)).val =
      if 2*p.val+(Equiv.swap 0 1 i).val+1<d then 2*p.val+(Equiv.swap 0 1 i).val+1
      else if 2*p.val+(Equiv.swap 0 1 i).val<d then 0 else 2*p.val+(Equiv.swap 0 1 i).val :=
  step hd _

private def evenIndex (r : ℕ) : Fin (r+1) ⊕ Fin (r+1) → Fin (2*r+2)
  | .inl i => ⟨2*i.val,by have := i.isLt;omega⟩
  | .inr i => ⟨2*i.val+1,by have := i.isLt;omega⟩

private theorem evenIndex_inj (r : ℕ) : Function.Injective (evenIndex r) := by
  rintro (i|i) (j|j) h <;> have e := congrArg Fin.val h <;> simp only [evenIndex] at e
  all_goals first | (congr 1;apply Fin.ext;omega) | omega

theorem even (r : ℕ) : Admits (localPerm (2*r+2) 0) [(r+1,1)] := by
  let d := 2*r+2
  have hd : 2≤d := by dsimp [d];omega
  have hh : 2*(r+1) ≤ d+0 := by dsimp [d];omega
  apply admits_even _ (upper hh) (lower hh)
  rw [chart hd (evenIndex r) (evenIndex_inj r) (by simp;omega),chart_sum]
  unfold arcs
  rw [Multiset.map_map]
  apply congrArg₂ (·+·) <;> apply congrArg (fun f => Multiset.map f Finset.univ.val) <;> funext i
  · apply Prod.ext <;> apply Fin.ext
    · change (localPerm d 0 (inside (evenIndex r (.inl i)))).val = _
      rw [step hd]
      change (if 2*i.val+1<d then 2*i.val+1 else if 2*i.val<d then 0 else 2*i.val) = 2*i.val+1
      have := i.isLt;dsimp [d];split_ifs <;> omega
    · rfl
  · apply Prod.ext <;> apply Fin.ext
    · rfl
    · rw [low_val hd]
      simp only [Equiv.swap_apply_right,Fin.val_zero,add_zero]
      change 2*i.val+1 = _
      have := i.isLt;dsimp [d];split_ifs <;> omega

private def oddIndex (r : ℕ) : Fin (r+1) ⊕ (Fin r ⊕ (Unit⊕Unit)) → Fin (2*r+3)
  | .inl i => ⟨2*i.val,by have := i.isLt;omega⟩
  | .inr (.inl i) => ⟨2*i.val+1,by have := i.isLt;omega⟩
  | .inr (.inr (.inl _)) => ⟨2*r+2,by omega⟩
  | .inr (.inr (.inr _)) => ⟨2*r+1,by omega⟩

private theorem oddIndex_inj (r : ℕ) : Function.Injective (oddIndex r) := by
  rintro (i|i|(⟨⟩|⟨⟩)) (j|j|(⟨⟩|⟨⟩)) h <;> have e := congrArg Fin.val h <;> simp only [oddIndex] at e
  all_goals simp only [Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,Fin.ext_iff] <;> first | trivial | omega

theorem odd (r s : ℕ) (u : ℚ) (hu : 0<u) :
    Admits (localPerm (2*r+3) s) (oddPolynomial (r+1) s u) := by
  let d := 2*r+3
  have hd : 2≤d := by dsimp [d];omega
  have uh : 2*(r+1) ≤ d+s := by dsimp [d];omega
  have lh : 2*r ≤ d+s := by dsimp [d];omega
  let i : Fin (d+s) := ⟨0,by omega⟩
  let j : Fin (d+s) := ⟨2*r+1,by dsimp [d];omega⟩
  let v : Fin (d+s) := ⟨2*r+2,by dsimp [d];omega⟩
  let U := Finset.Ici v
  let a := upper uh
  let b := lower (d:=d) (s:=s) lh
  have av (p : Fin (r+1) × Fin 2) : (a p).val = 2*p.1.val+p.2.val := rfl
  have bv (p : Fin r × Fin 2) : (b p).val = 2*p.1.val+(Equiv.swap 0 1 p.2).val+1 := by
    rw [show (b p).val = _ from low_val hd lh p.1 p.2,if_pos]
    have := p.1.isLt; have := (Equiv.swap 0 1 p.2).isLt; dsimp [d];omega
  apply admits_odd _ a b i j v U (by simp [Fin.ext_iff,i,j]) ?_ ?_ ?_ (Finset.mem_Ici.mpr le_rfl) ?_ s ?_ u hu
  · rintro ⟨p,e⟩; have h := congrArg Fin.val e; rw [bv] at h; change _=0 at h;omega
  · rintro ⟨p,e⟩; have h := congrArg Fin.val e; rw [bv] at h; change _=2*r+1 at h
    have := p.1.isLt; have := (Equiv.swap 0 1 p.2).isLt;omega
  · intro w hw
    have wv : 2*r+2≤w.val := (show v≤w from Finset.mem_Ici.mp hw)
    refine ⟨?_,?_,?_,?_⟩
    · intro h;have e := congrArg Fin.val h; change 0=w.val at e;omega
    · intro h;have e := congrArg Fin.val h; change 2*r+1=w.val at e;omega
    · rintro ⟨p,h⟩;have e := congrArg Fin.val h;rw [av] at e
      have := p.1.isLt;have := p.2.isLt;omega
    · rintro ⟨p,h⟩;have e := congrArg Fin.val h;rw [bv] at e
      have := p.1.isLt;have := (Equiv.swap 0 1 p.2).isLt;omega
  · rw [chart hd (oddIndex r) (oddIndex_inj r) (by simp;omega),chart_sum,chart_sum,chart_sum]
    unfold arcs
    rw [Multiset.map_map]
    apply congrArg₂ (·+·)
    · apply congrArg (fun f => Multiset.map f Finset.univ.val);funext t
      apply Prod.ext <;> apply Fin.ext
      · change (localPerm d s (inside (oddIndex r (.inl t)))).val = _
        rw [step hd]
        change (if 2*t.val+1<d then 2*t.val+1 else if 2*t.val<d then 0 else 2*t.val)=2*t.val+1
        have := t.isLt;dsimp [d];split_ifs <;> omega
      · rfl
    · apply congrArg₂ (·+·)
      · apply congrArg (fun f => Multiset.map f Finset.univ.val);funext t
        apply Prod.ext <;> apply Fin.ext
        · rfl
        · rw [bv]
          simp only [Equiv.swap_apply_right,Fin.val_zero,add_zero]
          rfl
      · simp only [Finset.univ_unique,Finset.singleton_val,Multiset.map_singleton]
        have hv : localPerm d s v = i := by
          apply Fin.ext;rw [step hd];dsimp [d,v,i];split_ifs <;> omega
        have hj : localPerm d s j = v := by
          apply Fin.ext;rw [step hd];dsimp [d,v,j];split_ifs <;> omega
        change {((localPerm d s) v,v)} + {((localPerm d s) j,j)} = _
        rw [hv,hj];rfl
  · rw [show U=Finset.Ici v from rfl,Fin.card_Ici];dsimp [v,d];omega

/-- Independent positive rational splitting constants, indexed by occurrence in a plan. -/
def piecePolynomial : Piece → ℚ → Polynomial
  | .fixed _,_ => [(0,1)]
  | .even r,_ => [(r+1,1)]
  | .odd r s,u => oddPolynomial (r+1) s u

private theorem piece_realizes (x : Piece) (u : ℚ) (hu : 0<u) :
    Realizes x.size x.parts (piecePolynomial x u) := by
  cases x with
  | fixed n => exact fixed_realizes n
  | even r =>
    exact ⟨_,by simpa [Piece.parts] using localPerm_type (2*r+2) 0 (by omega),even r⟩
  | odd r s =>
    exact ⟨_,by simpa [Piece.parts] using localPerm_type (2*r+3) s (by omega),odd r s u hu⟩

def selectedPolynomial : List Piece → (ℕ → ℚ) → Polynomial
  | [],_ => [(0,1)]
  | x::p,u => combine (piecePolynomial x (u 0)) (selectedPolynomial p (fun n => u (n+1)))

theorem selected_realizes (p : List Piece) (u : ℕ → ℚ) (hu : ∀ n, 0<u n) :
    Realizes (planSize p) (planParts p) (selectedPolynomial p u) := by
  induction p generalizing u with
  | nil => exact fixed_realizes 0
  | cons x p ih =>
    exact merge (piece_realizes x (u 0) (hu 0)) (ih (fun n => u (n+1)) (fun n => hu (n+1)))

private theorem default_realizes (x : Piece) : Realizes x.size x.parts x.polynomial := by
  cases x with
  | fixed n => exact fixed_realizes n
  | even r => exact piece_realizes (.even r) 1 zero_lt_one
  | odd r s =>
    apply piece_realizes (.odd r s)
    unfold CycleCoefficients.halfParameter
    have h := Nat.sqrt_le_sqrt (show 16 ≤ 16*(s+1) by omega)
    change 4 ≤ _ at h
    have ht : 0 < (Nat.sqrt (16*(s+1))+1)/2 := by omega
    positivity

theorem plan_realizes (p : List Piece) : Realizes (planSize p) (planParts p) (planPolynomial p) := by
  induction p with
  | nil => exact fixed_realizes 0
  | cons x p ih => exact merge (default_realizes x) ih

end
end BlockPermanents.CycleUnbounded
