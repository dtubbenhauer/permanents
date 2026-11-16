import BlockPermanents.OddCycleSquares
import BlockPermanents.CycleUnbounded

/-! Two signed reflected halves on the actual consecutive cycle, in every length. -/
namespace BlockPermanents.ReflectedCycles
open Closures CycleMatching CycleComposition CycleCuts CyclePolynomial Matchings
noncomputable section

/-- A consecutive odd cycle of length 2r+3 has r+1 upper edges, r short
lower edges and one two-step path with s+1 choices of middle label. -/
private structure OddLayout (r s : ℕ) where
  upper : Fin (r+1) × Fin 2 ↪ Fin (2*r+3+s)
  lower : Fin r × Fin 2 ↪ Fin (2*r+3+s)
  i : Fin (2*r+3+s)
  j : Fin (2*r+3+s)
  v : Fin (2*r+3+s)
  U : Finset (Fin (2*r+3+s))
  hij : i ≠ j
  hi : i ∉ Set.range lower
  hj : j ∉ Set.range lower
  fresh : ∀ w ∈ U, i ≠ w ∧ j ≠ w ∧ w ∉ Set.range upper ∧ w ∉ Set.range lower
  hv : v ∈ U
  wires : wiring (localPerm (2*r+3) s) =
    (arcs upper).map Prod.swap + (arcs lower + {(i,v),(v,j)})
  card : U.card = s+1

open private upper lower low_val chart oddIndex oddIndex_inj chart_sum inside step
  from BlockPermanents.CycleUnbounded in
private def oddLayout (r s : ℕ) : OddLayout r s := by
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
  refine ⟨a,b,i,j,v,U,by simp [Fin.ext_iff,i,j],?_,?_,?_,Finset.mem_Ici.mpr le_rfl,?_,?_⟩
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

/-- The two reflected terms for the alternating cut of the consecutive cycle.
The second term sums the spectator-weighted path squares for that cut. -/
def oddRemainder {D : Type*} [Fintype D] (r s : ℕ) (x : Fin (2*r+3+s) → D → ℂ)
    (plus : Bool) (u : ℝ) : ℝ :=
  let c := oddLayout r s
  let g := crossGram x x
  (average _ (fun σ => Complex.normSq (half plus u (amplitude g c.upper σ)
    (lowerHalf g c.lower c.i c.j c.U σ))) +
    TwoStepSpectator.remainder x c.lower c.i c.j c.U) / (2*u*((s:ℝ)+1))

theorem oddRemainder_nonneg {D : Type*} [Fintype D] (r s : ℕ) (x : Fin (2*r+3+s) → D → ℂ)
    (plus : Bool) (u : ℝ) (hu : 0 < u) : 0 ≤ oddRemainder r s x plus u := by
  unfold oddRemainder
  exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _)) (TwoStepSpectator.remainder_nonneg ..)) (by positivity)

/-- Both signs of the normalized odd-cycle estimate (AB.2), on the
specified cycle itself with all s unused labels. This includes triangles. -/
theorem odd_consecutive_squares {D : Type*} [Fintype D] (r s : ℕ)
    (x : Fin (2*r+3+s) → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    (u/((s:ℝ)+1)+1/u)/2 * Z g (r+1) + (s:ℝ)/(2*u) * Z g (r+2) +
      sign plus * (mean g (localPerm (2*r+3) s)).re = oddRemainder r s x plus u := by
  let c := oddLayout r s
  have h := odd_circuit_squares x unit _ c.upper c.lower c.i c.j c.v c.U
    c.hij c.hi c.hj c.fresh c.hv c.wires plus u hu
  dsimp only at h ⊢
  simpa only [c.card, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

/-- Taking the two signs recovers the absolute bound directly from these squares. -/
theorem odd_consecutive_bound {D : Type*} [Fintype D] (r s : ℕ)
    (x : Fin (2*r+3+s) → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    |(mean g (localPerm (2*r+3) s)).re| ≤
      (u/((s:ℝ)+1)+1/u)/2 * Z g (r+1) + (s:ℝ)/(2*u) * Z g (r+2) := by
  have signed (plus : Bool) := (odd_consecutive_squares r s x unit plus u hu).symm ▸
    oddRemainder_nonneg r s x plus u hu
  have pos := signed true
  have neg := signed false
  simp only [sign, Bool.true_eq_false, Bool.false_eq_true, if_pos, if_false, neg_mul,
    one_mul] at pos neg
  dsimp only
  exact abs_le.mpr ⟨by linarith only [pos], by linarith only [neg]⟩

private structure EvenLayout (r s : ℕ) where
  upper : Fin (r+1) × Fin 2 ↪ Fin (2*r+2+s)
  lower : Fin (r+1) × Fin 2 ↪ Fin (2*r+2+s)
  wires : wiring (localPerm (2*r+2) s) = (arcs upper).map Prod.swap + arcs lower

open private upper lower low_val chart evenIndex evenIndex_inj chart_sum inside step
  from BlockPermanents.CycleUnbounded in
private def evenLayout (r s : ℕ) : EvenLayout r s := by
  let d := 2*r+2
  have hd : 2≤d := by dsimp [d];omega
  have hh : 2*(r+1) ≤ d+s := by dsimp [d];omega
  refine ⟨upper hh, lower (d:=d) (s:=s) hh, ?_⟩
  rw [chart hd (evenIndex r) (evenIndex_inj r) (by simp;omega),chart_sum]
  unfold arcs
  rw [Multiset.map_map]
  apply congrArg₂ (·+·) <;> apply congrArg (fun f => Multiset.map f Finset.univ.val) <;> funext i
  · apply Prod.ext <;> apply Fin.ext
    · change (localPerm d s (inside (evenIndex r (.inl i)))).val = _
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

def evenRemainder (r s : ℕ) (g : Gram (2*r+2+s)) (plus : Bool) : ℝ :=
  let c := evenLayout r s
  average _ (fun σ => Complex.normSq (half plus 1 (amplitude g c.upper σ) (amplitude g c.lower σ))) / 2

/-- The two signs on a consecutive even cycle, including the length-two case. -/
theorem even_consecutive_squares (r s : ℕ) (g : Gram (2*r+2+s)) (hg : UnitGram g) (plus : Bool) :
    Z g (r+1) + sign plus * (mean g (localPerm (2*r+2) s)).re = evenRemainder r s g plus :=
  even_circuit_squares g hg _ (evenLayout r s).upper (evenLayout r s).lower (evenLayout r s).wires plus

end
end BlockPermanents.ReflectedCycles
