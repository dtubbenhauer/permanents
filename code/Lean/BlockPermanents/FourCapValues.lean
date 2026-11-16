import BlockPermanents.FourCapOrbit
import BlockPermanents.FourLastCaps
import BlockPermanents.ThreeWire
import BlockPermanents.FourQuadratic

/-! # Last-cap values on the three concrete proper cuts -/
namespace BlockPermanents.FourCapValues
open Bend FourRoutes FourCapAction FourCapOrbit FourLastCaps Equiv
open scoped BigOperators Matrix
noncomputable section

abbrev Port := Option (Fin 4)
abbrev U (r : Fin 3) := Fin (3-(r.val+1)) × Fin 2
abbrev A (r : Fin 3) := Fin ((r.val+1)*2)
private theorem hs (r : Fin 3) : r.val+1 ≤ 3 := by omega

def sections (r : Fin 3) : Pos ≃ U r ⊕ A r :=
  (((blocks (r.val+1) (hs r)).symm.prodCongr (Equiv.refl _)).trans
    (Equiv.sumProdDistrib _ _ _)).trans ((Equiv.refl _).sumCongr finProdFinEquiv)

def ports (r : Fin 3) : U r ⊕ A r ≃ Letter :=
  ((finProdFinEquiv.sumCongr (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (by have := r.isLt; omega)))).trans
    (finSuccEquivLast.trans (finSuccEquiv 4).optionCongr)

def order (r : Fin 3) (p : Perm (A r)) : Chart :=
  (sections r).trans (((Equiv.refl _).sumCongr p).trans (ports r))

@[simp] theorem order_inl (r : Fin 3) (p : Perm (A r)) (i : Fin (3-(r.val+1))) (j : Fin 2) :
    order r p (blocks _ (hs r) (.inl i), j) = ports r (.inl (i,j)) := by
  simp [order,sections]

@[simp] theorem order_inr (r : Fin 3) (p : Perm (A r)) (i : Fin (r.val+1)) (j : Fin 2) :
    order r p (blocks _ (hs r) (.inr i), j) = ports r (.inr (p (finProdFinEquiv (i,j)))) := by
  simp [order,sections]

def closed (r : Fin 3) (p : Perm (A r)) (a : Port) : Chart :=
  (order r p).trans (swap none a).optionCongr

def spectatorPort (r : Fin 3) (i : U r) : Port :=
  (finSuccEquiv 4) ⟨(finProdFinEquiv i).val,by
    have h := (finProdFinEquiv i).isLt; have := r.isLt; omega⟩

def activePort (r : Fin 3) (j : Fin ((r.val+1)*2-1)) : Port :=
  (finSuccEquiv 4) ⟨(3-(r.val+1))*2+j,by have := j.isLt;have := r.isLt;omega⟩

/-- The five ordinary outputs are read in spectator-then-active order. -/
def raw {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (u : Port → Fin d) (b : Fin d) : ℂ :=
  (capHalf d 2 (r.val+1) (hs r) ⟨1,by have := r.isLt;omega⟩ (fun i j => u (spectatorPort r (i,j)))).mulVec
    (product F (fun v => star (H v))) (fun i => u (activePort r i), fun _ => b)

private theorem leftSlot (r : Fin 3) (i : U r) :
    ports r (.inl i) = some (spectatorPort r i) := by
  rcases i with ⟨i,j⟩
  fin_cases r <;> fin_cases i <;> fin_cases j <;> rfl

private theorem activeWord {d : ℕ} (r : Fin 3) (u : Port → Fin d) (t : Fin d) (i : A r) :
    Fin.append (fun j => u (activePort r j)) (fun _ : Fin 1 => t)
      (Fin.cast (show (r.val+1)*2-1+1 = (r.val+1)*2 by omega).symm i) =
      (ports r (.inr i)).elim t u := by
  fin_cases r <;> fin_cases i <;> rfl

private theorem read (r : Fin 3) {d : ℕ} (p : Perm (A r)) (u : Port → Fin d) (t : Fin d) :
    Function.uncurry ((split (hs r) 1).symm (fun i j => u (spectatorPort r (i,j)),
      (fun i => Fin.append (fun j => u (activePort r j)) (fun _ : Fin 1 => t)
        (Fin.cast (show (r.val+1)*2-1+1 = (r.val+1)*2 by omega).symm i)) ∘ p)) =
      (fun l : Letter => l.elim t u) ∘ order r p := by
  funext ij
  obtain ⟨v,h⟩ := (blocks (r.val+1) (hs r)).surjective ij.1
  rcases ij with ⟨i,j⟩
  dsimp only at h
  subst i
  cases v with
  | inl i =>
    simp only [Function.uncurry, split, Equiv.coe_fn_symm_mk,Equiv.Perm.one_symm,Equiv.Perm.one_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    simp [Function.comp_apply,leftSlot]
  | inr i =>
    simp only [Function.uncurry, split, Equiv.coe_fn_symm_mk,Equiv.Perm.one_symm,Equiv.Perm.one_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    simpa only [Function.comp_apply, order_inr] using activeWord r u t (p (finProdFinEquiv (i,j)))

theorem raw_formula {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Bend.Symmetric H) (u : Port → Fin d) (b : Fin d) :
    raw r F H u b = (((r.val+1)*2).factorial : ℂ)⁻¹ * ∑ p : Perm (A r),
      ∑ t, feet F ((fun l : Letter => l.elim t u) ∘ order r p) * star (H ![b,t]) := by
  unfold raw
  rw [capHalf_entry _ F H hH]
  let e : (Fin 1 → Fin d) ≃ Fin d := Equiv.funUnique _ _
  rw [← e.symm.sum_comp]
  have eword (t : Fin d) : e.symm t = (fun _ => t) := rfl
  have hm (t : Fin d) : (fun i : Fin 2 => Fin.append (fun _ : Fin 1 => b) (fun _ : Fin 1 => t) i) = ![b,t] := by
    funext i; fin_cases i <;> rfl
  simp only [eword,Fin.cast_eq_self,hm]
  simp only [Closures.clasp,Closures.sumSlots,Fintype.card_fin,averaged_feet]
  have term (t : Fin d) (p : Perm (A r)) :=
    congrArg (feet F) (read r p.symm u t)
  simp only [Fin.cast_eq_self] at term
  let g := fun (p : Perm (A r)) (t : Fin d) =>
    feet F ((fun l : Letter => l.elim t u) ∘ order r p) * star (H ![b,t])
  trans ∑ t : Fin d, (((r.val+1)*2).factorial : ℂ)⁻¹ * ∑ p : Perm (A r), g p.symm t
  · apply Finset.sum_congr rfl
    intro t _
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (fun z => z * star (H ![b,t])) (term t p)
  rw [← Finset.mul_sum,Finset.sum_comm]
  exact congrArg (fun z : ℂ => (((r.val+1)*2).factorial : ℂ)⁻¹ * z)
    (Equiv.sum_comp (Equiv.inv (Perm (A r))) (fun p => ∑ t, g p t))

private theorem wire_insert {d : ℕ} (r : Fin 3) (p : Perm (A r)) (a : Port) (v : Fin 4 → Fin d)
    (b t : Fin d) :
    (fun l : Letter => l.elim t (insertAt a v b)) ∘ order r p =
      labels t b v ∘ closed r p a := by
  funext i
  change (order r p i).elim t (insertAt a v b) =
    labels t b v ((swap none a).optionCongr (order r p i))
  cases h : order r p i with
  | none => rfl
  | some j => change ((swap none a) j).elim b v = Option.elim' b v ((swap none a) j); cases (swap none a) j <;> rfl

/-- The second cap averages the first cap's actual active permutations,
the positive slot in the selected port and the final four-strand clasp. -/
theorem port_formula {d : ℕ} (r : Fin 3) (S : Finset (Fin d)) (P : Finset Port)
    (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (v : Word d 4) :
    portCap S P (raw r F H) v =
      (((r.val+1)*2).factorial : ℂ)⁻¹ * (P.card : ℂ)⁻¹ *
        ∑ p : Perm (A r), ∑ a ∈ P, value S F H (closed r p a) v := by
  unfold portCap value
  simp_rw [raw_formula r F H hH, wire_insert]
  let f := fun (σ : Perm (Fin 4)) (a : Port) (b : Fin d) (p : Perm (A r)) =>
    ∑ t, feet F (labels t b (v ∘ σ) ∘ closed r p a) * star (H ![b,t])
  classical
  have comm : (∑ σ, ∑ a ∈ P, ∑ b ∈ S, ∑ p, f σ a b p) =
      ∑ p, ∑ a ∈ P, ∑ σ, ∑ b ∈ S, f σ a b p := by
    conv_lhs =>
      enter [2,σ,2,a]
      rw [Finset.sum_comm]
    conv_lhs =>
      enter [2,σ]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    exact Finset.sum_comm
  change _ * (∑ σ, ∑ a ∈ P, ∑ b ∈ S, _ * ∑ p, f σ a b p) =
    _ * (∑ p, ∑ a ∈ P, _ * ∑ σ, ∑ b ∈ S, f σ a b p)
  simp only [← Finset.mul_sum,comm,mul_inv_rev]
  ring

def activeSet (r : Fin 3) : Finset Port :=
  Finset.univ.filter fun a => (3-(r.val+1))*2 ≤ ((finSuccEquiv 4).symm a).val

def spectatorSet (r : Fin 3) : Finset Port := (activeSet r)ᶜ

private def isActive (r : Fin 3) (l : Letter) : Prop := l.elim True (fun a => a ∈ activeSet r)

private instance (r : Fin 3) (l : Letter) : Decidable (isActive r l) := by
  rcases l with _|a
  · exact isTrue trivial
  · exact inferInstanceAs (Decidable (a ∈ activeSet r))

private theorem tag_left (r : Fin 3) (i : U r) : ¬isActive r (ports r (.inl i)) := by
  rcases i with ⟨i,j⟩
  fin_cases r <;> fin_cases i <;> fin_cases j <;> decide
private theorem tag_right (r : Fin 3) (i : A r) : isActive r (ports r (.inr i)) := by
  fin_cases r <;> fin_cases i <;> decide

private theorem tag_order (r : Fin 3) (p : Perm (A r)) (i : Pos) :
    isActive r (order r p i) ↔ 3-(r.val+1) ≤ i.1.val := by
  rcases i with ⟨i,j⟩
  obtain ⟨z,rfl⟩ := (blocks _ (hs r)).surjective i
  cases z with
  | inl i =>
    rw [order_inl,iff_false_left (tag_left r _)]
    change ¬ (3-(r.val+1)) ≤ i.val
    omega
  | inr i =>
    rw [order_inr,iff_true_left (tag_right r _)]
    change (3-(r.val+1)) ≤ (3-(r.val+1))+i.val
    omega

private def mate (i : Pos) : Pos := (i.1,swap 0 1 i.2)

private theorem partner (r : Fin 3) (p : Perm (A r)) : ∃ q ∈ activeSet r, ∀ a : Port,
    (((closed r p a).symm none).1 = ((closed r p a).symm (some none)).1) ↔ a = q := by
  let e := order r p
  let i := e.symm none
  have hne (j : Pos) : mate j ≠ j := by
    rcases j with ⟨j,k⟩; fin_cases j <;> fin_cases k <;> decide
  have hn : e (mate i) ≠ none := by
    intro h
    exact hne i (e.injective (h.trans (e.apply_symm_apply none).symm))
  obtain ⟨q,hq⟩ := Option.ne_none_iff_exists'.mp hn
  have hi : 3 - (r.val+1) ≤ i.1.val := by
    apply (tag_order r p i).mp
    change isActive r (e (e.symm none))
    rw [e.apply_symm_apply]; trivial
  have hqA := (tag_order r p (mate i)).mpr hi
  change isActive r (e (mate i)) at hqA
  rw [hq] at hqA
  refine ⟨q,hqA,?_⟩
  intro a
  have key : (closed r p a).symm (some none) = e.symm (some a) := by
    change e.symm (some ((swap none a).symm none)) = _; simp
  rw [key]
  change i.1 = (e.symm (some a)).1 ↔ _
  constructor
  · intro he
    have hj : e.symm (some a) ≠ i := fun hij => Option.noConfusion (e.symm.injective hij)
    have pair_unique (i j : Pos) (hij : j ≠ i) (hg : i.1 = j.1) : j = mate i := by
      rcases i with ⟨i,u⟩; rcases j with ⟨j,v⟩
      change i = j at hg; subst j
      fin_cases u <;> fin_cases v <;> simp_all [mate]
    have ht := congrArg e (pair_unique i (e.symm (some a)) hj he)
    rw [e.apply_symm_apply,hq] at ht
    exact Option.some_injective _ ht
  · rintro rfl
    rw [← hq,e.symm_apply_apply];rfl


/-- The active bundle has exactly one partner for the first turn, the
other strand of its original quadratic packet. Every spectator is mixed. -/
theorem rows {d : ℕ} (r : Fin 3) (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : Inner F)
    (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (w : Word d 4) :
    let x := value S F H sameChart w
    let y := value S F H mixedChart w
    (portCap S (activeSet r) (raw r F H) w =
      (x+((activeSet r).card-1 : ℂ)*y)/(activeSet r).card) ∧
    (r.val < 2 → portCap S (spectatorSet r) (raw r F H) w = y) := by
  dsimp only
  let x := value S F H sameChart w
  let y := value S F H mixedChart w
  have comp (p : Perm (A r)) :
      (∑ a ∈ activeSet r, value S F H (closed r p a) w) =
        x+((activeSet r).card-1 : ℂ)*y ∧
      (∑ a ∈ spectatorSet r, value S F H (closed r p a) w) = (spectatorSet r).card*y := by
    obtain ⟨q,hq,hc⟩ := partner r p
    have vals (a : Port) : value S F H (closed r p a) w = if a=q then x else y := by
      rw [classify S hF];simp only [hc a];rfl
    simp_rw [vals]
    constructor
    · rw [← Finset.sum_erase_add _ _ hq]
      simp only [if_pos rfl]
      have he : ∀ a ∈ (activeSet r).erase q, (if a=q then x else y) = y :=
        fun a ha => if_neg (Finset.mem_erase.mp ha).1
      rw [Finset.sum_congr rfl he,Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem hq,
          Nat.cast_sub (Finset.one_le_card.mpr ⟨q,hq⟩)]
      simp; ring
    · have he : ∀ a ∈ spectatorSet r, (if a=q then x else y) = y := by
        intro a ha;apply if_neg; rintro rfl;exact (Finset.mem_compl.mp ha) hq
      rw [Finset.sum_congr rfl he]; simp
  have hk : (((r.val+1)*2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  constructor
  · rw [port_formula _ _ _ _ _ hH]
    simp_rw [fun p => (comp p).1]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
    change _ = (x+_ * y)/_
    have ha : (activeSet r).card ≠ 0 := by fin_cases r <;> decide
    field_simp [hk,Nat.cast_ne_zero.mpr ha]; ring
  · intro hr
    have hs' : (spectatorSet r).card ≠ 0 := by fin_cases r <;> first | decide | exact (by decide : ¬ (2:Fin 3).val < 2) hr | contradiction
    rw [port_formula _ _ _ _ _ hH]
    simp_rw [fun p => (comp p).2]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
    change _ = y
    field_simp [hk,Nat.cast_ne_zero.mpr hs']; ring

def PU : Fin 2 → Finset Port := ![spectatorSet 0,activeSet 0]
def PW : Fin 2 → Finset Port := ![spectatorSet 1,activeSet 1]
def PV : Fin 1 → Finset Port := fun _ => activeSet 2

theorem five_values {d : ℕ} (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : Inner F)
    (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (w : Word d 4) :
    let x := value S F H sameChart w
    let y := value S F H mixedChart w
    portCap S (spectatorSet 0) (raw 0 F H) w = y ∧
    portCap S (activeSet 0) (raw 0 F H) w = x ∧
    portCap S (spectatorSet 1) (raw 1 F H) w = y ∧
    portCap S (activeSet 1) (raw 1 F H) w = (x+2*y)/3 ∧
    portCap S (activeSet 2) (raw 2 F H) w = (x+4*y)/5 := by
  dsimp only
  have ha : (activeSet 0).card = 1 := by decide
  have hb : (activeSet 1).card = 3 := by decide
  have hc : (activeSet 2).card = 5 := by decide
  have a := rows 0 S hF H hH w
  have b := rows 1 S hF H hH w
  have c := rows 2 S hF H hH w
  norm_num [ha,hb,hc] at a b c
  exact ⟨a.2,a.1,b.2,b.1,c⟩

end
end BlockPermanents.FourCapValues
