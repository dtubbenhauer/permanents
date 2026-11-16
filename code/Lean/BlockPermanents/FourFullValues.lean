import BlockPermanents.FourCapValues
import Mathlib.GroupTheory.Perm.Option
import BlockPermanents.FourCapReindex

/-! # Completing a proper half on its active bundle

Closing the last through pair in the original cap equals the two-strand
cap, with the same spectator coordinates. The coordinate plane restriction
only removes marked coefficients which are zero.
-/
namespace BlockPermanents.FourFullValues
open Bend Closures FourRoutes FourCapAction FourCapOrbit FourCapValues FourLastCaps Equiv
open scoped BigOperators Matrix
noncomputable section

def anchor : Port := some 3

def retained {d : ℕ} (w : Word d 4) (a : Port) := w (((swap none anchor) a).getD 0)

def through (r : Fin 3) (i : Fin ((r.val+1)*2-2)) : Port :=
  activePort r ⟨i,by have := i.isLt;omega⟩

/-- The full two-strand matrix cap, with its four output positions read
in the survivor coordinates of the final positive slot. -/
def full {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (w : Word d 4) : ℂ :=
  (capHalf d 2 (r.val+1) (by have := r.isLt;omega) ⟨2,by have := r.isLt;omega⟩
    (fun i j => retained w (spectatorPort r (i,j)))).mulVec
    (product F (fun v => star (H v))) (fun i => retained w (through r i), Fin.elim0)

private theorem idle {d : ℕ} (r : Fin 3) (w : Word d 4) (b : Fin d) :
    (fun i j => insertAt anchor w b (spectatorPort r (i,j))) =
      (fun i j => retained w (spectatorPort r (i,j))) := by
  funext i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;> rfl

private theorem paired {d : ℕ} (r : Fin 3) (w : Word d 4) (b t : Fin d) :
    (fun i : A r => Fin.append (fun j => insertAt anchor w b (activePort r j))
      (fun _ : Fin 1 => t) (Fin.cast (show (r.val+1)*2-1+1=(r.val+1)*2 by omega).symm i)) =
      (fun i : A r => Fin.append (fun j => retained w (through r j))
        ![b,t] (Fin.cast (show (r.val+1)*2-2+2=(r.val+1)*2 by omega).symm i)) := by
  funext i
  fin_cases r <;> fin_cases i <;> rfl

theorem join_cut {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Bend.Symmetric H) (w : Word d 4) :
    (∑ b, raw r F H (insertAt anchor w b) b) = full r F H w := by
  unfold raw full
  simp only [capHalf_entry _ F H hH]
  let e : (Fin 1 → Fin d) ≃ Fin d := Equiv.funUnique _ _
  let j : Word d 2 ≃ Fin d × Fin d := finTwoArrowEquiv (Fin d)
  rw [← j.symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  rw [idle]
  have hh : (fun i : Fin 2 => Fin.append (fun _ : Fin 1 => b) (e.symm t) i) =
      (fun i : Fin 2 => Fin.append (Fin.elim0 : Fin 0 → Fin d) (j.symm (b,t)) i) := by
    funext i; fin_cases i <;> rfl
  exact congrArg₂ (fun v h => clasp _ v * star (H h)) (paired r w b t) hh

/-- A planar marked input in the chosen orthonormal coordinates. -/
def Supported {d : ℕ} (S : Finset (Fin d)) (H : Word d 2 → ℂ) : Prop :=
  ∀ b ∉ S, ∀ t, H ![b,t] = 0

theorem packet_supported {d : ℕ} (S : Finset (Fin d)) (x : Fin 2 → Fin d → ℂ)
    (hx : ∀ i j, j ∉ S → x i j = 0) : Supported S (packet x) := by
  intro b hb t
  unfold packet orderSum
  have hz (p : Perm (Fin 2)) : pureWord (x ∘ p) ![b,t] = 0 := by
    simp [pureWord,Fin.prod_univ_two,hx _ b hb]
  simp [hz]

theorem outside_zero {d : ℕ} (r : Fin 3) (S : Finset (Fin d))
    (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (hS : Supported S H)
    (u : Port → Fin d) {b : Fin d} (hb : b ∉ S) : raw r F H u b = 0 := by
  simp [raw_formula r F H hH,hS b hb]

theorem anchor_value {d : ℕ} (r : Fin 3) (S : Finset (Fin d)) (F : Triple d 2 → ℂ)
    (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (hS : Supported S H) (w : Word d 4) :
    portCap S {anchor} (raw r F H) w = clasp (full r F H) w := by
  have he (v : Word d 4) :
      (∑ b ∈ S, raw r F H (insertAt anchor v b) b) = full r F H v := by
    rw [← join_cut r F H hH]
    exact Finset.sum_subset (Finset.subset_univ _) fun b _ hb =>
      outside_zero r S F H hH hS _ hb
  simp only [portCap,Finset.card_singleton,Nat.cast_one,one_mul,Finset.sum_singleton,he,
    clasp,sumSlots,Fintype.card_fin]
  exact congrArg (fun v : ℂ => (24:ℂ)⁻¹ * v)
    (Equiv.sum_comp (Equiv.inv (Perm (Fin 4))) (fun p => full r F H (w ∘ p))).symm

private theorem active_witness (r : Fin 3) (a : Port) (ha : a ∈ activeSet r) :
    ∃ i : A r, ports r (.inr i) = some a := by
  have h : ∀ (r : Fin 3) (a : Port), a ∈ activeSet r →
      ∃ i : A r, ports r (.inr i) = some a := by decide
  exact h r a ha

/-- Swapping two positions inside the through part of a merged cable
has no effect on the actual once-contracted tensor. -/
theorem raw_swap {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Bend.Symmetric H) {a b : Port} (ha : a ∈ activeSet r) (hb : b ∈ activeSet r)
    (u : Port → Fin d) (c : Fin d) :
    raw r F H (u ∘ swap a b) c = raw r F H u c := by
  obtain ⟨i,hi⟩ := active_witness r a ha
  obtain ⟨j,hj⟩ := active_witness r b hb
  have hp (p : Perm (A r)) : (order r p).trans (swap a b).optionCongr = order r (swap i j * p) := by
    apply Equiv.ext; intro s
    rw [Equiv.optionCongr_swap, ← hi, ← hj]
    let z := (Equiv.refl (U r)).sumCongr p (sections r s)
    change swap (ports r (.inr i)) (ports r (.inr j)) (ports r z) = _
    rw [← (ports r).injective.map_swap]
    apply congrArg (ports r)
    rcases h : sections r s with v|v <;> simp [z,h,swap_apply_def,Perm.mul_apply]
    split_ifs <;> rfl
  rw [raw_formula r F H hH,raw_formula r F H hH]
  congr 1
  have hu (t : Fin d) : (fun l : Letter => l.elim t (u ∘ swap a b)) =
      (fun l : Letter => l.elim t u) ∘ (swap a b).optionCongr := by
    funext l; cases l <;> rfl
  have hx (p : Perm (A r)) (t : Fin d) :
      (fun l : Letter => l.elim t (u ∘ swap a b)) ∘ order r p =
        (fun l : Letter => l.elim t u) ∘ order r (swap i j * p) := by
    rw [hu, ← hp];rfl
  simp_rw [hx]
  exact (Group.mulLeft_bijective (swap i j)).sum_comp (fun p : Perm (A r) =>
    ∑ t, feet F ((fun l : Letter => l.elim t u) ∘ order r p) * star (H ![c,t]))

/-- Completing at any physical position of the active bundle gives the
same projected amplitude. This identifies the whole port with the two-cap
matrix on the marked support. -/
theorem active_full {d : ℕ} (r : Fin 3) (S : Finset (Fin d)) (F : Triple d 2 → ℂ)
    (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (hS : Supported S H) (w : Word d 4) :
    portCap S (activeSet r) (raw r F H) w = clasp (full r F H) w := by
  have hanc : anchor ∈ activeSet r := by fin_cases r <;> decide
  have has (a : Port) (ha : a ∈ activeSet r) :
      portCap S {a} (raw r F H) w = clasp (full r F H) w := by
    have move := FourLastCaps.cap_reindex S {a} {anchor} (swap a anchor)
      (by intro i;simpa only [Finset.mem_singleton,swap_apply_right] using
        (swap a anchor).injective.eq_iff (a := i) (b := anchor))
      (raw r F H) w
    simp_rw [raw_swap r F H hH ha hanc] at move
    exact move.trans (anchor_value r S F H hH hS w)
  have hcard : ((activeSet r).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨anchor,hanc⟩)
  unfold portCap
  rw [Finset.sum_comm]
  have he (a : Port) (ha : a ∈ activeSet r) :
      (∑ σ : Perm (Fin 4), ∑ c ∈ S, raw r F H (insertAt a (w ∘ σ) c) c) =
        24 * clasp (full r F H) w := by
    have q := has a ha
    simp only [portCap,Finset.card_singleton,Nat.cast_one,one_mul,Finset.sum_singleton] at q
    linear_combination (24:ℂ) * q
  rw [Finset.sum_congr rfl he,Finset.sum_const,nsmul_eq_mul]
  field_simp [hcard]; ring

theorem full_values {d : ℕ} (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : FourCapOrbit.Inner F)
    (H : Word d 2 → ℂ) (hH : Bend.Symmetric H) (hS : Supported S H) (w : Word d 4) :
    let x := value S F H sameChart w
    let y := value S F H mixedChart w
    clasp (full 0 F H) w = x ∧
      clasp (full 1 F H) w = (x+2*y)/3 ∧
      clasp (full 2 F H) w = (x+4*y)/5 := by
  obtain ⟨_,hu,_,hw,hv⟩ := five_values S hF H hH w
  simp only [← active_full _ S F H hH hS]
  exact ⟨hu,hw,hv⟩

private def survivorOrder : Perm (Fin 4) := swap 0 1 * swap 0 2 * swap 0 3

private theorem last_args {d : ℕ} (w : Word d 4) (i : Fin 4) :
    retained w (through 2 i) = w (survivorOrder i) := by
  fin_cases i <;> rfl

private theorem append_permutation {d : ℕ} (w : Word d 4) (t : Word d 2)
    (p : Perm (Fin 4)) :
    ∃ q : Perm (Fin 6), Fin.append (fun i => w (p (survivorOrder i))) t =
      Fin.append (fun i => w (survivorOrder i)) t ∘ q := by
  let h := survivorOrder.trans (p.trans survivorOrder.symm)
  let q := finSumFinEquiv.symm.trans ((h.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv)
  refine ⟨q,?_⟩
  funext i
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
    simp only [q,Function.comp_apply,trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl]
    change Fin.append _ t (Fin.castAdd 2 i) = Fin.append _ t (Fin.castAdd 2 (h i))
    simp [h]
  | inr i =>
    simp only [q,Function.comp_apply,trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr,Equiv.refl_apply]
    change Fin.append _ t (Fin.natAdd 4 i) = Fin.append _ t (Fin.natAdd 4 i)
    simp [-Fin.natAdd_eq_addNat]

/-- The three-packet merge leaves four jointly symmetric positive
strands after both contractions. -/
theorem last_symmetric {d : ℕ} (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ)
    (hH : Bend.Symmetric H) : clasp (full 2 F H) = full 2 F H := by
  have hi (w : Word d 4) (p : Perm (Fin 4)) :
      full 2 F H (w ∘ p) = full 2 F H w := by
    unfold full
    simp only [capHalf_entry _ F H hH]
    apply Finset.sum_congr rfl
    intro t _
    let empty : Spectator d 2 3 := fun i => Fin.elim0 i
    have hs (v : Word d 4) : (fun i j => retained v (spectatorPort 2 (i,j))) = empty := by
      funext i;exact Fin.elim0 i
    rw [hs,hs]
    simp only [last_args,Function.comp_apply,Fin.cast_eq_self]
    obtain ⟨q,hq⟩ := append_permutation w t p
    exact congrArg (fun v : ℂ => v * star (H (Fin.append Fin.elim0 t)))
      ((congrArg (clasp (averaged (by decide : 3≤3) F empty)) hq).trans (clasp_invariant _ q.symm _))
  funext w
  simp only [clasp,sumSlots,hi,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin,nsmul_eq_mul]
  norm_num [Nat.factorial];ring

private def outputSlots (r : Fin 3) : U r ⊕ Fin ((r.val+1)*2-2) ≃ Fin 4 :=
  (finProdFinEquiv.sumCongr (Equiv.refl _)).trans
    ((finSumFinEquiv.trans (finCongr (by have := r.isLt;omega))).trans survivorOrder)

private theorem out_left {d : ℕ} (r : Fin 3) (w : Word d 4) (i : U r) :
    retained w (spectatorPort r i) = w (outputSlots r (.inl i)) := by
  rcases i with ⟨i,j⟩
  fin_cases r <;> fin_cases i <;> fin_cases j <;> rfl

private theorem out_right {d : ℕ} (r : Fin 3) (w : Word d 4) (i : Fin ((r.val+1)*2-2)) :
    retained w (through r i) = w (outputSlots r (.inr i)) := by
  fin_cases r <;> fin_cases i <;> rfl

/-- Regrouping the four full-cap output strands by spectator and active
cable is a permutation of the complete product basis. -/
def outputWords (r : Fin 3) (d : ℕ) : Word d 4 ≃
    Spectator d 2 (r.val+1) × Word d ((r.val+1)*2-2) where
  toFun w := (fun i j => w (outputSlots r (.inl (i,j))), fun i => w (outputSlots r (.inr i)))
  invFun v i := Sum.elim (Function.uncurry v.1) v.2 ((outputSlots r).symm i)
  left_inv w := by
    funext i;obtain ⟨i,rfl⟩ := (outputSlots r).surjective i
    cases i <;> simp [Function.uncurry]
  right_inv v := by
    rcases v with ⟨s,a⟩
    apply Prod.ext
    · funext i j;simp [Function.uncurry]
    · funext i;simp

/-- The norm on the four common output words equals the sum of norms on
the original full-cap matrices, including the zero-strand marked output. -/
theorem full_energy {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) :
    energy (full r F H) =
      ∑ s, energy ((capHalf d 2 (r.val+1) (by have := r.isLt;omega) ⟨2,by have := r.isLt;omega⟩ s).mulVec
        (product F (fun t => star (H t)))) := by
  let M := capHalf d 2 (r.val+1) (by have := r.isLt;omega) ⟨2,by have := r.isLt;omega⟩
  let z := product F (fun t => star (H t))
  let f := fun v : Spectator d 2 (r.val+1) × Word d ((r.val+1)*2-2) =>
    Complex.normSq ((M v.1).mulVec z (v.2,Fin.elim0))
  have h (w : Word d 4) : Complex.normSq (full r F H w) = f (outputWords r d w) := by
    simp only [full,out_left,out_right]; rfl
  unfold energy
  simp_rw [h]
  rw [Equiv.sum_comp (outputWords r d) f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  letI : Unique (Word d 0) := ⟨⟨Fin.elim0⟩, fun _ => funext fun i => Fin.elim0 i⟩
  rw [Fintype.sum_unique]
  rfl

end
end BlockPermanents.FourFullValues
