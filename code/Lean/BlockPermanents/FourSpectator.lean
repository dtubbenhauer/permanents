import BlockPermanents.FourCapReindex
import BlockPermanents.Coarse

/-! # Projecting the four spectator strands on the one-cap row -/
namespace BlockPermanents.FourLastCaps
open Bend Closures Equiv
open scoped BigOperators Matrix
noncomputable section
variable {D : Type*} [Fintype D] [DecidableEq D]
def specPerm (b : Slots) (π : Perm (Fin 4)) : Perm Slots :=
  (swap none b).trans (π.optionCongr.trans (swap none b))

@[simp] theorem specPerm_self (b : Slots) (π : Perm (Fin 4)) : specPerm b π b = b := by
  simp [specPerm]

/-- The four-word spectator clasp, fixing the remaining active strand. -/
def spectator (b : Slots) (z : Raw D) : Raw D :=
  fun t c => (24:ℂ)⁻¹ * ∑ σ : Perm (Fin 4), z (t ∘ specPerm b σ.symm) c

omit [Fintype D] [DecidableEq D] in
theorem cap_spectator (S : Finset D) (P : Finset Slots) (b : Slots)
    (hP : ∀ σ : Perm (Fin 4), ∀ i, specPerm b σ i ∈ P ↔ i ∈ P)
    (z : Raw D) (w : Fin 4 → D) : portCap S P (spectator b z) w = portCap S P z w := by
  have scale (a : ℂ) (v : Raw D) : portCap S P (fun t c => a * v t c) w = a * portCap S P v w := by
    unfold portCap; simp_rw [← Finset.mul_sum]; ring
  unfold spectator
  rw [scale,cap_sum]
  simp_rw [cap_reindex S P P _ (hP _) z w]
  norm_num [Fintype.card_perm,Nat.factorial]; ring

theorem spectator_ports (b : Slots) (σ : Perm (Fin 4)) (i : Slots) :
    (specPerm b σ i ∈ ({b} : Finset Slots) ↔ i ∈ ({b} : Finset Slots)) ∧
    (specPerm b σ i ∈ ({b} : Finset Slots)ᶜ ↔ i ∈ ({b} : Finset Slots)ᶜ) := by
  have h : specPerm b σ i = b ↔ i = b := by
    simpa only [specPerm_self] using (show specPerm b σ i = specPerm b σ b ↔ i = b from (specPerm b σ).injective.eq_iff)
  simp [h]

omit [DecidableEq D] in
/-- Pythagoras for the actual normalized word clasp. -/
lemma clasp_energy_split {I : Type*} [Fintype I] [DecidableEq I] (v : (I → D) → ℂ) :
    energy v = energy (clasp v) + energy (fun w => v w-clasp v w) := by
  have h := congrArg Complex.re (bracket_clasp v v)
  rw [Coarse.bracket_self,Complex.ofReal_re] at h
  have diff : energy (fun w => v w - clasp v w) = energy v + energy (clasp v) -
      2 * (bracket v (clasp v)).re := by
    unfold energy bracket
    simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    apply Finset.sum_congr rfl; intro w _; ring
  linarith

omit [Fintype D] [DecidableEq D] in
private lemma insert_spec (b : Slots) (π : Perm (Fin 4)) (w : Fin 4 → D) (a : D) :
    insertAt b w a ∘ specPerm b π = insertAt b (w ∘ π) a := by
  funext i
  simp only [Function.comp_apply,insertAt,specPerm,Equiv.trans_apply,swap_apply_self]
  cases h : (swap none b) i <;> rfl

omit [Fintype D] [DecidableEq D] in
lemma spectator_slice (b : Slots) (z : Raw D) (w : Fin 4 → D) (a c : D) :
    spectator b z (insertAt b w a) c = clasp (fun v => z (insertAt b v a) c) w := by
  simp only [spectator,clasp,sumSlots,insert_spec,Fintype.card_fin]
  rfl

omit [DecidableEq D] in
theorem energy_slices (S : Finset D) (b : Slots) (z : Raw D) :
    rawEnergy S z = ∑ a, ∑ c ∈ S, energy (fun w => z (insertAt b w a) c) := by
  unfold rawEnergy energy
  rw [← (splitWord b).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm

omit [DecidableEq D] in
theorem spectator_energy (S : Finset D) (b : Slots) (z : Raw D) :
    rawEnergy S z = rawEnergy S (spectator b z) +
      rawEnergy S (fun w c => z w c-spectator b z w c) := by
  simp_rw [energy_slices S b,spectator_slice]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro c _
  exact clasp_energy_split _

/-- The open last cap, before merging the four spectator strands. -/
def lastTrace (S : Finset D) (b : Slots) (z : Raw D) (w : Fin 4 → D) : ℂ :=
  ∑ c ∈ S, z (insertAt b w c) c

omit [Fintype D] [DecidableEq D] in
lemma clasp_lastTrace (S : Finset D) (b : Slots) (z : Raw D) :
    clasp (lastTrace S b z) = portCap S {b} z := by
  funext w
  simp only [clasp,sumSlots,lastTrace,portCap,Finset.card_singleton,Nat.cast_one,one_mul,
    Finset.sum_singleton,Fintype.card_fin]
  congr 1
  exact inv_involutive.bijective.sum_comp (fun σ : Perm (Fin 4) =>
    ∑ c ∈ S, z (insertAt b (w ∘ σ) c) c)

omit [Fintype D] [DecidableEq D] in
lemma trace_spectator (S : Finset D) (b : Slots) (z : Raw D) :
    lastTrace S b (spectator b z) = portCap S {b} z := by
  rw [← clasp_lastTrace]
  funext w; unfold lastTrace clasp sumSlots
  simp only [spectator,insert_spec,Fintype.card_fin]
  rw [← Finset.mul_sum,Finset.sum_comm]
  rfl

/-- The two-dimensional last cap has squared norm 2. This form keeps
the four ordered spectator outputs and spends only their complementary norm. -/
theorem trace_norm (S : Finset D) (hS : S.card = 2) (b : Slots) (z : Raw D) :
    energy (lastTrace S b z) ≤ 2 * rawEnergy S z := by
  obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hS
  subst S
  unfold lastTrace energy
  rw [energy_slices _ b]
  simp only [Finset.sum_pair hij]
  have hb (w : Fin 4 → D) : Complex.normSq (z (insertAt b w i) i + z (insertAt b w j) j) ≤
      2*(Complex.normSq (z (insertAt b w i) i)+Complex.normSq (z (insertAt b w j) j)) := by
    have hn := Complex.normSq_nonneg (z (insertAt b w i) i - z (insertAt b w j) j)
    simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im] at hn ⊢
    linarith only [hn]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => hb w)
  rw [← Finset.mul_sum,Finset.sum_add_distrib] at hs
  refine hs.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  simp only [energy,Finset.sum_add_distrib]
  exact add_le_add (Finset.single_le_sum (f:=fun a => ∑ w, Complex.normSq (z (insertAt b w a) i))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
    (Finset.single_le_sum (f:=fun a => ∑ w, Complex.normSq (z (insertAt b w a) j))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j))

theorem spectator_complement (S : Finset D) (hS : S.card = 2) (b : Slots) (z : Raw D) :
    energy (lastTrace S b z) - energy (portCap S {b} z) ≤
      2*(rawEnergy S z-rawEnergy S (spectator b z)) := by
  have bound := trace_norm S hS b (fun w c => z w c - spectator b z w c)
  have eq : lastTrace S b (fun w c => z w c - spectator b z w c) =
      fun w => lastTrace S b z w - portCap S {b} z w := by
    rw [← trace_spectator]; funext w; simp [lastTrace,Finset.sum_sub_distrib]
  rw [eq] at bound
  have hsplit := clasp_energy_split (lastTrace S b z)
  rw [clasp_lastTrace] at hsplit
  linarith only [bound,hsplit,spectator_energy S b z]

open FourQuadratic in
/-- The complete supported form from (5C.3), on ordered word coordinates.
The first row is the unprojected proper half. Its last cap is closed before
the remaining four spectator strands are symmetrized. -/
theorem full_word_bound (S : Finset D) (hS : S.card = 2) (b : Slots)
    (PW : Fin 2 → Finset Slots) (PV : Fin 1 → Finset Slots)
    (hW : ∀ i, (PW i).card = d23 i + 1) (hV : ∀ i, (PV i).card = d5 i + 1)
    (hDW : ∀ i j, i≠j → Disjoint (PW i) (PW j))
    (U W V : Raw D) (x y fullW : (Fin 4 → D) → ℂ)
    (hu₀ : ∀ t, portCap S ({b} : Finset Slots)ᶜ U t = y t)
    (hu₁ : ∀ t, portCap S {b} U t = x t)
    (hw : ∀ i t, portCap S (PW i) W t = ![y t,fullCapMean 2 (x t) (y t)] i)
    (hv : ∀ i t, portCap S (PV i) V t = fullCapMean 3 (x t) (y t))
    (hwFull : ∀ t, clasp fullW t = fullCapMean 2 (x t) (y t)) :
    0 ≤ 24*rawEnergy S U + 144*rawEnergy S W + 1080*rawEnergy S V +
      1350*energy (fun t => fullCapMean 3 (x t) (y t)-x t/15) +
      108*energy fullW - 12*energy (lastTrace S b U) - 24*energy x := by
  let PU : Fin 2 → Finset Slots := ![({b} : Finset Slots)ᶜ,{b}]
  have hU (i : Fin 2) : (PU i).card = d41 i + 1 := by
    fin_cases i <;> simp [PU,d41,Finset.card_compl,Fintype.card_option]
  have dU (i j : Fin 2) (hij : i≠j) : Disjoint (PU i) (PU j) := by
    fin_cases i <;> fin_cases j <;> simp_all [PU]
  have hsp (i : Fin 2) (t) : portCap S (PU i) (spectator b U) t = ![y t,x t] i := by
    fin_cases i
    · exact (cap_spectator S _ b (fun σ i => (spectator_ports b σ i).2) U t).trans (hu₀ t)
    · exact (cap_spectator S _ b (fun σ i => (spectator_ports b σ i).1) U t).trans (hu₁ t)
  have hp := four_word_bound S hS PU PW PV hU hW hV dU hDW (spectator b U) W V x y hsp hw hv
  have hc := spectator_complement S hS b U
  rw [funext hu₁] at hc
  have hwEnergy : energy (fun t => fullCapMean 2 (x t) (y t)) ≤ energy fullW := by
    have e := clasp_energy_split fullW
    rw [funext hwFull] at e
    have pos : 0 ≤ energy (fun t => fullW t - fullCapMean 2 (x t) (y t)) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    linarith only [e,pos]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hp
  unfold energy at hc hwEnergy ⊢
  linarith only [hp,hc,hwEnergy]

end
end BlockPermanents.FourLastCaps
