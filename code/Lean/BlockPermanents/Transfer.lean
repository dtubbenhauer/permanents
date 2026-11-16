import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# Packet transfer (Lemma `lem:tr-transfer`)

An operator algebra with a representation of the packet permutations is enough.
The outer `none` labels the spectator, `some none` labels the first ordinary
packet and `some (some j)` labels every other packet.
-/

namespace BlockPermanents.Transfer
open scoped BigOperators
open Equiv

variable {R G H : Type*} [Ring R] [Algebra ℚ R] [Group G] [Fintype G]
  [Group H] [Fintype H]

/-- Conjugate both ends by the same permutation, then average. -/
noncomputable def bracket (ρ : G →* R) : R →ₗ[ℚ] R where
  toFun B := (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ρ g * B * ρ g⁻¹
  map_add' X Y := by simp [mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' r X := by
    simp only [mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum, RingHom.id_apply]
    exact smul_comm _ _ _

private theorem conj_invariant (ρ : G →* R) (p : G) (B : R) :
    bracket ρ (ρ p * B * ρ p⁻¹) = bracket ρ B := by
  apply congrArg (fun X : R => (Fintype.card G : ℚ)⁻¹ • X)
  have h := (Group.mulRight_bijective p).sum_comp (fun g : G => ρ g * B * ρ g⁻¹)
  simpa only [map_mul, mul_inv_rev, mul_assoc] using h

theorem slide (ρ : G →* R) (p : G) (B : R) :
    bracket ρ (ρ p * B) = bracket ρ (B * ρ p) := by
  have h := conj_invariant ρ p (B * ρ p)
  simpa only [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] using h

/-- The average of all operators of a finite group. -/
noncomputable def clasp (π : H →* R) : R :=
  (Fintype.card H : ℚ)⁻¹ • ∑ h : H, π h

theorem absorb_left (π : H →* R) (h : H) : π h * clasp π = clasp π := by
  unfold clasp
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [← map_mul]
  rw [(Group.mulLeft_bijective h).sum_comp π]

theorem absorb_right (π : H →* R) (h : H) : clasp π * π h = clasp π := by
  unfold clasp
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [← map_mul]
  rw [(Group.mulRight_bijective h).sum_comp π]

theorem clasp_sq (π : H →* R) : clasp π * clasp π = clasp π := by
  nth_rw 1 [clasp]
  simp only [smul_mul_assoc, Finset.sum_mul, absorb_left, Finset.sum_const, Finset.card_univ]
  have hc : (Fintype.card H : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hc]

private theorem slide_clasp (ρ : G →* R) (i : H →* G) (X : R) :
    bracket ρ (clasp (ρ.comp i) * X) = bracket ρ (X * clasp (ρ.comp i)) := by
  simp only [clasp, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
    map_smul, map_sum, MonoidHom.comp_apply, slide]

/-- Extend a packet permutation by the identity on a spectator. -/
def liftPerm {α : Type*} : Perm α →* Perm (Option α) where
  toFun := Equiv.optionCongr
  map_one' := Equiv.optionCongr_one
  map_mul' a b := (Equiv.optionCongr_trans b a).symm

private lemma lift_id {α : Type*} [DecidableEq α] (g : Perm (Option α)) (h : g none = none) :
    liftPerm g.removeNone = g := by
  change g.removeNone.optionCongr = g
  simp [map_equiv_removeNone, h, ← Equiv.Perm.one_def]

private theorem exit_value {α : Type*} [DecidableEq α] [Fintype α]
    (ρ : Perm (Option α) →* R) (B : R) (a : α)
    (hL : ∀ g : Perm (Option α), g none = none → ρ g * B = B)
    (hR : ∀ g : Perm (Option α), g none = none → B * ρ g = B)
    (g : Perm (Option α)) (hg : g none ≠ none) :
    bracket ρ (B * ρ g) = bracket ρ (B * ρ (swap none (some a))) := by
  let t := swap none (some a)
  let q := swap (g none) (some a)
  let v := t * q * g
  have hq : q none = none := swap_apply_of_ne_of_ne (Ne.symm hg) (by simp)
  have hv : v none = none := by simp [v, q, t, Perm.mul_apply]
  have hfac : q * t * v = g := by
    calc
      q * t * v = q * (t * t) * q * g := by simp only [v, mul_assoc]
      _ = g := by rw [Equiv.swap_mul_self, mul_one, Equiv.swap_mul_self, one_mul]
  calc
    bracket ρ (B * ρ g) = bracket ρ ((B * ρ q) * ρ t * ρ v) := by
      rw [← hfac]; simp only [map_mul, mul_assoc]
    _ = bracket ρ (ρ v * (B * ρ t)) := by rw [hR q hq, slide]
    _ = bracket ρ (B * ρ t) := by rw [← mul_assoc, hL v hv]

omit [Algebra ℚ R] in
private theorem count_exits {α : Type*} [Fintype α] [DecidableEq α] (X Y : R) :
    (∑ p : Perm (Option α), if p none = none then X else Y) =
      (Fintype.card α).factorial • (X + Fintype.card α • Y) := by
  rw [Finset.univ_perm_option, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product,
    Equiv.Perm.decomposeOption_symm_apply, Perm.mul_apply, optionCongr_apply,
    Option.map_none, swap_apply_left, Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  simp [Fintype.sum_option, Fintype.card_perm, nsmul_add, ← mul_assoc,
    (Nat.cast_commute (Fintype.card α) ((Fintype.card α).factorial : R)).eq]


private theorem relabeled_average {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Perm (Option (Option α)) →* R) (B : R) (a : α)
    (hL : ∀ g : Perm (Option (Option α)), g none = none → ρ g * B = B)
    (hR : ∀ g : Perm (Option (Option α)), g none = none → B * ρ g = B) :
    let f := clasp (ρ.comp liftPerm)
    let s : Perm (Option (Option α)) := swap none (some none)
    let t : Perm (Option (Option α)) := swap none (some (some a))
    ((Fintype.card α : ℚ) + 1) • bracket ρ (B * (ρ s * f * ρ s)) =
      bracket ρ B + Fintype.card α • bracket ρ (B * ρ t) := by
  classical
  dsimp only
  let s : Perm (Option (Option α)) := swap none (some none)
  let t : Perm (Option (Option α)) := swap none (some (some a))
  have hex (p : Perm (Option α)) : bracket ρ (B * ρ (s * liftPerm p * s)) =
      if p none = none then bracket ρ B else bracket ρ (B * ρ t) := by
    have hi : (s * liftPerm p * s) none = none ↔ p none = none := by
      change s ((liftPerm p) (s none)) = none ↔ _
      rw [show s none = some none from swap_apply_left _ _]
      change s (some (p none)) = none ↔ _
      rw [← show s (some none) = none from swap_apply_right _ _, s.injective.eq_iff]
      simp
    split_ifs with h
    · rw [hR _ (hi.mpr h)]
    · exact exit_value ρ B (some a) hL hR _ (fun e => h (hi.mp e))
  change ((Fintype.card α : ℚ) + 1) • bracket ρ (B * (ρ s * clasp (ρ.comp liftPerm) * ρ s)) = _
  simp only [clasp, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul,
    map_smul, map_sum, MonoidHom.comp_apply]
  simp_rw [← map_mul, hex]
  rw [count_exits, Fintype.card_perm, Fintype.card_option, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add_one, ← Nat.cast_smul_eq_nsmul ℚ (Fintype.card α).factorial,
    smul_smul, smul_smul]
  have hfac : ((Fintype.card α).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcard : (Fintype.card α : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (Fintype.card α)
  rw [show ((Fintype.card α : ℚ) + 1) *
      (((Fintype.card α : ℚ) + 1) * (Fintype.card α).factorial)⁻¹ *
      (Fintype.card α).factorial = 1 by field_simp, one_smul]

/-- Packet transfer for `n = |α| + 1` ordinary packets and one spectator.
`a` chooses the ordinary packet in the swap `t`, so `n ≥ 2`. The sole
operator hypothesis is two-sided clasp absorption. The ambient representation
can, in particular, act by packet permutations on a tensor power. -/
theorem packet_transfer {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Perm (Option (Option α)) →* R) (a : α) (B : R)
    (hB : B = clasp (ρ.comp liftPerm) * B * clasp (ρ.comp liftPerm)) :
    let f := clasp (ρ.comp liftPerm)
    let s : Perm (Option (Option α)) := swap none (some none)
    let t : Perm (Option (Option α)) := swap none (some (some a))
    bracket ρ B = ((Fintype.card α : ℚ) + 1) • bracket ρ (f * (ρ s * B * ρ s) * f) -
      ((Fintype.card α : ℚ) / 2) • (bracket ρ (B * ρ t * f) + bracket ρ (f * ρ t * B)) := by
  classical
  let f := clasp (ρ.comp liftPerm)
  let s : Perm (Option (Option α)) := swap none (some none)
  let t : Perm (Option (Option α)) := swap none (some (some a))
  change bracket ρ B = ((Fintype.card α : ℚ) + 1) • bracket ρ (f * (ρ s * B * ρ s) * f) -
      ((Fintype.card α : ℚ) / 2) • (bracket ρ (B * ρ t * f) + bracket ρ (f * ρ t * B))
  have hsq : f * f = f := clasp_sq _
  have hfb : f * B = B := by
    calc
      f * B = f * (f * B * f) := congrArg (fun X => f * X) hB
      _ = f * B * f := by rw [← mul_assoc, ← mul_assoc, hsq]
      _ = B := hB.symm
  have hbf : B * f = B := by
    calc
      B * f = (f * B * f) * f := congrArg (fun X => X * f) hB
      _ = f * B * f := by rw [mul_assoc (f * B), hsq]
      _ = B := hB.symm
  have hL (g : Perm (Option (Option α))) (hg : g none = none) : ρ g * B = B := by
    calc
      ρ g * B = ρ g * (f * B) := by rw [hfb]
      _ = B := by rw [← mul_assoc, ← lift_id g hg, show ρ (liftPerm g.removeNone) * f = f from
                    absorb_left (ρ.comp liftPerm) _, hfb]
  have hR (g : Perm (Option (Option α))) (hg : g none = none) : B * ρ g = B := by
    calc
      B * ρ g = (B * f) * ρ g := by rw [hbf]
      _ = B := by rw [mul_assoc, ← lift_id g hg, show f * ρ (liftPerm g.removeNone) = f from
                    absorb_right (ρ.comp liftPerm) _, hbf]
  have hs (X : R) : bracket ρ (f * X) = bracket ρ (X * f) := slide_clasp ρ liftPerm X
  have hmain : bracket ρ (f * (ρ s * B * ρ s) * f) = bracket ρ (B * (ρ s * f * ρ s)) := by
    calc
      _ = bracket ρ (((ρ s * B * ρ s) * f) * f) := by rw [mul_assoc f, hs]
      _ = bracket ρ (ρ s * (B * (ρ s * f))) := by rw [mul_assoc _ f f, hsq]; simp [mul_assoc]
      _ = _ := by rw [slide]; simp [mul_assoc]
  have hcross₁ : bracket ρ (B * ρ t * f) = bracket ρ (B * ρ t) := by
    rw [← hs, ← mul_assoc, hfb]
  have hcross₂ : bracket ρ (f * ρ t * B) = bracket ρ (B * ρ t) := by
    rw [mul_assoc f, hs, mul_assoc, slide, hbf]
  rw [hmain, hcross₁, hcross₂, relabeled_average ρ B a hL hR, ← two_smul ℚ,
    smul_smul, div_mul_cancel₀ _ (by decide : (2 : ℚ) ≠ 0), Nat.cast_smul_eq_nsmul, add_sub_cancel_right]

/-- Permute the slots of a tensor expressed in a product basis. A word
`w : ι → D` chooses one basis label for each packet. -/
def tensorAction (ι D : Type*) : Perm ι →* Module.End ℂ ((ι → D) → ℂ) where
  toFun p := {
    toFun := fun z w => z (w ∘ p)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The same transfer on the operator algebra of a packet tensor power. -/
theorem tensor_packet_transfer {α D : Type*} [Fintype α] [DecidableEq α]
    (a : α) (B : Module.End ℂ ((Option (Option α) → D) → ℂ))
    (hB : let ρ := tensorAction (Option (Option α)) D
          B = clasp (ρ.comp liftPerm) * B * clasp (ρ.comp liftPerm)) :
    let ρ := tensorAction (Option (Option α)) D
    let f := clasp (ρ.comp liftPerm)
    let s : Perm (Option (Option α)) := swap none (some none)
    let t : Perm (Option (Option α)) := swap none (some (some a))
    bracket ρ B = ((Fintype.card α : ℚ) + 1) • bracket ρ (f * (ρ s * B * ρ s) * f) -
      ((Fintype.card α : ℚ) / 2) • (bracket ρ (B * ρ t * f) + bracket ρ (f * ρ t * B)) :=
  packet_transfer _ a B hB

end BlockPermanents.Transfer
