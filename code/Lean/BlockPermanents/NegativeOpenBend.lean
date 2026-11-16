import BlockPermanents.OccupationBasis
import Mathlib.Data.Nat.Choose.Central

/-! # The negative two-packet direction in Remark 3A.5

Use the delta word with one constant colour per packet. The whole-packet
clasp averages two words, while the fine clasp averages their full orbit.
Their difference is an eigenvector of the actual two-packet defect.
-/
namespace BlockPermanents.NegativeOpenBend
open Closures
noncomputable section

abbrev Slots (k : ℕ) := Fin 2 × Fin k
abbrev State (d k : ℕ) := (Slots k → Fin d) → ℂ

private def exchange (k : ℕ) : Equiv.Perm (Slots k) :=
  (Equiv.swap 0 1).prodCongr (Equiv.refl (Fin k))

private theorem flip_flip {k d : ℕ} (w : Slots k → Fin d) :
    (w ∘ exchange k) ∘ exchange k = w := by
  funext ⟨i,j⟩; simp [exchange]

private theorem packet_two {k d : ℕ} (f : State d k) (w : Slots k → Fin d) :
    packetClasp f w = (f w + f (w ∘ exchange k))/2 := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  simp [packetClasp,clasp,sumSlots,hu,show (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 by decide,
    Nat.factorial,div_eq_mul_inv,mul_comm,exchange]
  rfl

private theorem fine_packet {k d : ℕ} (f : State d k) : clasp (packetClasp f) = clasp f := by
  have h := sumSlots_absorb (exchange k).symm f
  simp only [Equiv.symm_symm] at h
  funext w
  have hf := congrFun h w
  unfold sumSlots at hf
  simp only [clasp,sumSlots,packet_two,← Finset.sum_div,Finset.sum_add_distrib,hf]
  ring

private theorem fine_twice {k d : ℕ} (f : State d k) : clasp (clasp f) = clasp f := by
  funext w
  change ((Fintype.card (Slots k)).factorial:ℂ)⁻¹ *
    (∑ p : Equiv.Perm (Slots k), clasp f (w ∘ p.symm)) = _
  simp only [clasp_invariant,Finset.sum_const,Finset.card_univ,Fintype.card_perm,nsmul_eq_mul]
  field_simp [Nat.factorial_ne_zero]

/-- Two distinct orthonormal coordinate directions, one on each packet. -/
def input {k d : ℕ} (a : Fin 2 ↪ Fin d) : State d k :=
  fun w => if w = (fun i => a i.1) then 1 else 0

/-- The manuscript's w=(R₂−E₂)(x^k ⊗ y^k) on ordinary thin-word coordinates. -/
def witness {k d : ℕ} (a : Fin 2 ↪ Fin d) : State d k :=
  packetClasp (input a) - clasp (input a)

theorem fine_zero {k d : ℕ} (a : Fin 2 ↪ Fin d) : clasp (witness (k:=k) a) = 0 := by
  have h {f g : State d k} : clasp (f-g) = clasp f - clasp g := by
    funext w; simp [clasp,sumSlots,Finset.sum_sub_distrib,mul_sub]
  rw [witness,h,fine_packet,fine_twice,sub_self]

private theorem fixed_flip {k d : ℕ} (a : Fin 2 ↪ Fin d) (w : Slots k → Fin d) :
    witness a (w ∘ exchange k) = witness a w := by
  have h := clasp_invariant (input (k:=k) a) (exchange k).symm w
  simp only [Equiv.symm_symm] at h
  simp only [witness, Pi.sub_apply,packet_two,flip_flip,h,add_comm]

/-- Both independent internal clasps fix this direction, so the vector is
on the ordinary two-packet boundary. -/
theorem internal_symmetric {k d : ℕ} (a : Fin 2 ↪ Fin d)
    (p : Fin 2 → Equiv.Perm (Fin k)) (u : Slots k → Fin d) :
    witness a (u ∘ withinPackets p) = witness a u := by
  let q := withinPackets p
  have eqv (e : Equiv.Perm (Slots k)) (v t : Slots k → Fin d) :
      v ∘ e = t ↔ v = t ∘ e.symm := by
    constructor
    · intro h; funext i; simpa using congrFun h (e.symm i)
    · intro h; funext i; simpa using congrFun h (e i)
  have swapv (v : Slots k → Fin d) :
      v ∘ exchange k = (fun i => a i.1) ↔ v = (fun i => a i.1) ∘ exchange k := by
    constructor <;> rintro h
    · rw [← h,flip_flip]
    · rw [h,flip_flip]
  have hf := clasp_invariant (input a) q.symm u
  simp only [Equiv.symm_symm] at hf
  simp only [witness, Pi.sub_apply,packet_two,input,swapv]
  dsimp only [q] at hf
  simp only [eqv (withinPackets p) u, hf]
  rfl

theorem eigenvector {k d : ℕ} (a : Fin 2 ↪ Fin d) :
    defect (witness (k:=k) a) = (-2:ℂ) • witness a := by
  funext w
  simp only [defect, fine_zero, Pi.zero_apply,mul_zero,packet_two,fixed_flip,
    Fintype.card_fin,Pi.smul_apply,smul_eq_mul]
  norm_num

private theorem fine_value {k d : ℕ} (a : Fin 2 ↪ Fin d) :
    clasp (input (k:=k) a) (fun i => a i.1) = 1/((2*k).choose k : ℂ) := by
  let z : Slots k → Fin 2 := Prod.fst
  have test (p : Equiv.Perm (Slots k)) :
      ((fun i : Slots k => a i.1) ∘ p.symm = fun i => a i.1) ↔ z = z ∘ p.symm := by
    constructor <;> intro hh <;> funext i
    · exact (a.injective (congrFun hh i)).symm
    · exact congrArg a (congrFun hh i).symm
  have hs (p : Equiv.Perm (Slots k)) : z = z ∘ p.symm ↔ z = z ∘ p := by
    constructor
    · intro h; funext i; simpa [Function.comp_def] using (congrFun h (p i)).symm
    · intro h; funext i; simpa [Function.comp_def] using (congrFun h (p.symm i)).symm
  have hv (j : Fin 2) : OccupationBasis.occ z j = k := by
    let e : OccupationBasis.Fiber z j ≃ Fin k :=
      { toFun := fun i => i.val.2, invFun := fun i => ⟨(j,i),rfl⟩
        left_inv := fun ⟨⟨u,v⟩,h⟩ => by subst j; rfl, right_inv := fun _ => rfl }
    rw [← OccupationBasis.fiber_card, Fintype.card_congr e,Fintype.card_fin]
  have hc := OccupationBasis.kernel_count z z
  simp only [if_true,hv,Fin.prod_univ_two] at hc
  have hfac : (2*k).choose k * k.factorial * k.factorial = (2*k).factorial := by
    simpa only [show 2*k = k+k by omega] using Nat.add_choose_mul_factorial_mul_factorial k k
  simp only [clasp,sumSlots,input,test,hs,Finset.sum_boole,← Fintype.card_subtype,hc, Fintype.card_prod,
    Fintype.card_fin,Nat.cast_mul]
  have hh : ((2*k).choose k:ℂ) * k.factorial * k.factorial = (2*k).factorial := by
    exact_mod_cast hfac
  have hn : ((2*k).choose k:ℂ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero k
  field_simp [hn,Nat.factorial_ne_zero]
  linear_combination hh

private theorem distinct {k d : ℕ} (hk : 0 < k) (a : Fin 2 ↪ Fin d) :
    (fun i : Slots k => a i.1) ∘ exchange k ≠ fun i => a i.1 := by
  intro h
  have hh := a.injective (congrFun h (0,⟨0,hk⟩))
  simp [exchange] at hh

private theorem value {k d : ℕ} (hk : 0 < k) (a : Fin 2 ↪ Fin d) :
    witness (k:=k) a (fun i => a i.1) = 1/2 - 1/((2*k).choose k:ℂ) := by
  simp [witness,packet_two,input,distinct hk a,fine_value]

/-- Squared norm in the actual complex word-space inner product. -/
theorem norm_sq {k d : ℕ} (hk : 0 < k) (a : Fin 2 ↪ Fin d) :
    bracket (witness (k:=k) a) (witness a) = 1/2 - 1/((2*k).choose k:ℂ) := by
  let z : Slots k → Fin d := fun i => a i.1
  let w := witness (k:=k) a
  have horth : bracket w (clasp (input a)) = 0 := by
    rw [← bracket_clasp,show clasp w = 0 from fine_zero a]
    simp [bracket]
  have split : bracket w w = bracket w (packetClasp (input a)) - bracket w (clasp (input a)) := by
    simp only [w,witness,bracket,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  have he (u : Slots k → Fin d) : u ∘ exchange k = z ↔ u = z ∘ exchange k := by
    constructor <;> rintro h
    · rw [← h, flip_flip]
    · rw [h, flip_flip]
  rw [split,horth,sub_zero]
  change (∑ u, star (w u)*packetClasp (input a) u) = _
  simp only [packet_two,input,show (fun i : Slots k => a i.1) = z from rfl,he,mul_div_assoc',
    mul_add,mul_ite,mul_one,mul_zero,← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]
  simp [w,z, fixed_flip,value hk a]

theorem nonzero {k d : ℕ} (hk : 2 ≤ k) (a : Fin 2 ↪ Fin d) : witness (k:=k) a ≠ 0 := by
  have hc : 2 < (2*k).choose k := by
    have h := Nat.choose_le_centralBinom 1 k
    rw [Nat.choose_one_right] at h
    change 2*k ≤ (2*k).choose k at h
    omega
  intro h
  have hh := norm_sq (by omega : 0 < k) a
  rw [h] at hh
  have hp : (2:ℝ) < ((2*k).choose k : ℝ) := by exact_mod_cast hc
  have hpos : (0:ℝ) < 1/2 - 1/((2*k).choose k:ℝ) := by
    have := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<2) hp
    linarith
  have hn : (1/2 - 1/((2*k).choose k:ℂ) : ℂ) ≠ 0 := by
    have hreal := Complex.ofReal_ne_zero.mpr hpos.ne'
    push_cast at hreal
    exact hreal
  exact hn (by simpa [bracket] using hh.symm)

/-- Every fine half in the next marked opening annihilates the witness,
for every marked k-packet and every cut order. -/
theorem fine_cuts {k d : ℕ} (a : Fin 2 ↪ Fin d) (l : Bend.Word d k → ℂ)
    (r : Bend.CutIndex (2*k) k) :
    (Bend.wordCap d (2*k) k r).mulVec
      (Bend.product (clasp (fun u : Bend.Word d (2*k) => witness a (u ∘ finProdFinEquiv))) l) = 0 := by
  have hf : clasp (fun u : Bend.Word d (2*k) => witness a (u ∘ finProdFinEquiv)) = 0 := by
    funext w
    rw [Bridges.clasp_transport, fine_zero]; rfl
  rw [hf]
  have hprod : Bend.product (0 : Bend.Word d (2*k) → ℂ) l = 0 := by funext w; simp [Bend.product]
  rw [hprod, Matrix.mulVec_zero]

end
end BlockPermanents.NegativeOpenBend
