import BlockPermanents.FourTarget
import BlockPermanents.WireSchur

/-! Compressing the three concrete Schur expansions to packet-symmetric
inputs and outputs in the four-quadratic transfer. -/
namespace BlockPermanents.FourLocalCompression
open FourTarget TransferBlocks Closures
open scoped BigOperators
noncomputable section

local instance (n : ℕ) : Fintype (group 2 n) := Fintype.ofFinite _

def withinHom : (Fin 4 → Equiv.Perm (Fin 2)) →* Wire 2 where
  toFun := withinPackets
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The orthogonal projection onto independently symmetric quadratic packets. -/
def W (d : ℕ) : Op d 2 := Transfer.clasp ((act d 2).comp withinHom)

def eWire : Wire 2 := Equiv.swap (0,1) (3,1)
def tWire : Wire 2 := wires 2 swap14

theorem W_idem (d : ℕ) : W d * W d = W d := Transfer.clasp_sq _

theorem W_absorbs (d : ℕ) (p : Fin 4 → Equiv.Perm (Fin 2)) :
    act d 2 (withinHom p) * W d = W d ∧ W d * act d 2 (withinHom p) = W d :=
  ⟨Transfer.absorb_left ((act d 2).comp withinHom) p,
    Transfer.absorb_right ((act d 2).comp withinHom) p⟩

private theorem average_fixed {G I : Type*} [Fintype G] [Group G]
    (ρ : G →* Module.End ℂ (I → ℂ)) (v : I → ℂ) (h : ∀ g, ρ g v = v) :
    Transfer.clasp ρ v = v := by
  simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,h,Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) v

theorem W_flatPackets {d : ℕ} (x : Fin 4 → Fin 2 → Fin d → ℂ) :
    W d (flatPackets x) = flatPackets x := by
  apply average_fixed
  intro p
  funext w
  change (∏ i, packet (x i) (fun j => w (i,p i j))) = ∏ i, packet (x i) (fun j => w (i,j))
  apply Finset.prod_congr rfl
  intro i _
  have h := Bridges.packet_symmetric d 2 (x i)
  rw [Bend.Symmetric,Bridges.symClasp_action] at h
  simpa only [Equiv.symm_symm,h] using
    clasp_invariant (packet (x i)) (p i).symm (fun j => w (i,j))

private theorem move_perm {d : ℕ} (z y : (Slot 2 → Fin d) → ℂ) (p : Wire 2) :
    bracket z (act d 2 p y) = bracket (act d 2 p⁻¹ z) y := by
  let e := p.symm.arrowCongr (Equiv.refl (Fin d))
  simpa [e,bracket,Function.comp_def,act,Transfer.tensorAction] using
    e.sum_comp (fun w => (starRingEnd ℂ) (z (w ∘ p.symm)) * y w)

private theorem W_pair_flat {d : ℕ} (x : Fin 4 → Fin 2 → Fin d → ℂ) (v : (Slot 2 → Fin d) → ℂ) :
    bracket (flatPackets x) (W d v) = bracket (flatPackets x) v := by
  let z := flatPackets x
  have fixp (p : Fin 4 → Equiv.Perm (Fin 2)) : act d 2 (withinHom p) z = z := by
    calc
      _ = act d 2 (withinHom p) (W d z) := by rw [W_flatPackets]
      _ = (act d 2 (withinHom p) * W d) z := rfl
      _ = z := by rw [(W_absorbs d p).1,W_flatPackets]
  have hm (p : Fin 4 → Equiv.Perm (Fin 2)) :
      bracket z (act d 2 (withinHom p) v) = bracket z v := by
    rw [move_perm,← map_inv,fixp]
  let na := Fintype.card (Fin 4 → Equiv.Perm (Fin 2))
  have hB (f : (Fin 4 → Equiv.Perm (Fin 2)) → ((Slot 2 → Fin d) → ℂ)) :
      bracket z (((na:ℚ)⁻¹) • ∑ p, f p) = (na:ℂ)⁻¹ * ∑ p, bracket z (f p) := by
    simp only [bracket, Pi.smul_apply, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, smul_eq_mul,
      Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro p _
    ring
  change bracket z ((Transfer.clasp ((act d 2).comp withinHom)) v) = bracket z v
  simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply]
  rw [hB]
  simp only [MonoidHom.comp_apply,hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc]
  rw [inv_mul_cancel₀ (show (na:ℂ)≠0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_mul]

theorem compression_bracket {d : ℕ} (x y : Fin 4 → Fin 2 → Fin d → ℂ) (A : Op d 2) :
    bracket (flatPackets x) ((W d * A * W d) (flatPackets y)) =
      bracket (flatPackets x) (A (flatPackets y)) := by
  simp only [Module.End.mul_apply,W_flatPackets,W_pair_flat]

variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem avg_mul_fixed {G : Type*} [Fintype G] [Group G] (ρ : G →* R) (a : R)
    (h : ∀ g, ρ g*a = a) : Transfer.clasp ρ*a = a := by
  simp only [Transfer.clasp,smul_mul_assoc,Finset.sum_mul,h,Finset.sum_const,Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) a

theorem mul_avg_fixed {G : Type*} [Fintype G] [Group G] (ρ : G →* R) (a : R)
    (h : ∀ g, a*ρ g = a) : a*Transfer.clasp ρ = a := by
  simp only [Transfer.clasp,mul_smul_comm,Finset.mul_sum,h,Finset.sum_const,Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ]
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) a

theorem mul_avg_comm {G : Type*} [Fintype G] [Group G] (ρ : G →* R) (a : R)
    (h : ∀ g, a*ρ g = ρ g*a) : a*Transfer.clasp ρ = Transfer.clasp ρ*a := by
  simp only [Transfer.clasp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,h]

theorem row_preserving {p : Wire 2} (h : ∀ a, (p a).1 = a.1) :
    ∃ t : Fin 4 → Equiv.Perm (Fin 2), withinHom t = p := by
  let f (i : Fin 4) (j : Fin 2) : Fin 2 := (p (i,j)).2
  have hi (i : Fin 4) : Function.Injective (f i) := by
    intro a b he
    exact congrArg Prod.snd (p.injective (Prod.ext ((h (i,a)).trans (h (i,b)).symm) he))
  refine ⟨fun i => Equiv.ofBijective (f i) ⟨hi i,Finite.surjective_of_injective (hi i)⟩,?_⟩
  ext ⟨i,j⟩ : 1
  exact Prod.ext (h (i,j)).symm rfl

theorem row_preserving_of_single {p : Wire 2} (i : Fin 4) (h : ∀ a, a.1 ≠ i → p a = a) :
    ∀ a, (p a).1 = a.1 := by
  intro a
  by_cases ha : a.1 = i
  · rw [ha]
    by_contra hn
    have he : p a = a := p.injective (h (p a) hn)
    rw [he,ha] at hn
    exact hn rfl
  · rw [h a ha]

theorem single_wire_absorbed (d : ℕ) (p : Wire 2) (i : Fin 4) (h : ∀ a, a.1 ≠ i → p a = a) :
    act d 2 p * W d = W d ∧ W d * act d 2 p = W d := by
  obtain ⟨t,rfl⟩ := row_preserving (row_preserving_of_single i h)
  exact W_absorbs d t

theorem first_packet_absorbed (d : ℕ) :
    localClasp d 2 1 * W d = W d ∧ W d * localClasp d 2 1 = W d := by
  have h (p : group 2 1) := single_wire_absorbed d p 0 (fun a ha => p.property a (by
    have hne : a.1.val ≠ 0 := fun hh => ha (Fin.ext hh)
    omega))
  exact ⟨avg_mul_fixed _ _ fun p => (h p).1,mul_avg_fixed _ _ fun p => (h p).2⟩

theorem W_comm_packet (d : ℕ) (σ : FourPerm) :
    W d * packets d 2 σ = packets d 2 σ * W d := by
  let e := σ.symm.arrowCongr (Equiv.refl (Equiv.Perm (Fin 2)))
  simp only [W,Transfer.clasp,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]
  congr 1
  apply Fintype.sum_equiv e
  intro i
  change act d 2 (withinHom i) * act d 2 (wires 2 σ) =
    act d 2 (wires 2 σ) * act d 2 (withinHom (e i))
  rw [← map_mul,← map_mul]
  rfl

theorem W_comm_triple (d : ℕ) :
    W d * triple (packets d 2 swap12) (packets d 2 swap23) =
      triple (packets d 2 swap12) (packets d 2 swap23) * W d := by
  have hr {a b : Op d 2} (ha : W d * a = a * W d) (hb : W d * b = b * W d) :
      W d * (a*b) = (a*b) * W d := by rw [← mul_assoc,ha,mul_assoc,hb,mul_assoc]
  have hu := W_comm_packet d swap12
  have hv := W_comm_packet d swap23
  simp only [triple, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    hu,hv,hr hu hv,hr hv hu,hr (hr hu hv) hu]

omit [Algebra ℚ R] in
theorem absorb_conjugate (a f x y : R) (hfL : f*a=f) (hfR : a*f=f)
    (xy : x = a*y*a) : f*x*f = f*y*f := by
  rw [xy]
  calc
    _ = (f*a)*y*(a*f) := by simp only [mul_assoc]
    _ = _ := by rw [hfL,hfR]

omit [Algebra ℚ R] in
private theorem unit_cancels {G : Type*} [Group G] (ρ : G →* R) (g : G) :
    ρ g⁻¹ * ρ g = 1 := by rw [← map_mul,inv_mul_cancel,map_one]

omit [Algebra ℚ R] in
theorem commute_from_conj {G : Type*} [Group G] (ρ : G →* R) (g : G) (a : R)
    (h : ρ g*a*ρ g⁻¹=a) : ρ g*a=a*ρ g := by
  calc
    _ = (ρ g*a*ρ g⁻¹)*ρ g := by rw [mul_assoc (ρ g*a),unit_cancels,mul_one]
    _ = _ := by rw [h]

end
end BlockPermanents.FourLocalCompression
