import BlockPermanents.FourLocalCompression

/-! # Packetwise compression at arbitrary thickness -/
namespace BlockPermanents.FourThickCompression
open FourTarget TransferBlocks Closures
open FourLocalCompression (avg_mul_fixed mul_avg_fixed)
open scoped BigOperators
noncomputable section
local instance (k n : ℕ) : Fintype (group k n) := Fintype.ofFinite _

def withinHom (k : ℕ) : (Fin 4 → Equiv.Perm (Fin k)) →* Wire k where
  toFun := withinPackets
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The orthogonal projection onto independently symmetric packets. -/
def W (d k : ℕ) : Op d k := Transfer.clasp ((act d k).comp (withinHom k))

theorem W_idem (d k : ℕ) : W d k * W d k = W d k := Transfer.clasp_sq _

theorem W_absorbs (d k : ℕ) (p : Fin 4 → Equiv.Perm (Fin k)) :
    act d k (withinHom k p) * W d k = W d k ∧ W d k * act d k (withinHom k p) = W d k :=
  ⟨Transfer.absorb_left ((act d k).comp (withinHom k)) p,
    Transfer.absorb_right ((act d k).comp (withinHom k)) p⟩

theorem row_preserving {k} {p : Wire k} (h : ∀ a, (p a).1 = a.1) :
    ∃ t : Fin 4 → Equiv.Perm (Fin k), withinHom k t = p := by
  let f (i : Fin 4) (j : Fin k) : Fin k := (p (i,j)).2
  have hi (i : Fin 4) : Function.Injective (f i) := by
    intro a b he
    exact congrArg Prod.snd (p.injective (Prod.ext ((h (i,a)).trans (h (i,b)).symm) he))
  refine ⟨fun i => Equiv.ofBijective (f i) ⟨hi i,Finite.surjective_of_injective (hi i)⟩,?_⟩
  ext ⟨i,j⟩ : 1
  exact Prod.ext (h (i,j)).symm rfl

theorem row_preserving_of_single {k} {p : Wire k} (i : Fin 4) (h : ∀ a, a.1 ≠ i → p a = a) :
    ∀ a, (p a).1 = a.1 := by
  intro a
  by_cases ha : a.1 = i
  · rw [ha]
    by_contra hn
    have he : p a = a := p.injective (h (p a) hn)
    rw [he,ha] at hn
    exact hn rfl
  · rw [h a ha]

theorem single_wire_absorbed (d k : ℕ) (p : Wire k) (i : Fin 4) (h : ∀ a, a.1 ≠ i → p a = a) :
    act d k p * W d k = W d k ∧ W d k * act d k p = W d k := by
  obtain ⟨t,rfl⟩ := row_preserving (row_preserving_of_single i h)
  exact W_absorbs d k t

theorem first_packet_absorbed (d k : ℕ) :
    localClasp d k 1 * W d k = W d k ∧ W d k * localClasp d k 1 = W d k := by
  have h (p : group k 1) := single_wire_absorbed d k p 0 (fun a ha => p.property a (by
    have hne : a.1.val ≠ 0 := fun hh => ha (Fin.ext hh)
    omega))
  exact ⟨avg_mul_fixed _ _ fun p => (h p).1,mul_avg_fixed _ _ fun p => (h p).2⟩

theorem W_comm_packet (d k : ℕ) (σ : FourPerm) :
    W d k * packets d k σ = packets d k σ * W d k := by
  let e := σ.symm.arrowCongr (Equiv.refl (Equiv.Perm (Fin k)))
  simp only [W,Transfer.clasp,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]
  congr 1
  apply Fintype.sum_equiv e
  intro i
  change act d k (withinHom k i) * act d k (wires k σ) =
    act d k (wires k σ) * act d k (withinHom k (e i))
  rw [← map_mul,← map_mul]
  rfl

theorem W_comm_triple (d k : ℕ) :
    W d k * triple (packets d k swap12) (packets d k swap23) =
      triple (packets d k swap12) (packets d k swap23) * W d k := by
  have hr {a b : Op d k} (ha : W d k * a = a * W d k) (hb : W d k * b = b * W d k) :
      W d k * (a*b) = (a*b) * W d k := by rw [← mul_assoc,ha,mul_assoc,hb,mul_assoc]
  have hu := W_comm_packet d k swap12
  have hv := W_comm_packet d k swap23
  simp only [triple, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    hu,hv,hr hu hv,hr hv hu,hr (hr hu hv) hu]


end
end BlockPermanents.FourThickCompression
