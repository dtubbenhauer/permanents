import BlockPermanents.FourThickJoint
import BlockPermanents.FourThickExchange
import BlockPermanents.FourSymbolic

/-! # Three compressed Schur openings for packets of arbitrary positive thickness -/
namespace BlockPermanents.FourThickOpenings
open FourTarget FourThickSlots FourThickCompression FourThickJoint FourWireAlgebra
open FourLocalCompression (absorb_conjugate)
open LocalGroup TransferBlocks SchurNormalization Bend
open scoped BigOperators
noncomputable section
local instance (k n : ℕ) : Fintype (group k n) := Fintype.ofFinite _

def properIndices (p k : ℕ) : Finset (CutIndex p k) :=
  Finset.univ.filter (fun r => 0 < r.val ∧ r.val < k)

/-- The proper cuts use the native local placement. Each term is the actual
wire permutation sandwiched between the active ordinary clasps. -/
def proper (d k n : ℕ) (hn : n ≤ 3) : Op d k :=
  ∑ r ∈ properIndices (n*k) k, (weight (n*k) k r : ℚ) • (localClasp d k n *
    act d k (FourThickSlots.exchange k n hn r) * localClasp d k n)

def start (p k : ℕ) : CutIndex p k := ⟨0,by omega⟩
def finish (p k : ℕ) (h : k ≤ p) : CutIndex p k := ⟨k,by omega⟩

theorem split_indices {R : Type*} [AddCommMonoid R] {p k : ℕ} (hk : 0<k) (hp : k≤p)
    (f : CutIndex p k → R) : ∑ r,f r = f (start p k) +
      (∑ r ∈ properIndices p k,f r) + f (finish p k hp) := by
  let a := start p k
  let b := finish p k hp
  have hne : b ≠ a := fun hh => hk.ne' (congrArg Fin.val hh)
  have hb : b ∈ (Finset.univ.erase a) := Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩
  have eq : (Finset.univ.erase a).erase b = properIndices p k := by
    ext r
    simp only [properIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
    change (r ≠ finish p k hp ∧ r ≠ start p k) ↔ _
    have hr := WireSchur.rightLe r
    constructor
    · rintro ⟨g,h⟩
      have h0 : r.val ≠ 0 := fun e => h (Fin.ext e)
      have hk' : r.val ≠ k := fun e => g (Fin.ext e)
      omega
    · rintro ⟨h,g⟩
      exact ⟨fun e => g.ne (congrArg Fin.val e),fun e => h.ne' (congrArg Fin.val e)⟩
  rw [← Finset.sum_erase_add _ f (Finset.mem_univ a),← Finset.sum_erase_add _ f hb,eq]
  dsimp only [a,b]; abel

theorem last_resident {d k n : ℕ} (hn : n≤3) (h0 : 0<n) :
    let a : Fin 4 := ⟨n-1,by omega⟩
    let P := localClasp d k n
    P * packets d k (Equiv.swap a 3) * P = P * packets d k swap14 * P := by
  dsimp only
  let a : Fin 4 := ⟨n-1,by omega⟩
  let c := Equiv.swap 0 a
  have hc : wires k c ∈ group k n := by
    rintro ⟨i,b⟩ hi
    change n ≤ i.val at hi; change (c i,b)=(i,b)
    have i0 : i ≠ 0 := fun h => by rw [h] at hi; change n≤0 at hi; omega
    have ia : i ≠ a := fun h => by rw [h] at hi; change n≤n-1 at hi; omega
    rw [show c i=i from Equiv.swap_apply_of_ne_of_ne i0 ia]
  have c0 : c 0=a := Equiv.swap_apply_left _ _
  have c3 : c 3=3 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => by
    have he := congrArg Fin.val h; change 3=n-1 at he; omega)
  have perm : Equiv.swap a 3 = c * swap14 * c := by
    have eq : ∀ a : Fin 4, a ≠ 3 → Equiv.swap a 3 = Equiv.swap 0 a * swap14 * Equiv.swap 0 a := by decide
    exact eq a (fun e => by have := congrArg Fin.val e; change n-1=3 at this; omega)
  have hL : act d k (wires k c) * localClasp d k n = localClasp d k n :=
    Transfer.absorb_left ((act d k).comp (group k n).subtype) ⟨_,hc⟩
  have hR : localClasp d k n * act d k (wires k c) = localClasp d k n :=
    Transfer.absorb_right ((act d k).comp (group k n).subtype) ⟨_,hc⟩
  rw [show Equiv.swap (⟨n-1,by omega⟩:Fin 4) 3 = _ from perm,map_mul,map_mul]
  exact absorb_conjugate _ _ _ _ hR hL rfl

/-- Separate the zero/full cuts and retain every proper partial exchange.
The two endpoint permutations are proved from the flattened slot layout. -/
theorem opened_local {d k n : ℕ} (hk : 0<k) (hn : n≤3) (h0 : 0<n)
    (hs : HomogeneousSchur d (n*k) k) (hp : k ≤ n*k)
    (hz : FourThickSlots.exchange k n hn (start (n*k) k) = 1)
    (hf : FourThickSlots.exchange k n hn (finish (n*k) k hp) =
      wires k (Equiv.swap (⟨n-1,by omega⟩ : Fin 4) 3)) :
    let C := sand (W d k)
    let P := localClasp d k n
    C (((n*k+k).choose (n*k) : ℚ) • joint d k n) =
      C (P + proper d k n hn + ((n*k).choose k : ℚ) • (P * packets d k swap14 * P)) := by
  dsimp only
  let term (r : CutIndex (n*k) k) := (weight (n*k) k r : ℚ) •
    (localClasp d k n * act d k (FourThickSlots.exchange k n hn r) * localClasp d k n)
  have e := congrArg (sand (W d k)) (schur_on_slots d k n hn hs)
  rw [map_sum] at e
  simp only [map_smul,compressed_block d k n hn] at e
  have he : sand (W d k) (((n*k+k).choose (n*k) : ℚ) • joint d k n) =
      sand (W d k) (∑ r,term r) := by simpa only [term,map_sum,map_smul] using e
  have a : term (start (n*k) k) = localClasp d k n := by
    simp only [term,hz,map_one,mul_one,show weight (n*k) k (start (n*k) k)=1 by simp [weight,start],
      Nat.cast_one,one_smul]
    exact Transfer.clasp_sq _
  have b : term (finish (n*k) k hp) = ((n*k).choose k : ℚ) •
      (localClasp d k n * packets d k swap14 * localClasp d k n) := by
    simp only [term,hf,show weight (n*k) k (finish (n*k) k hp)=(n*k).choose k by simp [weight,finish]]
    exact congrArg (((n*k).choose k : ℚ) • ·) (last_resident hn h0)
  rw [he,split_indices hk hp term,a,b]
  rfl

end
end BlockPermanents.FourThickOpenings
