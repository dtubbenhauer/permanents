import BlockPermanents.RoutingFibres
import Mathlib.Tactic.FieldSimp

/-! # Operator expansion by the routing double cosets

The representation can be the actual action on words or a formal action of
the strand permutations. No independence of represented routings is required.
-/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {m k : ℕ}

def within : (Fin m → Perm (Fin k)) →* Wire m k where
  toFun := Equiv.prodCongrRight
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem preserves {b : Wire m k} (h : ∀ x, (b x).1 = x.1) :
    ∃ z : Fin m → Perm (Fin k), within z = b := by
  have hi (x : Slot m k) : (b.symm x).1 = x.1 := by
    have hb := h (b.symm x);simpa using hb.symm
  let z (i : Fin m) : Perm (Fin k) := {
    toFun := fun t => (b (i,t)).2
    invFun := fun t => (b.symm (i,t)).2
    left_inv := fun t => by
      have e : (i,(b (i,t)).2) = b (i,t) := Prod.ext (h (i,t)).symm rfl
      change (b.symm (i,(b (i,t)).2)).2 = t
      rw [e,b.symm_apply_apply]
    right_inv := fun t => by
      have e : (i,(b.symm (i,t)).2) = b.symm (i,t) := Prod.ext (hi (i,t)).symm rfl
      change (b (i,(b.symm (i,t)).2)).2 = t
      rw [e,b.apply_symm_apply] }
  refine ⟨z,Equiv.ext fun ⟨i,t⟩ => Prod.ext (h (i,t)).symm rfl⟩

/-- The routing matrix completely determines the double coset. -/
theorem double_coset {p q : Wire m k} (h : table p = table q) :
    ∃ a b : Fin m → Perm (Fin k), q = within b * p * within a := by
  classical
  let dest (w : Wire m k) (i : Fin m) (t : Fin k) := (w (i,t)).1
  let f (i j : Fin m) : Fibre (dest q i) j ≃ Fibre (dest p i) j :=
    Fintype.equivOfCardEq (congrArg (fun M => Routing.entries M i j) h.symm)
  let a i := Equiv.ofFiberEquiv (f i)
  let p' := p * within a
  have hm (x : Slot m k) : (p' x).1 = (q x).1 := Equiv.ofFiberEquiv_map (f x.1) x.2
  have hb (x : Slot m k) : ((q * p'⁻¹) x).1 = x.1 := by
    change (q (p'.symm x)).1 = _
    rw [← hm,p'.apply_symm_apply]
  obtain ⟨b,hb⟩ := preserves hb
  refine ⟨a,b,?_⟩
  rw [hb,mul_assoc]
  change q = (q*p'⁻¹)*p'; simp

theorem table_within (p : Wire m k) (a b : Fin m → Perm (Fin k)) :
    table (within b * p * within a) = table p := by
  apply table_ext
  intro i j
  change Fintype.card {t : Fin k // (p (i,a i t)).1 = j} = Fintype.card {t : Fin k // (p (i,t)).1 = j}
  apply Fintype.card_congr
  exact (a i).subtypeEquiv (fun _ => Iff.rfl)

variable {R : Type*} [Ring R] [Algebra ℚ R]

def internal (ρ : Wire m k →* R) := Transfer.clasp (ρ.comp within)

def compressed (ρ : Wire m k →* R) (p : Wire m k) := internal ρ * ρ p * internal ρ

/-- The internal clasp absorbs the two independent changes of strand order. -/
theorem compressed_eq {p q : Wire m k} (ρ : Wire m k →* R) (h : table p=table q) :
    compressed ρ p = compressed ρ q := by
  obtain ⟨a,b,rfl⟩ := double_coset h
  have hL : internal ρ * ρ (within b) = internal ρ := Transfer.absorb_right (ρ.comp within) b
  have hR : ρ (within a) * internal ρ = internal ρ := Transfer.absorb_left (ρ.comp within) a
  simp only [compressed,map_mul,← mul_assoc,hL]
  rw [mul_assoc (_ * _) (ρ (within a)),hR]

def routingOp (ρ : Wire m k →* R) (M : Routing m k) : R :=
  compressed ρ (realizable M).choose

theorem routingOp_table (ρ : Wire m k →* R) (p : Wire m k) :
    routingOp ρ (table p) = compressed ρ p :=
  compressed_eq ρ (realizable (table p)).choose_spec

def weight (M : Routing m k) : ℚ := (k.factorial:ℚ)^m /
  (∏ i, ∏ j, ((M.entries i j).factorial : ℚ))

/-- A single thin permutation contributes the inverse of all input
packet factorials in the fine expansion. -/
theorem normalized_multiplicity (M : Routing m k) :
    (Fintype.card (Fibre table M) : ℚ) / (k.factorial:ℚ)^m = weight M := by
  have hc : (Fintype.card (Fibre table M) : ℚ) *
    (∏ i, ∏ j, ((M.entries i j).factorial : ℚ)) = (k.factorial : ℚ)^(2*m) := by
    exact_mod_cast fibre_multiplicity M
  have hi : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj : (∏ i, ∏ j, ((M.entries i j).factorial : ℚ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Finset.prod_ne_zero_iff.mpr fun _ _ =>
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold weight
  rw [div_eq_div_iff (pow_ne_zero _ hi) hj,← pow_add,← two_mul]
  exact hc

theorem weighted_expand (ρ : Wire m k →* R) (c : Routing m k → ℚ) :
    ((k.factorial:ℚ)^m)⁻¹ •
      (∑ p : Wire m k, c (table p) • compressed ρ p) =
    ∑ M : Routing m k, (weight M * c M) • routingOp ρ M := by
  classical
  rw [← Equiv.sum_comp (sigmaFiberEquiv table) (fun p => c (table p) • compressed ρ p),
    Fintype.sum_sigma,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro M _
  have term (p : Fibre table M) :
      c (table ((sigmaFiberEquiv table) ⟨M,p⟩)) • compressed ρ ((sigmaFiberEquiv table) ⟨M,p⟩) =
      c M • routingOp ρ M := by change c (table p.val) • compressed ρ p.val = _
                                rw [← routingOp_table,p.property]
  simp only [term,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ,smul_smul]
  rw [← normalized_multiplicity]
  congr 1;ring

/-- The actual simultaneous thin clasp, normalized in permanent units and
sandwiched between the row and column packet clasps. -/
theorem fine_expand (ρ : Wire m k →* R) :
    (((m*k).factorial : ℚ)/(k.factorial:ℚ)^m) •
      (internal ρ * Transfer.clasp ρ * internal ρ) =
      ∑ M : Routing m k, weight M • routingOp ρ M := by
  have e := weighted_expand ρ (fun _ => 1)
  simp only [one_smul,mul_one] at e
  rw [← e]
  have card : Fintype.card (Wire m k) = (m*k).factorial := by
    simp [Wire,Slot,Fintype.card_perm]
  simp only [Transfer.clasp,card,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,
    compressed,smul_smul]
  congr 1
  have h : ((m*k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp;ring

end
end BlockPermanents.RoutingFibres
