import BlockPermanents.RoutingInsertion
import BlockPermanents.RoutingDefect

/-! # The stationary, moved and crossed spectator terms of Section 3E -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {n k : ℕ} {R : Type*} [Ring R] [Algebra ℚ R]

/-- The residual diagram after adjoining one complete packet between
the prescribed input and output. Its old coefficient can depend on the
number of split packets. -/
def exitOp (ρ : Wire (n+1) k →* R) (i j : Fin (n+1)) (c : ℕ → ℚ) :=
  ((k.factorial:ℚ)^n)⁻¹ • ∑ p : Wire n k, c (table p).splitInputs.card •
    compressed ρ (insertWire i j 1 p)

private theorem order_absorbed (ρ : Wire (n+1) k →* R) (i j : Fin (n+1))
    (z : Perm (Fin k)) (p : Wire n k) :
    compressed ρ (insertWire i j z p) = compressed ρ (insertWire i j 1 p) := by
  apply compressed_eq
  apply table_ext
  intro a b
  change profileSize (fun t => (insertWire i j z p (a,t)).1) b =
    profileSize (fun t => (insertWire i j 1 p (a,t)).1) b
  by_cases ha : a=i
  · subst a;simp
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq ha
    simp

/-- Every old permutation extends in k! independent ways, all with equal
compressed action. Thus a prescribed exit is the full normalized fine sum
restricted to permutations containing that whole edge. -/
theorem exit_expand (ρ : Wire (n+1) k →* R) (i j : Fin (n+1)) (hk : 0<k) (c : ℕ → ℚ) :
    exitOp ρ i j c = ∑ M : Routing (n+1) k,
      (weight M * (if (i,j) ∈ M.whole then c M.splitInputs.card else 0)) • routingOp ρ M := by
  classical
  let pred := fun p : Wire (n+1) k => (table p).entries i j=k
  let f := fun p : Wire (n+1) k => c (table p).splitInputs.card • compressed ρ p
  have h (p : Wire (n+1) k) :
      ((if (i,j) ∈ (table p).whole then c (table p).splitInputs.card else 0) • compressed ρ p)
        = (if pred p then f p else 0) := by
    simp [Routing.whole,pred,f,ite_smul]
  have sub : (∑ p : Wire (n+1) k, if pred p then f p else 0) =
      ∑ p : {q : Wire (n+1) k // pred q}, f p.val := by
    rw [← Fintype.sum_subtype_add_sum_subtype pred (fun p => if pred p then f p else 0)]
    have hneg (p : {q : Wire (n+1) k // ¬pred q}) : (if pred p.val then f p.val else 0) = 0 := if_neg p.property
    simp [Subtype.property,hneg]
  rw [← weighted_expand]
  simp_rw [h]
  rw [sub,← Equiv.sum_comp (edgeFibre i j),Fintype.sum_prod_type]
  have terms (u : Perm (Fin k)) (p : Wire n k) :
      f ((edgeFibre i j) (u,p)).val =
        c (table p).splitInputs.card • compressed ρ (insertWire i j 1 p) := by
    change c (table (insertWire i j u p)).splitInputs.card • compressed ρ (insertWire i j u p) = _
    rw [split_count_insert _ _ _ _ hk,order_absorbed]
  simp only [terms,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℚ,smul_smul,exitOp]
  apply congrArg (· • _)
  field_simp [Nat.factorial_ne_zero];ring

/-- Relative coefficients assembled from the actual normalized sum of
thin permutations. The scalar recurrence is the one in the manuscript. -/
def iterate (ρ : Wire n k →* R) :=
  ((k.factorial:ℚ)^n)⁻¹ • ∑ p : Wire n k,
    Routing.relativeA (table p).splitInputs.card (table p).whole.card • compressed ρ p

theorem iterate_expand (ρ : Wire n k →* R) (hk : 0<k) :
    iterate ρ = ∑ M : Routing n k, (weight M * ((n:ℚ)/M.splitInputs.card)) • routingOp ρ M := by
  unfold iterate
  rw [weighted_expand ρ (fun M => Routing.relativeA M.splitInputs.card M.whole.card)]
  simp_rw [Routing.relativeA_table _ hk]

def defect (ρ : Wire n k →* R) :=
    (((n*k).factorial : ℚ)/(k.factorial:ℚ)^n) • (internal ρ * Transfer.clasp ρ * internal ρ) -
      (n.factorial:ℚ) • (internal ρ * Transfer.clasp (ρ.comp (packetHom n k)) * internal ρ)

/-- Deleting any whole edge of the new table preserves the split count.
This realizes the defining recurrence of A on actual thin permutations.
The factor 1/n combines (n+1)²/n with the mean of the (n+1)² exits. -/
theorem iterate_step (ρ : Wire (n+1) k →* R) (hk : 0<k) (hn : 0<n) :
    iterate ρ = defect ρ +
      (n:ℚ)⁻¹ • ∑ ij : Fin (n+1) × Fin (n+1), exitOp ρ ij.1 ij.2 (fun b => n/b) := by
  classical
  rw [iterate_expand _ hk, defect,defect_expand _ hk]
  simp_rw [exit_expand _ _ _ hk]
  rw [Finset.sum_comm,Finset.smul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro M _
  let b := M.splitInputs.card
  let op := routingOp ρ M
  have hs : (∑ ij : Fin (n+1) × Fin (n+1), (weight M *
      (if ij ∈ M.whole then (n:ℚ)/b else 0)) • op) =
      ((M.whole.card:ℚ) * weight M * ((n:ℚ)/b)) • op := by
    simp only [mul_ite,mul_zero,ite_smul,zero_smul,← Finset.sum_filter]
    simp [← Nat.cast_smul_eq_nsmul ℚ,smul_smul,mul_assoc]
  change _ = _ + (n:ℚ)⁻¹ • (∑ ij, (weight M * (if ij ∈ M.whole then (n:ℚ)/b else 0)) • op)
  rw [hs,smul_smul,← add_smul]
  apply congrArg (· • op)
  have hcount : (b:ℚ) + M.whole.card = (n:ℚ)+1 := by exact_mod_cast M.splitInputs_add_whole hk
  by_cases hb : b=0
  · simp [b,show M.splitInputs.card=0 from hb] at *
  · have hb' : (b:ℚ)≠0 := Nat.cast_ne_zero.mpr hb
    have hn' : (n:ℚ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    change weight M * ((↑(n+1):ℚ)/b) = (if b=0 then 0 else weight M) + _
    rw [if_neg hb,Nat.cast_succ,← hcount]
    field_simp [hb',hn'];ring

/-- Signed readout of the stationary, complementary, and crossed placements.
Each summand is an actual inserted old thin-permutation operator. -/
def marked (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) :=
  defect ρ + ∑ ij : Fin (n+1) × Fin (n+1), (Routing.exitWeight a ij / n) •
    exitOp ρ ij.1 ij.2 (fun b => n/b)

theorem marked_expand (ρ : Wire (n+1) k →* R) (a : Fin (n+1)) (hk : 0<k) (hn : 0<n) :
    marked ρ a = ∑ M : Routing (n+1) k,
      (weight M * ((n+1:ℚ)/(2*M.splitInputs.card)) *
        ((if a ∈ M.splitInputs then 1 else 0)+(if a ∈ M.splitOutputs then 1 else 0))) • routingOp ρ M := by
  classical
  unfold marked defect
  rw [defect_expand _ hk]
  simp_rw [exit_expand _ _ _ hk, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro M _
  let b := M.splitInputs.card
  let op := routingOp ρ M
  have hn' : (n:ℚ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have item (ij : Fin (n+1) × Fin (n+1)) :
      (Routing.exitWeight a ij / n * (weight M * (if ij ∈ M.whole then (n:ℚ)/b else 0))) • op =
      if ij ∈ M.whole then (weight M * (Routing.exitWeight a ij / b)) • op else 0 := by
    split_ifs
    · apply congrArg (· • op)
      calc
        _ = (Routing.exitWeight a ij * weight M) * ((n:ℚ)*(n:ℚ)⁻¹) * (b:ℚ)⁻¹ := by ring
        _ = _ := by rw [mul_inv_cancel₀ hn',mul_one];ring
    · simp
  change _ + (∑ ij : Fin (n+1) × Fin (n+1), (Routing.exitWeight a ij / n * (weight M * (if ij ∈ M.whole then (n:ℚ)/b else 0))) • op) = _
  simp_rw [item]
  rw [← Finset.sum_filter,Finset.filter_univ_mem, ← Finset.sum_smul,← add_smul]
  apply congrArg (· • op)
  rw [← Finset.mul_sum,← Finset.sum_div]
  have he := M.transferred_eq hk a
  change (if b=0 then 0 else 1+(∑ e ∈ M.whole,Routing.exitWeight a e)/(b:ℚ)) = _ at he
  change (if b=0 then 0 else weight M)+weight M*((∑ e ∈ M.whole,Routing.exitWeight a e)/(b:ℚ)) = _
  by_cases hb : b=0
  · have hzero : M.splitInputs.card=0 := hb
    simp [hb,hzero]
  · rw [if_neg hb] at he ⊢
    rw [← mul_one_add,he]
    push_cast;ring

end
end BlockPermanents.RoutingFibres
