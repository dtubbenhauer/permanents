import BlockPermanents.Transfer
import BlockPermanents.Bridges
import BlockPermanents.SchurNormalization

/-! The unbent Schur relation on labeled thin wires. -/
namespace BlockPermanents.WireSchur
open Bend Closures SchurNormalization
open scoped BigOperators
noncomputable section

abbrev Slots (p q : ℕ) := Fin p ⊕ Fin q

def leftLe {p q : ℕ} (r : CutIndex p q) : r.val ≤ p :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_left _ _)
def rightLe {p q : ℕ} (r : CutIndex p q) : r.val ≤ q :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_right _ _)

/-- Read a through prefix followed by an exchange suffix in their original cable. -/
def splitSlot {n r : ℕ} (h : r ≤ n) : Fin (n-r) ⊕ Fin r ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel h))

private def crossSuffix {A B C : Type*} : Equiv.Perm ((A ⊕ C) ⊕ (B ⊕ C)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inr c)
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr c) => .inl (.inr c)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inr c)
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr c) => .inl (.inr c)
  left_inv := by rintro ((a|c)|(b|c)) <;> rfl
  right_inv := by rintro ((a|c)|(b|c)) <;> rfl

/-- Fix the two through prefixes and swap the two ordered suffixes of length r. -/
def exchangePerm (p q : ℕ) (r : CutIndex p q) : Equiv.Perm (Slots p q) :=
  ((splitSlot (leftLe r)).sumCongr (splitSlot (rightLe r))).permCongr crossSuffix

/-- Uniform independent permutation averages of both sides of the cut. -/
def blockClasp {p q d : ℕ} (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) : ℂ :=
  (p.factorial : ℂ)⁻¹ * ∑ a : Equiv.Perm (Fin p),
    (q.factorial : ℂ)⁻¹ * ∑ b : Equiv.Perm (Fin q), z (w ∘ a.sumCongr b)

theorem clasp_direct {d n : ℕ} (f : Word d n → ℂ) (w : Word d n) :
    (symClasp d n).mulVec f w =
      (n.factorial : ℂ)⁻¹ * ∑ a : Equiv.Perm (Fin n), f (w ∘ a) := by
  rw [Bridges.symClasp_action]
  simp only [clasp,sumSlots,Fintype.card_fin]
  exact congrArg _ (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n))) (fun a : Equiv.Perm (Fin n) => f (w ∘ a)))

theorem symClasp_star {d n : ℕ} (u v : Word d n) :
    star (symClasp d n u v) = symClasp d n v u := by
  classical
  simp only [symClasp,star_mul',star_inv₀,star_natCast,star_sum,apply_ite,star_one,star_zero]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n)))
  intro a
  congr 1
  change (u = v ∘ a) = (v = u ∘ a.symm)
  apply propext
  constructor <;> rintro rfl <;> funext j <;> simp

abbrev splitWords (d p q : ℕ) :=
  Equiv.sumArrowEquivProdArrow (Fin p) (Fin q) (Fin d)

private def blockMatrix {d p q : ℕ} (x y : Slots p q → Fin d) : ℂ :=
  symClasp d p (x ∘ Sum.inl) (y ∘ Sum.inl) * symClasp d q (x ∘ Sum.inr) (y ∘ Sum.inr)

private theorem block_action {d p q : ℕ} (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    (∑ u, blockMatrix w u * z u) = blockClasp z w := by
  rw [← (splitWords d p q).symm.sum_comp (fun u => blockMatrix w u * z u), Fintype.sum_prod_type]
  change (∑ a : Word d p, ∑ b : Word d q, (symClasp d p (w ∘ Sum.inl) a *
    symClasp d q (w ∘ Sum.inr) b) * z (Sum.elim a b)) = _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (symClasp d p).mulVec (fun a => (symClasp d q).mulVec (fun b => z (Sum.elim a b))
    (w ∘ Sum.inr)) (w ∘ Sum.inl) = _
  simp only [clasp_direct, blockClasp]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext i
  cases i <;> rfl

private abbrev pieces (d p q : ℕ) (r : CutIndex p q) :=
  (Word d (p-r) × Word d (q-r)) × (Word d r × Word d r)

private def mergeWord {d n r : ℕ} (h : r ≤ n) : Word d (n-r) × Word d r ≃ Word d n :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans ((splitSlot h).arrowCongr (Equiv.refl _))

private theorem mergeWord_eq {d n r : ℕ} (h : r ≤ n) (a : Word d (n-r)) (b : Word d r) :
    mergeWord h (a,b) = fun t => Fin.append a b (Fin.cast (Nat.sub_add_cancel h).symm t) := by
  funext t
  obtain ⟨i,rfl⟩ := (splitSlot h).surjective t
  cases i <;> simp [mergeWord,splitSlot,finCongr, -Fin.natAdd_eq_addNat]

private def groupPieces {d p q : ℕ} (r : CutIndex p q) :
    pieces d p q r ≃ (Slots p q → Fin d) :=
  (Equiv.prodProdProdComm _ _ _ _).trans (((mergeWord (leftLe r)).prodCongr
    (mergeWord (rightLe r))).trans (splitWords d p q).symm)

private theorem group_cross {d p q : ℕ} (r : CutIndex p q) (u : pieces d p q r) :
    groupPieces r (u.1,u.2.swap) = groupPieces r u ∘ exchangePerm p q r := by
  funext i
  obtain ⟨i,rfl⟩ := ((splitSlot (leftLe r)).sumCongr (splitSlot (rightLe r))).surjective i
  rcases i with ((a|c)|(b|c)) <;>
    simp [groupPieces,exchangePerm,Equiv.permCongr_def,crossSuffix,mergeWord,Function.comp_def]

private theorem exchange_kernel {d p q : ℕ} (r : CutIndex p q) (x y : Slots p q → Fin d) :
    exchange (wordFork d p r (leftLe r)) (wordFork d q r (rightLe r))
      (splitWords d p q x) (splitWords d p q y) =
    ∑ u, blockMatrix x u * blockMatrix (u ∘ exchangePerm p q r) y := by
  rw [← (groupPieces r).sum_comp (fun u => blockMatrix x u * blockMatrix (u ∘ exchangePerm p q r) y)]
  simp only [exchange,Matrix.mul_apply,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [← group_cross]
  change star (wordFork d p r _ (u.1.1,u.2.1) (x ∘ Sum.inl) *
    wordFork d q r _ (u.1.2,u.2.2) (x ∘ Sum.inr)) *
    (wordFork d p r _ (u.1.1,u.2.2) (y ∘ Sum.inl) *
    wordFork d q r _ (u.1.2,u.2.1) (y ∘ Sum.inr)) =
    (symClasp d p (x ∘ Sum.inl) (mergeWord (leftLe r) (u.1.1,u.2.1)) *
    symClasp d q (x ∘ Sum.inr) (mergeWord (rightLe r) (u.1.2,u.2.2))) *
    (symClasp d p (mergeWord (leftLe r) (u.1.1,u.2.2)) (y ∘ Sum.inl) *
    symClasp d q (mergeWord (rightLe r) (u.1.2,u.2.1)) (y ∘ Sum.inr))
  simp only [wordFork,mergeWord_eq,star_mul',symClasp_star]

private abbrev joinSlots (d p q : ℕ) :
    (Slots p q → Fin d) ≃ Word d (p+q) := finSumFinEquiv.arrowCongr (Equiv.refl _)

private theorem joinSlots_eq {d p q : ℕ} (w : Slots p q → Fin d) :
    joinSlots d p q w = Fin.append (w ∘ Sum.inl) (w ∘ Sum.inr) := by
  funext i
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [joinSlots, -Fin.natAdd_eq_addNat]

private theorem total_action {d p q : ℕ} (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    (∑ y, totalClasp d p q (splitWords d p q w) (splitWords d p q y) * z y) = clasp z w := by
  let e := joinSlots d p q
  change (∑ y, symClasp d (p+q) (Fin.append (w ∘ Sum.inl) (w ∘ Sum.inr))
    (Fin.append (y ∘ Sum.inl) (y ∘ Sum.inr)) * z y) = _
  simp_rw [← joinSlots_eq]
  have he := e.sum_comp (fun y => symClasp d (p+q) (e w) y * z (e.symm y))
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  change (symClasp d (p+q)).mulVec (fun y => z (y ∘ finSumFinEquiv)) (e w) = _
  rw [Bridges.symClasp_action, Bridges.clasp_transport]
  change clasp z (e.symm (e w)) = _
  rw [Equiv.symm_apply_apply]

theorem exchange_action {d p q : ℕ} (r : CutIndex p q)
    (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    (∑ y, exchange (wordFork d p r (leftLe r)) (wordFork d q r (rightLe r))
      (splitWords d p q w) (splitWords d p q y) * z y) =
    blockClasp (fun u => blockClasp z (u ∘ exchangePerm p q r)) w := by
  simp_rw [exchange_kernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, block_action]

/-- An operator identity on arbitrary tensor coordinates. The coefficient on each wiring
is the number of pairs of chosen suffixes; the two independent permutation averages
on either side allow any slots in the corresponding cables to be exchanged. -/
theorem wire_schur {d p q : ℕ} (h : HomogeneousSchur d p q)
    (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    ((p+q).choose p : ℂ) * clasp z w =
      ∑ r : CutIndex p q, (weight p q r : ℂ) *
        blockClasp (fun u => blockClasp z (u ∘ exchangePerm p q r)) w := by
  have hs := homogeneousSchur_implies_unbent d p q h
  rw [← total_action z w, Finset.mul_sum]
  have hs' (y : Slots p q → Fin d) := hs (splitWords d p q w) (splitWords d p q y)
  simp only [← mul_assoc, hs', Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← exchange_action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_assoc]


@[simp] theorem exchange_left_prefix {p q} (r : CutIndex p q) (i : Fin (p-r)) :
    exchangePerm p q r (.inl (splitSlot (leftLe r) (.inl i))) =
      .inl (splitSlot (leftLe r) (.inl i)) := by
  simp [exchangePerm,Equiv.permCongr_def,crossSuffix]

@[simp] theorem exchange_right_prefix {p q} (r : CutIndex p q) (i : Fin (q-r)) :
    exchangePerm p q r (.inr (splitSlot (rightLe r) (.inl i))) =
      .inr (splitSlot (rightLe r) (.inl i)) := by
  simp [exchangePerm,Equiv.permCongr_def,crossSuffix]

@[simp] theorem exchange_left_suffix {p q} (r : CutIndex p q) (i : Fin r) :
    exchangePerm p q r (.inl (splitSlot (leftLe r) (.inr i))) =
      .inr (splitSlot (rightLe r) (.inr i)) := by
  simp [exchangePerm,Equiv.permCongr_def,crossSuffix]

@[simp] theorem exchange_right_suffix {p q} (r : CutIndex p q) (i : Fin r) :
    exchangePerm p q r (.inr (splitSlot (rightLe r) (.inr i))) =
      .inl (splitSlot (leftLe r) (.inr i)) := by
  simp [exchangePerm,Equiv.permCongr_def,crossSuffix]

abbrev action (d p q : ℕ) := Transfer.tensorAction (Slots p q) (Fin d)

/-- Two independent symmetric clasps as an endomorphism of the combined tensor power. -/
def blockOp (d p q : ℕ) :=
  Transfer.clasp ((action d p q).comp (Equiv.Perm.sumCongrHom (Fin p) (Fin q)))

theorem blockOp_apply {d p q : ℕ} (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    blockOp d p q z w = blockClasp z w := by
  simp [blockOp,action,Transfer.clasp,Transfer.tensorAction,LinearMap.smul_apply,
    LinearMap.sum_apply,Finset.sum_apply,Rat.smul_def,blockClasp,Fintype.sum_prod_type,
    Fintype.card_perm,Finset.mul_sum,mul_assoc,mul_left_comm]

theorem totalOp_apply {d p q : ℕ} (z : (Slots p q → Fin d) → ℂ) (w : Slots p q → Fin d) :
    Transfer.clasp (action d p q) z w = clasp z w := by
  simp only [action,Transfer.clasp,Transfer.tensorAction,LinearMap.smul_apply,
    LinearMap.sum_apply,Finset.sum_apply,Rat.smul_def,clasp,sumSlots,Fintype.card_perm,
    Rat.cast_inv,Rat.cast_natCast,Pi.smul_apply,smul_eq_mul,MonoidHom.coe_mk,OneHom.coe_mk,
    LinearMap.coe_mk,AddHom.coe_mk]
  congr 1
  exact (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Slots p q)))
    (fun a : Equiv.Perm (Slots p q) => z (w ∘ a))).symm

/-- The full identity in the same endomorphism algebra used by the packet transfer. -/
theorem wire_schur_operator {d p q : ℕ} (h : HomogeneousSchur d p q) :
    ((p+q).choose p : ℚ) • Transfer.clasp (action d p q) =
      ∑ r : CutIndex p q, (weight p q r : ℚ) •
        (blockOp d p q * action d p q (exchangePerm p q r) * blockOp d p q) := by
  apply LinearMap.ext
  intro z
  funext w
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,Finset.sum_apply,
    Pi.smul_apply,Rat.smul_def,Rat.cast_natCast,smul_eq_mul,Module.End.mul_apply,
    totalOp_apply,blockOp_apply]
  have hb : (blockOp d p q) z = blockClasp z := funext (blockOp_apply z)
  rw [hb]
  exact wire_schur h z w

end
end BlockPermanents.WireSchur
