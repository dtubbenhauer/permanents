import BlockPermanents.FourExchangeBasis
import BlockPermanents.FourNativeCap
import BlockPermanents.FourWireAlgebra

/-! # The actual moved pair acts on exactly the two ordinary survivors -/
namespace BlockPermanents.FourNativeSurvivor
open Equiv FourTarget LocalGroup LocalAction FourWireAlgebra FourExchangeKernel Bend
open scoped Matrix BigOperators
noncomputable section

@[local simp] private theorem add_disjoint {k : ℕ} {M : Type*} (a b : Fin k → M) (t : Fin k) :
    Fin.addCases (motive:=fun _ => M) a b (t.addNat k)=b t := by
  rw [show t.addNat k = Fin.natAdd k t by apply Fin.ext;exact Nat.add_comm _ _,Fin.addCases_right]

@[local simp] private theorem append_disjoint {k : ℕ} {M : Type*} (a b : Fin k → M) (t : Fin k) :
    Fin.append a b (t.addNat k)=b t := add_disjoint a b t

private def pairSlots (k : ℕ) : (Fin (k+k) ⊕ (Fin k ⊕ Fin k)) ≃ Slot k where
  toFun := Sum.elim (Fin.addCases (fun t => (1,t)) (fun t => (2,t))) (Sum.elim (fun t => (0,t)) (fun t => (3,t)))
  invFun w := ![Sum.inr (.inl w.2), Sum.inl (Fin.castAdd k w.2), Sum.inl (Fin.natAdd k w.2), Sum.inr (.inr w.2)] w.1
  left_inv := by
    rintro (i|h)
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;> simp
    · cases h <;> rfl
  right_inv := by rintro ⟨i,t⟩;fin_cases i <;> simp

private theorem moved_extend (d k : ℕ) :
    movedPair (packets d k) (localClasp d k 2) =
      extend (pairSlots k) (Transfer.clasp (Transfer.tensorAction (Fin (k+k)) (Fin d))) := by
  let s : TransferBlocks.FourPerm := Equiv.swap 0 2
  let Q := fun i : Slot k => i.1=1 ∨ i.1=2
  have c := conjugate (D:=Fin d) (wires k s) (fun i : Slot k => i.1.val<2) Q (by
    rintro ⟨i,t⟩; change i.val<2 ↔ s i=1 ∨ s i=2; fin_cases i <;> decide)
  have inv : (wires k s)⁻¹=wires k s := by rw [←map_inv]; rfl
  rw [inv] at c
  rw [movedPair,FourThickSlots.local_is_projector]
  apply c.trans
  symm;apply projector_extend
  · intro i;refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;> simp [Q,pairSlots]
  · intro z;rcases z with t|t <;> simp [Q,pairSlots]

private theorem join_eq {I Z W D : Type*} (e : I⊕Z ≃ W) (v : I→D) (w y : W→D) :
    join e v w = y ↔ v=(fun i => y (e (.inl i))) ∧ ∀ t,w (e (.inr t))=y (e (.inr t)) := by
  constructor
  · intro h
    constructor
    · funext i; simpa [join] using congrFun h (e (.inl i))
    · intro j;simpa [join] using congrFun h (e (.inr j))
  · rintro ⟨rfl,h⟩;funext a;obtain ⟨i,rfl⟩ := e.surjective a;cases i <;> simp_all [join]

private theorem active {d k : ℕ} (x : Index d k) :
    (fun i => (layout d k).symm x (pairSlots k (.inl i))) = Fin.append (x.1 1) (x.1 2) := by
  funext i;refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;> simp [pairSlots,layout]

/-- In the original packet order, the survivor projector is the ordinary
fine 2k-clasp applied to packets 2 and 3, with packets 1 and 4 left idle. -/
theorem matrix_moved (d k : ℕ) :
    matrix d k (movedPair (packets d k) (localClasp d k 2)) =
      ThreeTransfer.upright (FourNativeCap.survivor (totalClasp d k k)) := by
  rw [moved_extend]
  ext x y
  rw [matrix_entry]
  let w := (layout d k).symm x
  let z := (layout d k).symm y
  let f := fun v => if join (pairSlots k) v w = z then (1:ℂ) else 0
  change Transfer.clasp (Transfer.tensorAction (Fin (k+k)) (Fin d)) f _ = _
  have act (v : Word d (k+k)) (g : Word d (k+k)→ℂ) :
      Transfer.clasp (Transfer.tensorAction (Fin (k+k)) (Fin d)) g v = (symClasp d (k+k)).mulVec g v := by
    rw [WireSchur.clasp_direct]
    simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,Pi.smul_apply,Finset.sum_apply,
      Rat.smul_def,Rat.cast_inv,Rat.cast_natCast,Fintype.card_perm,Fintype.card_fin];rfl
  rw [act,active]
  have frozen : (∀ t : Fin k ⊕ Fin k,w (pairSlots k (.inr t))=z (pairSlots k (.inr t))) ↔ x.1 0=y.1 0 ∧ x.2=y.2 := by
    constructor
    · intro h;exact ⟨funext (fun i => h (.inl i)),funext (fun i => h (.inr i))⟩
    · rintro ⟨a,b⟩ (i|i);exact congrFun a i;exact congrFun b i
  have hf (v) : f v = if v=Fin.append (y.1 1) (y.1 2) ∧ x.1 0=y.1 0 ∧ x.2=y.2 then 1 else 0 := by
    dsimp only [f];simp only [join_eq,frozen];dsimp only [z];rw [active]
  simp only [Matrix.mulVec,dotProduct,hf,ThreeTransfer.upright,FourNativeCap.survivor,totalClasp]
  by_cases h0 : x.1 0=y.1 0 <;> by_cases h3 : x.2=y.2 <;> simp [h0,h3]

end
end BlockPermanents.FourNativeSurvivor
