import BlockPermanents.FourExchangeBasis

/-! Spectator-sliced exchange on the original four-packet slot space. -/
namespace BlockPermanents.FourExchangeKernel
open FourTarget FourRoutes Bend Equiv WireSchur LocalAction
open scoped Matrix BigOperators
noncomputable section

def active {d k : ℕ} (n : ℕ) (hn : n≤3) (F : Triple d k) : Word d (n*k) :=
  fun i => F (i.divNat.castLE hn) i.modNat

def idle {d k : ℕ} (n : ℕ) (F : Triple d k) : Word d ((3-n)*k) :=
  fun i => F ⟨n+i.divNat.val,by have := i.divNat.isLt;omega⟩ i.modNat

def live {d k : ℕ} (n : ℕ) (hn : n≤3) (x : Index d k) : Slots (n*k) k → Fin d :=
  Sum.elim (active n hn x.1) x.2

private theorem layout_ord {d k : ℕ} (x : Index d k) (i : Fin 3) (j : Fin k) :
    (layout d k).symm x (i.castSucc,j)=x.1 i j := by fin_cases i <;> rfl

private theorem read_live {d k n : ℕ} (hn : n≤3) (x : Index d k) (i : Slots (n*k) k) :
    (layout d k).symm x (FourThickSlots.placement k n hn (.inl i)) = live n hn x i := by
  cases i with
  | inl i => exact layout_ord x (i.divNat.castLE hn) i.modNat
  | inr i => rfl

private theorem read_idle {d k n : ℕ} (hn : n≤3) (x : Index d k) (i : Fin ((3-n)*k)) :
    (layout d k).symm x (FourThickSlots.placement k n hn (.inr i)) = idle n x.1 i :=
  layout_ord x ⟨n+i.divNat.val,by have := i.divNat.isLt;omega⟩ i.modNat

private theorem join_eq {d k n : ℕ} (hn : n≤3) (x y : Index d k) (v : Slots (n*k) k → Fin d) :
    join (FourThickSlots.placement k n hn) v ((layout d k).symm x) = (layout d k).symm y ↔
      v = live n hn y ∧ idle n x.1=idle n y.1 := by
  let e := FourThickSlots.placement k n hn
  constructor
  · intro h
    constructor
    · funext i
      have hh := congrFun h (e (.inl i))
      simpa only [e,join,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,read_live] using hh
    · funext i
      have hh := congrFun h (e (.inr i))
      simpa only [e,join,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr,read_idle] using hh
  · rintro ⟨rfl,hi⟩
    funext i
    obtain ⟨i,rfl⟩ := e.surjective i
    cases i with
    | inl j => simp [e,join,read_live]
    | inr j => simp [e,join,read_idle,hi]

def xmatrix (d p k : ℕ) (r : CutIndex p k) :=
  exchange (wordFork d p r (WireSchur.leftLe r)) (wordFork d k r (WireSchur.rightLe r))

private theorem local_formula {d p k : ℕ} (r : CutIndex p k)
    (z : (Slots p k → Fin d) → ℂ) (w : Slots p k → Fin d) :
    (blockOp d p k * action d p k (exchangePerm p k r) * blockOp d p k) z w =
      ∑ i, xmatrix d p k r (WireSchur.splitWords d p k w) (WireSchur.splitWords d p k i) * z i := by
  change blockOp d p k (fun u => blockOp d p k z (u ∘ exchangePerm p k r)) w = _
  simp only [blockOp_apply]
  exact (exchange_action r z w).symm

/-- A native local exchange, including its two endpoint clasps, has a
Kronecker delta on the spectators and the usual exchange matrix on the
joined active words. -/
theorem exchange_entry {d k n : ℕ} (hn : n≤3) (r : CutIndex (n*k) k) (x y : Index d k) :
    matrix d k (FourThickSlots.block d k n * act d k (FourThickSlots.exchange k n hn r) *
        FourThickSlots.block d k n) x y =
      if idle n x.1=idle n y.1 then
        xmatrix d (n*k) k r (active n hn x.1,x.2) (active n hn y.1,y.2) else 0 := by
  let e := FourThickSlots.placement k n hn
  have ee := extend_perm (D:=Fin d) e (exchangePerm (n*k) k r)
  change extend e (action d (n*k) k (exchangePerm (n*k) k r)) =
    act d k (FourThickSlots.exchange k n hn r) at ee
  rw [←FourThickSlots.block_ext d k n hn,←ee,← map_mul,←map_mul,matrix_entry]
  change (blockOp d (n*k) k * action d (n*k) k (exchangePerm (n*k) k r) * blockOp d (n*k) k)
    (fun v => if join e v ((layout d k).symm x) = (layout d k).symm y then 1 else 0)
    (fun i => (layout d k).symm x (e (.inl i))) = _
  rw [local_formula]
  simp only [e,read_live,join_eq]
  by_cases hi : idle n x.1=idle n y.1 <;> simp [hi,mul_ite,live]
  rfl

/-- The lower half of one native exchange, with its ordinary spectators
recorded and the remaining thin labels on the two through words. -/
def half {d k : ℕ} (n : ℕ) (hn : n≤3) (r : CutIndex (n*k) k) (s : Word d ((3-n)*k)) :
    Matrix (Word d (n*k-r) × Word d (k-r)) (Index d k) ℂ :=
  fun a x => if idle n x.1=s then wordCap d (n*k) k r a (active n hn x.1,x.2) else 0

theorem bent_exchange {d k n : ℕ} (hn : n≤3) (r : CutIndex (n*k) k) :
    partialTranspose (matrix d k (FourThickSlots.block d k n * act d k (FourThickSlots.exchange k n hn r) *
      FourThickSlots.block d k n)) =
      ∑ s, Support.reflected (half n hn r s : Matrix _ (Index d k) ℂ) := by
  ext ⟨x,b⟩ ⟨y,c⟩
  change matrix d k _ (x,c) (y,b) = _
  rw [exchange_entry]
  have cap := congrFun (congrFun (bend_exchange (wordFork d (n*k) r (WireSchur.leftLe r))
    (wordFork d k r (WireSchur.rightLe r))) (active n hn x,b)) (active n hn y,c)
  change xmatrix d (n*k) k r (active n hn x,c) (active n hn y,b) =
    ((wordCap d (n*k) k r)ᴴ * (wordCap d (n*k) k r)) (active n hn x,b) (active n hn y,c) at cap
  simp only [Matrix.sum_apply,Support.reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,
    half,apply_ite star,star_zero,ite_mul,mul_ite,zero_mul,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [cap]
  by_cases h : idle n x=idle n y <;> simp [h,Matrix.mul_apply,Matrix.conjTranspose_apply]

end
end BlockPermanents.FourExchangeKernel
