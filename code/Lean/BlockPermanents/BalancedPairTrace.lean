import BlockPermanents.BalancedTrace
import BlockPermanents.BalancedOpen

/-! Trace comparisons on one edge of a balanced cut commute with any
chosen contraction on the other, disjoint edge. -/
namespace BlockPermanents.BalancedPairTrace
open Bend BalancedTrace BalancedSupport BalancedOpen
noncomputable section

/-- The fixed subspace of the orthogonal symmetric clasp. -/
def fixed (d k : ℕ) : Submodule ℂ (Word d k → ℂ) :=
  LinearMap.ker ((symClasp d k).mulVecLin - LinearMap.id)

private theorem in_fixed {d k} {u : Word d k → ℂ} : u ∈ fixed d k ↔ Symmetric u := by
  change (symClasp d k).mulVec u - u = 0 ↔ _
  exact sub_eq_zero

def unpack {K : Type*} (flip : Bool) (x : (K×K)×(K×K)) : Boundary K :=
  if flip then ((x.1.1,x.2.1),(x.2.2,x.1.2)) else ((x.1.1,x.2.1),(x.1.2,x.2.2))

def packing {K : Type*} (flip : Bool) : Boundary K ≃ (K×K)×(K×K) where
  toFun := arrange flip
  invFun := unpack flip
  left_inv _ := by cases flip <;> rfl
  right_inv _ := by cases flip <;> rfl

/-- Hold the other pair fixed. The first edge is symmetric in both packets
and supported on the chosen plane on its turned side. -/
structure EdgeSupported {d k} (U : Fin d → Fin k → ℂ)
    (z : ((Word d k×Word d k)×(Word d k×Word d k)) → ℂ) : Prop where
  ordinary : ∀ q j, (fun i => z ((i,j),q)) ∈ fixed d k
  turned : ∀ q i, (fun j => z ((i,j),q)) ∈ fixed d k
  plane : ∀ q i, (fun j => z ((i,j),q)) ∈ space k U

private def otherCap {d k} {T : Type*} (C : Matrix T (Word d k × Word d k) ℂ)
    (z : ((Word d k×Word d k)×(Word d k×Word d k)) → ℂ) (y : T) :
    Matrix (Word d k) (Word d k) ℂ := fun i j => ∑ q, C y q * z ((i,j),q)

private theorem edge_mem {Q I : Type*} [Fintype Q] (W : Submodule ℂ (I → ℂ))
    (c : Q → ℂ) (f : Q → I → ℂ) (h : ∀ q, f q ∈ W) :
    (fun i => ∑ q, c q * f q i) ∈ W := by
  rw [show (fun i => ∑ q, c q * f q i) = ∑ q, c q • f q by ext; simp]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ (c q) (h q)

private theorem joint_action {d k} {T : Type*} (flip : Bool) (r : CutIndex k k)
    (C : Matrix T (Word d k × Word d k) ℂ) (z : Boundary (Word d k) → ℂ)
    (w v : Word d (k-r)) (y : T) :
    (productRows flip (wordCap d k k r) C).mulVec z ((w,v),y) =
      (wordCap d k k r).mulVec (fun p => otherCap C (z ∘ unpack flip) y p.1 p.2) (w,v) := by
  show (∑ x, _) = _
  rw [← (packing flip).symm.sum_comp (fun x => productRows flip (wordCap d k k r) C ((w,v),y) x*z x),
    Fintype.sum_prod_type]
  have he (p q : Word d k × Word d k) : arrange flip ((packing flip).symm (p,q)) = (p,q) :=
    (packing flip).apply_symm_apply _
  simp only [productRows,he, Matrix.mulVec, dotProduct,otherCap,Function.comp_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change _ * _ * z (unpack flip (p,q)) = _ * (_ * z (unpack flip (p,q)))
  ring

/-- Bound full contraction on the first edge while applying an arbitrary
matrix C on the other pair. Hence C may itself be any cutMatrix or full cap. -/
theorem complete_first {d k : ℕ} {T : Type*} [Fintype T]
    (flip : Bool) (r : CutIndex k k) (U : Fin d → Fin k → ℂ)
    (z : Boundary (Word d k) → ℂ) (C : Matrix T (Word d k × Word d k) ℂ)
    (hz : EdgeSupported U (z ∘ unpack flip)) :
    energy ((productRows flip (wordCap d k k (fullCut k)) C).mulVec z) ≤
      ((k+(k-r)-1).choose (k-r):ℝ) * energy ((productRows flip (wordCap d k k r) C).mulVec z) := by
  let A := otherCap C (z ∘ unpack flip)
  have hO (y j) : Symmetric (fun i => A y i j) :=
    in_fixed.mp (edge_mem _ (C y) _ (fun q => hz.ordinary q j))
  have hT (y i) : Symmetric (A y i) :=
    in_fixed.mp (edge_mem _ (C y) _ (fun q => hz.turned q i))
  have hp (y i) : A y i ∈ space k U :=
    edge_mem _ (C y) _ (fun q => hz.plane q i)
  have hr (s : CutIndex k k) (w v : Word d (k-s)) (y : T) :
      (productRows flip (wordCap d k k s) C).mulVec z ((w,v),y) =
        cutMatrix (PairBound.cut_le s) (A y) w v := by
    rw [joint_action]; exact partial_action s _ (hT y) (hO y) w v
  have un : Unique (Word d (k-(fullCut k).val)) := by
    simp only [fullCut,Nat.sub_self]; infer_instance
  letI := un
  have hf (y w v) : cutMatrix (PairBound.cut_le (fullCut k)) (A y) w v = (A y).trace := by
    rw [← partial_trace (PairBound.cut_le (fullCut k)) (A y)]
    simp [Matrix.trace,Matrix.diag,Subsingleton.elim w default,Subsingleton.elim v default]
  unfold energy
  simp only [Fintype.sum_prod_type,hr,hf]
  simp only [Finset.sum_const,Fintype.card_unique,Finset.card_univ,one_smul]
  rw [Finset.sum_comm (f := fun x y => ∑ t, Complex.normSq (cutMatrix (PairBound.cut_le r) (A t) x y))]
  simp_rw [Finset.sum_comm (f := fun x t => Complex.normSq (cutMatrix (PairBound.cut_le r) (A t) x _))]
  rw [Finset.sum_comm (f := fun y t => ∑ x, Complex.normSq (cutMatrix (PairBound.cut_le r) (A t) x y)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  rw [Finset.sum_comm]
  exact terminal_le (PairBound.cut_le r) U (A y) (hp y)

def reverse {K : Type*} (flip : Bool) (z : Boundary K → ℂ) (p : Boundary K) :=
  z (unpack flip (arrange flip p).swap)

private theorem product_entry {K A B : Type*} [Fintype K]
    (flip : Bool) (M : Matrix A (K×K) ℂ) (N : Matrix B (K×K) ℂ) (z : Boundary K → ℂ) (a b) :
    (productRows flip M N).mulVec z (a,b) =
      ∑ p : K×K, ∑ q : K×K, M a p * N b q * z (unpack flip (p,q)) := by
  change (∑ x, productRows flip M N (a,b) x * z x) = _
  rw [← (packing flip).symm.sum_comp (fun x => productRows flip M N (a,b) x*z x),Fintype.sum_prod_type]
  have he (p q : K×K) : arrange flip ((packing flip).symm (p,q)) = (p,q) :=
    (packing flip).apply_symm_apply _
  simp only [productRows, he]
  rfl

theorem energy_reverse {K A B : Type*} [Fintype K] [Fintype A] [Fintype B]
    (flip : Bool) (M : Matrix A (K×K) ℂ) (N : Matrix B (K×K) ℂ) (z : Boundary K → ℂ) :
    energy ((productRows flip M N).mulVec z) =
      energy ((productRows flip N M).mulVec (reverse flip z)) := by
  apply Fintype.sum_equiv (Equiv.prodComm _ _)
  rintro ⟨a,b⟩
  apply congrArg Complex.normSq
  change _ = (productRows flip N M).mulVec (reverse flip z) (b,a)
  rw [product_entry, product_entry, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  cases flip <;> dsimp [reverse,arrange,unpack] <;> ring

theorem complete_second {d k : ℕ} (flip : Bool) (r t : CutIndex k k) (U : Fin d → Fin k → ℂ)
    (z : Boundary (Word d k) → ℂ) (hz : EdgeSupported U (reverse flip z ∘ unpack flip)) :
    energy ((productCap flip d k r (fullCut k)).mulVec z) ≤
      ((k+(k-t)-1).choose (k-t):ℝ) * energy ((productCap flip d k r t).mulVec z) := by
  unfold productCap
  rw [energy_reverse flip _ _ z,energy_reverse flip _ _ z]
  exact complete_first flip t U _ _ hz

/-- A four-word input with all cables symmetric, the two turned ones in
the symmetric powers of their indicated planes. This is a linear slice
condition on an arbitrary joint tensor. -/
structure Supported {d k} (U V : Fin d → Fin k → ℂ) (z : Boundary (Word d k) → ℂ) : Prop where
  sym0 : ∀ b c e, (fun a => z ((a,b),(c,e))) ∈ fixed d k
  sym1 : ∀ a c e, (fun b => z ((a,b),(c,e))) ∈ fixed d k
  sym2 : ∀ a b e, (fun c => z ((a,b),(c,e))) ∈ fixed d k
  sym3 : ∀ a b c, (fun e => z ((a,b),(c,e))) ∈ fixed d k
  plane2 : ∀ a b e, (fun c => z ((a,b),(c,e))) ∈ space k U
  plane3 : ∀ a b c, (fun e => z ((a,b),(c,e))) ∈ space k V

theorem first_supported {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (hz : Supported U V z) :
    EdgeSupported (if flip then V else U) (z ∘ unpack flip) := by
  cases flip
  · exact ⟨fun q j => hz.sym0 q.1 j q.2,fun q i => hz.sym2 i q.1 q.2,fun q i => hz.plane2 i q.1 q.2⟩
  · exact ⟨fun q j => hz.sym0 q.1 q.2 j,fun q i => hz.sym3 i q.1 q.2,fun q i => hz.plane3 i q.1 q.2⟩

theorem second_supported {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (hz : Supported U V z) :
    EdgeSupported (if flip then U else V) (reverse flip z ∘ unpack flip) := by
  cases flip
  · exact ⟨fun q j => hz.sym1 q.1 q.2 j,fun q i => hz.sym3 q.1 i q.2,fun q i => hz.plane3 q.1 i q.2⟩
  · exact ⟨fun q j => hz.sym1 q.1 j q.2,fun q i => hz.sym2 q.1 i q.2,fun q i => hz.plane2 q.1 i q.2⟩

theorem raw_product {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (hz : Supported U V z)
    (r t : CutIndex k k) (a b : Word d (k-r)) (c e : Word d (k-t)) :
    (productCap flip d k r t).mulVec z ((a,b),(c,e)) =
      ∑ s, ∑ v, z (unpack flip ((join (PairBound.cut_le r) a s,join (PairBound.cut_le r) b s),
        (join (PairBound.cut_le t) c v,join (PairBound.cut_le t) e v))) := by
  let C := wordCap d k k t
  let A := otherCap C (z ∘ unpack flip) (c,e)
  have hl := first_supported flip hz
  have hr := second_supported flip hz
  have hO (j) : Symmetric (fun i => A i j) :=
    in_fixed.mp (edge_mem _ (C (c,e)) _ (fun q => hl.ordinary q j))
  have hT (i) : Symmetric (A i) :=
    in_fixed.mp (edge_mem _ (C (c,e)) _ (fun q => hl.turned q i))
  rw [productCap,joint_action]
  change (wordCap d k k r).mulVec (fun p => A p.1 p.2) (a,b) = _
  rw [partial_action r _ hT hO]
  apply Finset.sum_congr rfl
  intro s _
  let p := (join (PairBound.cut_le r) a s,join (PairBound.cut_le r) b s)
  let Z : Matrix (Word d k) (Word d k) ℂ := fun i j => z (unpack flip (p,(i,j)))
  have hr' (w : (Word d k × Word d k) × (Word d k × Word d k)) :
      (reverse flip z ∘ unpack flip) w = z (unpack flip w.swap) := by cases flip <;> rfl
  have hS₁ (j) : Symmetric (fun i => Z i j) := by
    apply in_fixed.mp; simpa only [hr',Z] using hr.ordinary p j
  have hS₂ (i) : Symmetric (Z i) := by
    apply in_fixed.mp; simpa only [hr',Z] using hr.turned p i
  exact partial_action t Z hS₂ hS₁ c e


end
end BlockPermanents.BalancedPairTrace
