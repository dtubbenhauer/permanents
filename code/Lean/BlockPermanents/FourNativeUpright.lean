import BlockPermanents.FourExchangeBasis
import BlockPermanents.FourAdjoints
import BlockPermanents.FourNativeCap

/-! # Ordinary factors in the word matrix of the marked four-packet transfer -/
namespace BlockPermanents.FourNative
open FourTarget FourRoutes FourExchangeKernel FourWireAlgebra FourAdjoints Bend ThreeTransfer
open scoped Matrix BigOperators
noncomputable section

variable {d k : ℕ}

private def uprightAlg {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A] [DecidableEq K] :
    Matrix A A ℂ →ₐ[ℚ] Matrix (A×K) (A×K) ℂ where
  toFun := upright
  map_one' := by ext i j; rcases i with ⟨a,b⟩; rcases j with ⟨c,e⟩
                 by_cases h : b=e <;> simp [upright,Matrix.one_apply,h,Prod.ext_iff]
  map_mul' a b := by ext i j; by_cases h : i.2=j.2 <;>
      simp [upright,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul,h]
  map_zero' := by ext i j; simp [upright]
  map_add' a b := by ext i j; by_cases h : i.2=j.2 <;> simp [upright,h]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    ext ⟨a,b⟩ ⟨f,g⟩
    by_cases h : b=g <;> simp [upright,h,Matrix.one_apply,Prod.ext_iff]

def ordinaryAlgebra (d k : ℕ) : Subalgebra ℚ (Op d k) :=
  (uprightAlg (A:=Triple d k) (K:=Word d k)).range.comap (matrix d k)

theorem getUpright {A : Op d k} (h : A ∈ ordinaryAlgebra d k) :
    ∃ B : Matrix (Triple d k) (Triple d k) ℂ, matrix d k A = upright B := by
  obtain ⟨B,hB⟩ := h
  exact ⟨B,hB.symm⟩

theorem layout_read (x : Index d k) (i : Fin 3) (j : Fin k) :
    (layout d k).symm x (i.castSucc,j)=x.1 i j := by fin_cases i <;> rfl

theorem act_ordinary (p : Wire k) (hp : ∀ j : Fin k, p (3,j)=(3,j)) :
    act d k p ∈ ordinaryAlgebra d k := by
  have hi (i : Fin 3) (j : Fin k) : (p (i.castSucc,j)).1.val < 3 := by
    by_contra! h
    have h3 : (p (i.castSucc,j)).1 = 3 := Fin.ext (by
      have := (p (i.castSucc,j)).1.isLt; omega)
    have he : p (i.castSucc,j) = p (3,(p (i.castSucc,j)).2) := by rw [hp]; exact Prod.ext h3 rfl
    have hne := congrArg (fun a : Slot k => a.1.val) (p.injective he)
    change i.val=3 at hne; omega
  let sh (z : Triple d k) (i : Fin 3) (j : Fin k) :=
    z ⟨(p (i.castSucc,j)).1.val,hi i j⟩ (p (i.castSucc,j)).2
  refine ⟨fun u v => if sh u=v then 1 else 0, ?_⟩
  ext x y
  change upright (fun u v => if sh u=v then (1:ℂ) else 0) x y = matrix d k (act d k p) x y
  rw [matrix_perm_apply]
  have hw : layout d k ((layout d k).symm x ∘ p) = (sh x.1,x.2) := by
    apply Prod.ext
    · funext i j
      exact layout_read x ⟨(p (i.castSucc,j)).1.val,hi i j⟩ (p (i.castSucc,j)).2
    · funext j; change (layout d k).symm x (p (3,j))=x.2 j; rw [hp]; rfl
  rw [hw]
  change (if x.2=y.2 then (if sh x.1=y.1 then (1:ℂ) else 0) else 0)=_
  rcases y with ⟨v,l⟩
  by_cases h : x.2=l <;> simp [Prod.ext_iff,h]

theorem local_ordinary (d k n : ℕ) (hn : n ≤ 3) : localClasp d k n ∈ ordinaryAlgebra d k := by
  letI : Fintype (group k n) := Fintype.ofFinite _
  apply Subalgebra.smul_mem
  apply Subalgebra.sum_mem
  intro p _
  exact act_ordinary p.val (fun j => p.property (3,j) hn)

theorem packet_ordinary (p : TransferBlocks.FourPerm) (hp : p 3=3) :
    packets d k p ∈ ordinaryAlgebra d k :=
  act_ordinary (wires k p) (fun j => Prod.ext hp rfl)

theorem average_ordinary (d k : ℕ) : ordinary (packets d k) ∈ ordinaryAlgebra d k := by
  have u : packets d k TransferBlocks.swap12 ∈ ordinaryAlgebra d k := packet_ordinary _ (by decide)
  have v : packets d k TransferBlocks.swap23 ∈ ordinaryAlgebra d k := packet_ordinary _ (by decide)
  let S := ordinaryAlgebra d k
  exact S.smul_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem S.one_mem u) v)
    (S.mul_mem u v)) (S.mul_mem v u)) (S.mul_mem (S.mul_mem u v) u)) _

theorem reflected_matrix {A B : Op d k} (h : Reflected A B) :
    (matrix d k A)ᴴ = matrix d k B := by
  classical
  ext x y
  let a := (layout d k).symm x
  let b := (layout d k).symm y
  have H := h (Pi.single b 1) (Pi.single a 1)
  change Closures.bracket (Pi.single b 1) (A (Pi.single a 1)) =
    Closures.bracket (B (Pi.single b 1)) (Pi.single a 1) at H
  simp [Closures.bracket, Pi.single_apply,ite_mul,mul_ite] at H
  have hd (z : Slot k → Fin d) : Pi.single z (1:ℂ) = (fun v => if v=z then (1:ℂ) else 0) := by
    funext v; simp [Pi.single_apply]
  simpa [Matrix.conjTranspose_apply,matrix_entry,a,b,hd] using congrArg star H

theorem packet_cross (d k : ℕ) : matrix d k (packets d k TransferBlocks.swap14) =
    FourNativeCap.swapMatrix := by
  ext ⟨u,h⟩ ⟨v,g⟩
  rw [show packets d k TransferBlocks.swap14=act d k (wires k TransferBlocks.swap14) by rfl,matrix_perm_apply]
  have H : layout d k ((layout d k).symm (u,h) ∘ wires k TransferBlocks.swap14)=(![h,u 1,u 2],u 0) := by
    apply Prod.ext
    · funext i;fin_cases i <;> rfl
    · rfl
  rw [H]
  simp only [FourNativeCap.swapMatrix,ThreeTransfer.cross,FourNativeCap.order,Equiv.coe_fn_mk,Prod.mk.injEq]
  congr 1
  apply propext
  constructor
  · rintro ⟨e,e'⟩;subst v;subst g; exact ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨⟨⟨e₁,e₂⟩,e₃⟩,e₄⟩
    exact ⟨by funext i;fin_cases i; exact e₄;exact e₁;exact e₂,e₃⟩

end
end BlockPermanents.FourNative
