import BlockPermanents.ThreeCanonical
import BlockPermanents.ClaspAbsorb

/-! # Rejoining the three-packet spectator and the fine pair on word matrices -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend ThreeTransfer TransferBlocks
open scoped Matrix BigOperators
noncomputable section

def join3 (d k : ℕ) : ThreeWords d k ≃ K d (k+k) × K d k :=
  (Bridges.joinWords d k).prodCongr (Equiv.refl _)

def firstFine (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ :=
  ThreeTransfer.upright (totalClasp d k k)

def secondFine (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := fun i j =>
  if i.1.1=j.1.1 then totalClasp d k k (i.1.2,i.2) (j.1.2,j.2) else 0

def allFine (d k : ℕ) : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := fun i j =>
  totalClasp d (k+k) k (join3 d k i) (join3 d k j)

private lemma upright_legs {A B C J L : Type*} [Fintype B] [Fintype L] [DecidableEq L]
    (T : Matrix A B ℂ) (X : Matrix B C ℂ) (N : Matrix L J ℂ) :
    ThreeTransfer.upright T * legs X N = legs (T*X) N := by
  ext ⟨a,b⟩ ⟨c,j⟩
  simp only [ThreeTransfer.upright,legs,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_mul,mul_assoc]

theorem fine_leg (d k : ℕ) : firstFine d k * internal d k = legs (stackedFine (P d k)) (symClasp d k) := by
  rw [firstFine,internal,upright_legs,total_absorbs]; rfl

theorem fine_star (d k : ℕ) : (firstFine d k)ᴴ = firstFine d k := by
  ext i j
  simp only [firstFine,Matrix.conjTranspose_apply,upright,apply_ite star,star_zero,totalClasp,column_star]
  by_cases he : i.2=j.2 <;> simp [he,Ne.symm,eq_comm]

private theorem contract_slices {S T H A : Type*} [Fintype S] [Fintype T] [Fintype H] [DecidableEq S]
    (C : Matrix ((S × T) × H) A ℂ) (B : Matrix (T × H) (T × H) ℂ) :
    Cᴴ * Matrix.of (fun i j : (S × T) × H => if i.1.1 = j.1.1 then B (i.1.2,i.2) (j.1.2,j.2) else 0) * C =
      ∑ s, (Matrix.of (fun i : T × H => C ((s,i.1),i.2)))ᴴ * B * (Matrix.of (fun i : T × H => C ((s,i.1),i.2))) := by
  ext i j
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.of_apply,Fintype.sum_prod_type,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_mul]
  simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem opened_small (d k : ℕ) : opened (M d k) (symClasp d k) =
    (legs (stack (M d k)) (symClasp d k))ᴴ * secondFine d k * (legs (stack (M d k)) (symClasp d k)) := by
  exact (contract_slices (legs (stack (M d k)) (symClasp d k)) (totalClasp d k k)).symm

private theorem transport_full {T U A : Type*} [Fintype T] [Fintype U] (e : T ≃ U)
    (C : Matrix U A ℂ) (B : Matrix U U ℂ) :
    Cᴴ * B * C = (Matrix.of (fun i : T => C (e i)))ᴴ * (Matrix.of (fun i j : T => B (e i) (e j))) * (Matrix.of (fun i : T => C (e i))) := by
  ext i j; simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.of_apply]
  rw [← e.sum_comp]; apply Finset.sum_congr rfl; intro t _
  exact congrArg (· * C (e t) j) (e.sum_comp _).symm

theorem opened_big (d k : ℕ) : opened (fun _ : Unit => P d k) (symClasp d k) =
    (legs (stackedFine (P d k)) (symClasp d k))ᴴ * allFine d k * (legs (stackedFine (P d k)) (symClasp d k)) := by
  unfold opened; rw [Finset.univ_unique, Finset.sum_singleton]
  exact transport_full (join3 d k) _ _

theorem straight_big (d k : ℕ) : straight (fun _ : Unit => P d k) (symClasp d k) =
    (legs (stackedFine (P d k)) (symClasp d k))ᴴ * (legs (stackedFine (P d k)) (symClasp d k)) := by
  ext i j; simp only [straight,Finset.univ_unique,Finset.sum_singleton,Support.reflected,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact ((join3 d k).sum_comp (fun t => star (legs (P d k) (symClasp d k) t i) * legs (P d k) (symClasp d k) t j)).symm

private lemma swap_join {D : Type*} {k : ℕ} (a b : Fin k → D) :
    ∃ σ : Equiv.Perm (Fin (k+k)), Fin.append b a = Fin.append a b ∘ σ := by
  let σ : Equiv.Perm (Fin (k+k)) := finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)
  refine ⟨σ,?_⟩;funext i;obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [σ, Function.comp_apply,-Fin.natAdd_eq_addNat]

private lemma upright_comp {A B C L : Type*} [Fintype B] [Fintype L] [DecidableEq L]
    (X : Matrix A B ℂ) (Y : Matrix B C ℂ) :
    ThreeTransfer.upright (K:=L) (X*Y) = ThreeTransfer.upright X * ThreeTransfer.upright Y := by
  ext ⟨a,l⟩ ⟨c,m⟩
  simp [ThreeTransfer.upright,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,Finset.sum_ite_irrel]

private theorem total_sq (d k : ℕ) : totalClasp d k k * totalClasp d k k = totalClasp d k k := by
  ext a b
  change (∑ i : K d k × K d k, symClasp d (k+k) (Fin.append a.1 a.2) (Fin.append i.1 i.2) *
    symClasp d (k+k) (Fin.append i.1 i.2) (Fin.append b.1 b.2)) = _
  exact ((Bridges.joinWords d k).sum_comp (fun i : K d (k+k) =>
    symClasp d (k+k) (Fin.append a.1 a.2) i * symClasp d (k+k) i (Fin.append b.1 b.2))).trans (congrFun (column_symmetric d (k+k) _) _)

theorem first_sq (d k : ℕ) : firstFine d k * firstFine d k = firstFine d k := by
  rw [firstFine,←upright_comp,total_sq]

theorem first_front (d k : ℕ) : swapFront d k * firstFine d k = firstFine d k := by
  ext ⟨⟨a,b⟩,v⟩ ⟨⟨i,j⟩,w⟩
  rw [front_mul]
  obtain ⟨σ,h⟩ := swap_join a b
  simp only [firstFine,upright,totalClasp,Prod.swap_prod_mk,h]
  rw [←column_star, symClasp_right_perm, column_star]

theorem first_pair (d k : ℕ) : pair (swapFront d k) * firstFine d k = firstFine d k := by
  rw [pair,smul_mul_assoc,add_mul,one_mul,first_front]; module

theorem pair_first (d k : ℕ) : firstFine d k * pair (swapFront d k) = firstFine d k := by
  simpa only [Matrix.conjTranspose_mul,fine_star,pair_star] using congrArg Matrix.conjTranspose (first_pair d k)

theorem all_first (d k : ℕ) : allFine d k * firstFine d k = allFine d k := by
  ext i ⟨⟨a,b⟩,j⟩
  simp only [firstFine,upright,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change (∑ s, ∑ t, symClasp d ((k+k)+k) _ (Fin.append (Fin.append s t) j) *
    symClasp d (k+k) (Fin.append s t) (Fin.append a b)) = _
  rw [← Fintype.sum_prod_type']
  let e := Bridges.joinWords d k
  have h := e.sum_comp (fun w : K d (k+k) => symClasp d ((k+k)+k)
    (Fin.append (Fin.append i.1.1 i.1.2) i.2) (Fin.append w j) * symClasp d (k+k) w (Fin.append a b))
  exact h.trans (avg_fixed _ (Fin.append a b) (fun π => by
    change symClasp _ _ _ (Fin.append (Fin.append a b ∘ π) (j ∘ (1 : Equiv.Perm (Fin k)))) = _
    rw [append_permute,symClasp_right_perm]))

end
end BlockPermanents.ThreeGeneralOpen
