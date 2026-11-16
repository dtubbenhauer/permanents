import BlockPermanents.ZeroCapDefs

/-! The zero, proper and terminal terms of the marked Schur opening at the two
scales, with their factorial normalization, on the full mixed packet boundary. -/
namespace BlockPermanents.ZeroCap
open Bend ThreeGeneralOpen Support SchurNormalization
open scoped BigOperators Matrix
noncomputable section

theorem factorial_step (m k : ℕ) : a (m+1) k = a m k * ((m*k+k).choose (m*k):ℂ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial (m*k) k
  rw [← Nat.choose_symm_add] at h
  have hc : ((m*k+k).choose (m*k):ℂ) * ((m*k).factorial:ℂ) * (k.factorial:ℂ) =
    ((m*k+k).factorial:ℂ) := by exact_mod_cast h
  have hn : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [a,Nat.add_mul,one_mul,pow_succ,← hc]
  field_simp
  ring

theorem singleton_clasp (d : ℕ) : symClasp d 1=1 := by
  ext x y
  by_cases h : x=y <;> simp [symClasp,Matrix.one_apply,h,Finset.filter_singleton]

private theorem coarse_sym (d k m : ℕ) (i) : Symmetric (fun w => coarseMerge d k m w i) :=
  PairBound.projected_symmetric _ _ _
private theorem mark_sym (d k : ℕ) (j) : Symmetric (fun w => coarseMark d k w j) := by
  unfold Bend.Symmetric
  rw [singleton_clasp,Matrix.one_mulVec]

theorem gram_legs {A B I J : Type*} [Fintype A] [Fintype B]
    (M : Matrix A I ℂ) (N : Matrix B J ℂ) :
    reflected (legs M N) = legs (reflected M) (reflected N) := by
  ext ⟨i,j⟩ ⟨v,w⟩
  simp only [reflected,legs,Matrix.mul_apply,Matrix.conjTranspose_apply,star_mul',
    Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  ring

private theorem empty_square {d p k : ℕ} {I J : Type*} (M : Matrix (Word d p) I ℂ)
    (N : Matrix (Word d k) J ℂ) (hM : ∀ i,Symmetric (fun w => M w i))
    (hN : ∀ j,Symmetric (fun w => N w j)) :
    (∑ s : Unit, reflected (routed (fun _ : Unit => M) N (emptyCut p k) s)) =
    legs (reflected M) (reflected (dual N)) := by
  simp only [routed_zero _ N (fun _ => hM) hN,Finset.univ_unique,Finset.sum_singleton,gram_legs]

private theorem dual_mark (d k : ℕ) : reflected (dual (mark d k)) = symClasp d k := by
  have real (x y : Packet d k) : star (symClasp d k x y) = symClasp d k x y := by
    simp [symClasp,star_sum,apply_ite]
  have hh : dual (mark d k)=symClasp d k := by ext x y;exact real _ _
  have hh' : (symClasp d k)ᴴ=symClasp d k := by ext x y;exact column_star _ _
  rw [hh,reflected,hh']
  ext x y;exact congrFun (column_symmetric d k y) x
private theorem dual_coarseMark (d k : ℕ) : reflected (dual (coarseMark d k)) = symClasp d k := by
  rw [←dual_mark]
  ext i j
  exact ((single d k).sum_comp (fun w => star (dual (coarseMark d k) w i) * dual (coarseMark d k) w j)).symm.trans (by simp [dual,coarseMark,reflected,Matrix.mul_apply,Matrix.conjTranspose_apply])

/-- The terminal Schur cut is exactly contraction over the last whole packet.
Changing survivor and letter coordinates contributes no scalar. -/
theorem last_square {K I J : Type*} [Fintype K] {d p k n : ℕ} (hp : k≤p)
    (front : (Fin n→K) ≃ Word d (p-k)) (letter : K ≃ Word d k)
    (M : Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ i,Symmetric (fun w => M w i)) (hN : ∀ j,Symmetric (fun w => N w j)) :
    (∑ s : Unit, reflected (routed (fun _ : Unit => M) N (lastCut p k hp) s)) =
    reflected (fullCut (termRows hp front letter M) (fun t j => N (letter t) j)) := by
  have hentry (t : Fin n→K) (b : Word d (k-k)) (y : I×J) :
      routed (fun _ : Unit => M) N (lastCut p k hp) () (front t,b) y =
      fullCut (termRows hp front letter M) (fun t j => N (letter t) j) t y := by
    rcases y with ⟨i,j⟩
    rw [routed_entry _ N (fun _ => hM) hN]
    simp only [lastCut,fullCut,termRows,Fin.init_snoc,Fin.snoc_last]
    rw [← letter.sum_comp]
    apply Finset.sum_congr rfl;intro a _
    simp only [Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def]
    rfl
  ext i j
  simp only [Finset.univ_unique,Finset.sum_singleton,reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type]
  refine (front.sum_comp (fun (w : Word d (p-k)) => ∑ b : Word d (k-k),
    star (routed (fun _ : Unit => M) N (lastCut p k hp) () (w,b) i) *
      routed (fun _ : Unit => M) N (lastCut p k hp) () (w,b) j)).symm.trans ?_
  apply Finset.sum_congr rfl;intro t _
  calc
    _ = ∑ _b : Word d (k-k), star (fullCut (termRows hp front letter M) (fun t j => N (letter t) j) t i) *
          fullCut (termRows hp front letter M) (fun t j => N (letter t) j) t j := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hentry t b i,hentry t b j]
    _ = _ := by simp [Fintype.card_fun]

private theorem partition {d p k : ℕ} {I J : Type*} (hk : 0<k) (hp : k≤p)
    (hs : HomogeneousSchur d p k) (M : Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (hM : ∀ i,Symmetric (fun w => M w i)) (hN : ∀ j,Symmetric (fun w => N w j)) :
    ((p+k).choose p : ℂ) • partialTranspose (opened (fun _ : Unit => M) N) =
      legs (reflected M) (reflected (dual N)) + properSquares hp (fun _ : Unit => M) N +
      (p.choose k : ℂ) • (∑ s : Unit, reflected (routed (fun _ : Unit => M) N (lastCut p k hp) s)) := by
  rw [schur_open hs,ends_sum hk hp,show weight p k (emptyCut p k)=1 by simp [weight,emptyCut],
    show weight p k (lastCut p k hp)=p.choose k by simp [weight,lastCut],
    Nat.cast_one,one_smul,empty_square M N hM hN]
  unfold properSquares
  abel

private theorem no_proper {D n : ℕ} {I J : Type*} (M : Matrix (Word D (n+1)) I ℂ)
    (N : Matrix (Word D 1) J ℂ) :
    properSquares (show 1≤n+1 by omega) (fun _ : Unit => M) N=0 := by
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨hn,hr⟩ := Finset.mem_erase.mp hr
  obtain ⟨hz,_⟩ := Finset.mem_erase.mp hr
  have hnn : r.val ≠ 1 := fun h => hn (Fin.ext h)
  have hzz : r.val ≠ 0 := fun h => hz (Fin.ext h)
  have hl := WireSchur.rightLe r
  omega

/-- The zero-cap remainder, with the final thin full cut exhibited separately.
In these ambient words the identity of the marked symmetric cable is its clasp. -/
theorem opening (d k n : ℕ) (hk : 0<k)
    (hFine : HomogeneousSchur d ((n+1)*k) k)
    (hPacket : HomogeneousSchur (dim d k) (n+1) 1) :
    partialTranspose (newX d k (n+1)) =
      legs (oldX d k (n+1)) (symClasp d k) + a (n+1) k • proper d k n +
      (a (n+1) k * (((n+1)*k).choose k:ℂ)) • reflected (fullCut (thinRows d k n) (mark d k)) -
      (((n+1:ℕ):ℂ)*((n+1).factorial:ℂ)) • reflected (fullCut (packetRows d k n) (mark d k)) := by
  let m := n+1
  let M := merge d k m
  let N := mark d k
  let C := coarseMerge d k m
  let L := coarseMark d k
  have hm (i) : Symmetric (fun w => M w i) := column_symmetric _ _ _
  have hN (i) : Symmetric (fun w => N w i) := column_symmetric _ _ _
  have hf := partition hk (thin_le n k) hFine M N hm hN
  rw [dual_mark,last_square (thin_le n k) (thinFront d k n) (Equiv.refl _) M N hm hN] at hf
  have hc := partition (by decide : 0<1) (show 1≤m by dsimp [m];omega) hPacket C L
    (coarse_sym _ _ _) (mark_sym _ _)
  rw [dual_coarseMark,no_proper,add_zero,Nat.choose_one_right,Nat.choose_succ_self_right,
    last_square (show 1≤m by dsimp [m];omega) (coarseFront d k n) (single d k) C L
      (coarse_sym _ _ _) (mark_sym _ _)] at hc
  have e : (fun t j => L (single d k t) j)=N := by funext t j;simp [L,N,coarseMark]
  rw [e] at hc
  change turn (newX d k m) = _
  simp only [newX,map_sub,map_smul]
  change a (m+1) k • partialTranspose (opened (fun _ : Unit => M) N) -
    ((m+1).factorial:ℂ) • partialTranspose (opened (fun _ : Unit => C) L) = _
  have hfac : ((m+1).factorial:ℂ) = (m.factorial:ℂ) * (m+1:ℕ) := by
    rw [Nat.factorial_succ,Nat.cast_mul,mul_comm]
  rw [factorial_step,hfac,←smul_smul,←smul_smul,hf,hc]
  have old : legs (oldX d k m) (symClasp d k) =
      a m k • legs (reflected M) (symClasp d k) -
        (m.factorial:ℂ) • legs (reflected C) (symClasp d k) := by
    ext i j; simp only [oldX,legs,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,M,C];ring
  change _ = legs (oldX d k m) (symClasp d k) + a m k • proper d k n +
      (a m k * ((m*k).choose k:ℂ)) • reflected (fullCut (thinRows d k n) N) -
      ((m:ℂ)*(m.factorial:ℂ)) • reflected (fullCut (packetRows d k n) N)
  rw [old]
  change a m k • (_ + proper d k n + ((m*k).choose k:ℂ) • reflected (fullCut (thinRows d k n) N)) -
    (m.factorial:ℂ) • (_ + (m:ℂ) • reflected (fullCut (packetRows d k n) N)) = _
  module

end
end BlockPermanents.ZeroCap
