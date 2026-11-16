import BlockPermanents.BalancedOpen
import BlockPermanents.PairBound
import BlockPermanents.WireSchur

/-! The four corner terms of a crossed two-edge Schur opening are exactly
the two independent packet-order projectors. -/
namespace BlockPermanents.BalancedCorners
open Bend Support BalancedOpen
open scoped Matrix BigOperators
noncomputable section

private theorem real_entry {d k} (x y : Word d k) : star (symClasp d k x y)=symClasp d k x y := by
  simp [symClasp,star_sum,apply_ite]

private theorem symmetric_entry {d k} (x y : Word d k) : symClasp d k x y=symClasp d k y x :=
  (real_entry x y).symm.trans (WireSchur.symClasp_star x y)

private theorem project_col {d k} (x y : Word d k) :
    (∑ s, symClasp d k s x * symClasp d k s y) = symClasp d k x y := by
  have q := PairBound.projected_symmetric d k (Pi.single y (1:ℂ))
  have h : (symClasp d k).mulVec (Pi.single y (1:ℂ)) = fun t => symClasp d k t y := by
    funext t;simp [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite]
  rw [h] at q
  have he := congrFun q x
  change (∑ s, symClasp d k x s * symClasp d k s y)=symClasp d k x y at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro s _
  rw [symmetric_entry s x]

private theorem zero_entry {d k} (a b x y : Word d k) :
    wordCap d k k (zeroCut k) (a,b) (x,y) = symClasp d k a x * symClasp d k b y := by
  simp only [wordCap, zeroCut, cap, wordFork,Fin.append_right_nil _ _ rfl, Function.comp_def]
  simp [real_entry,Fintype.card_fun]

private theorem last_entry {d k} (a b : Word d (k-k)) (x y : Word d k) :
    wordCap d k k (fullCut k) (a,b) (x,y) = symClasp d k x y := by
  simp only [wordCap,fullCut,cap,wordFork,Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def,
    real_entry]
  exact project_col x y

theorem first_square {d k} (i j : Word d k × Word d k) :
    reflected (wordCap d k k (zeroCut k)) i j =
      symClasp d k i.1 j.1 * symClasp d k i.2 j.2 := by
  have got (a b : Word d k) (x : Word d k × Word d k) : wordCap d k k (zeroCut k) (a,b) x =
      symClasp d k a x.1 * symClasp d k b x.2 := zero_entry a b x.1 x.2
  simp only [reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    got,star_mul',real_entry]
  rw [← project_col i.1 j.1,← project_col i.2 j.2,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem last_square {d k} (i j : Word d k × Word d k) :
    reflected (wordCap d k k (fullCut k)) i j =
      symClasp d k i.1 i.2 * symClasp d k j.1 j.2 := by
  have got (a b : Word d (k-k)) (x : Word d k × Word d k) : wordCap d k k (fullCut k) (a,b) x =
      symClasp d k x.1 x.2 := last_entry a b x.1 x.2
  simp only [reflected,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,got,real_entry]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    fullCut,Nat.sub_self,pow_zero,one_smul]

/-- The two orders of a pair of packets, each with its own internal clasp. -/
def packetPair (d k : ℕ) : Matrix (Word d k × Word d k) (Word d k × Word d k) ℂ :=
  fun a b => (symClasp d k a.1 b.1*symClasp d k a.2 b.2+
    symClasp d k a.1 b.2*symClasp d k a.2 b.1)/2

theorem pair_ends {d k} :
    (2:ℂ) • partialTranspose (packetPair d k) =
      reflected (wordCap d k k (zeroCut k)) + reflected (wordCap d k k (fullCut k)) := by
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,partialTranspose,packetPair,Matrix.add_apply,
    first_square,last_square]
  rw [symmetric_entry j.2 i.2,symmetric_entry j.2 j.1]
  ring

/-- The four corner indices in the product of the two disjoint caps. -/
def corners (k : ℕ) := ({zeroCut k, fullCut k} : Finset (CutIndex k k)) ×ˢ
  ({zeroCut k, fullCut k} : Finset (CutIndex k k))

def weighted (flip : Bool) (d k : ℕ) (u : CutIndex k k × CutIndex k k) :=
  ((weight k k u.1 : ℂ)*(weight k k u.2 : ℂ)) • reflected (productCap flip d k u.1 u.2)

/-- The actual crossing-pair correction B_M on the four ordinary word blocks. -/
def correction (flip : Bool) (d k : ℕ) :=
  (((k+k).choose k : ℂ)^2) • productFine flip d k -
    (4:ℂ) • productOperator flip (packetPair d k) (packetPair d k)

theorem four_corners {d k} (hk : 0<k) (flip : Bool) :
    ∑ u ∈ corners k, weighted flip d k u =
      (4:ℂ) • partialTranspose (productOperator flip (packetPair d k) (packetPair d k)) := by
  have hne : zeroCut k ≠ fullCut k := fun h => hk.ne (congrArg Fin.val h)
  have hz : weight k k (zeroCut k)=1 := by simp [weight,zeroCut]
  have hf : weight k k (fullCut k)=1 := by simp [weight,fullCut]
  ext i j
  simp only [corners,Finset.sum_product,Finset.sum_insert (Finset.not_mem_singleton.mpr hne),
    Finset.sum_singleton,weighted,hz,hf,Nat.cast_one,mul_one,one_smul,
    productCap,glue_product,bend_product,productOperator,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  have h1 := congrArg (fun C : Matrix _ _ ℂ => C (arrange flip i).1 (arrange flip j).1)
    (pair_ends (d:=d) (k:=k))
  have h2 := congrArg (fun C : Matrix _ _ ℂ => C (arrange flip i).2 (arrange flip j).2)
    (pair_ends (d:=d) (k:=k))
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply] at h1 h2
  rw [show (4:ℂ)=2*2 by norm_num,mul_mul_mul_comm,h1,h2]
  ring

/-- Opening the crossed correction cancels precisely its four corners. -/
theorem open_correction {d k : ℕ} (hk : 0<k) (flip : Bool)
    (h : SchurNormalization.HomogeneousSchur d k k) :
    partialTranspose (correction flip d k) = ∑ u ∈ (corners k)ᶜ, weighted flip d k u := by
  have ht := crossing_schur flip h
  have hsum : (∑ u,weighted flip d k u) =
      (∑ u ∈ corners k,weighted flip d k u) + ∑ u ∈ (corners k)ᶜ,weighted flip d k u :=
    (Finset.sum_add_sum_compl _ _).symm
  rw [Fintype.sum_prod_type] at hsum
  change _ = ∑ r,∑ t,weighted flip d k (r,t) at ht
  rw [hsum,four_corners hk] at ht
  have hc : partialTranspose (correction flip d k) =
      (((k+k).choose k : ℂ)^2) • partialTranspose (productFine flip d k) -
      (4:ℂ) • partialTranspose (productOperator flip (packetPair d k) (packetPair d k)) := rfl
  rw [hc,ht,add_sub_cancel_left]

end
end BlockPermanents.BalancedCorners
