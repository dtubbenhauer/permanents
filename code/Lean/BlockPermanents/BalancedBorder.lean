import BlockPermanents.BalancedCorners
import BlockPermanents.BalancedSupport

/-! # Summing the supported last-cap weights around the crossing cut rectangle -/
namespace BlockPermanents.BalancedSupport
open Bend
open scoped BigOperators
noncomputable section

def ends (k : ℕ) : Finset (CutIndex k k) := {zeroCut k,fullCut k}
def mid (k : ℕ) := (ends k)ᶜ

theorem rectangle (k : ℕ) : (BalancedCorners.corners k)ᶜ =
    (mid k ×ˢ ends k) ∪ (ends k ×ˢ mid k) ∪ (mid k ×ˢ mid k) := by
  ext ⟨i,j⟩
  simp only [BalancedCorners.corners,ends,mid,Finset.mem_compl,Finset.mem_product,Finset.mem_union]
  tauto

theorem middle_weight (k : ℕ) : ∑ r ∈ mid k, weight k r.val = lastWeight k := by
  unfold lastWeight
  have hm (r : CutIndex k k) : r ∈ mid k ↔ 1 ≤ r.val ∧ r.val < k := by
    have hr : r.val ≤ k := by have := r.isLt;simp only [min_self] at this;omega
    simp only [mid,ends,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,zeroCut,fullCut]
    omega
  apply Finset.sum_bij (fun r _ => r.val)
  · intro r hr;exact Finset.mem_Ico.mpr ((hm r).mp hr)
  · intro _ _ _ _ e; exact Fin.ext e
  · intro n hn
    have h := Finset.mem_Ico.mp hn
    let t : CutIndex k k := ⟨n,by simp only [min_self];omega⟩
    exact ⟨t,(hm t).mpr h,rfl⟩
  · intro _ _;rfl

private theorem complete_weight {k : ℕ} (hk : 0<k) (r : CutIndex k k) (A B : ℝ)
    (h : A ≤ ((k+(k-r.val)-1).choose (k-r.val):ℝ)*B) :
    weight k r.val*A ≤ (Bend.weight k k r:ℝ)*B := by
  let D := (k+(k-r.val)-1).choose (k-r.val)
  have hD : 0 < (D:ℝ) := by exact_mod_cast (Nat.choose_pos (by omega : k-r.val ≤ k+(k-r.val)-1))
  have hC : 0 ≤ (k.choose r.val:ℝ)^2 := sq_nonneg _
  change ((_ : ℝ)/(D:ℝ))*A ≤ _
  rw [div_mul_eq_mul_div,div_le_iff₀ hD]
  push_cast; unfold Bend.weight; push_cast
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left h hC
    _ = _ := by dsimp [D];ring

/-- Exactly the four borders supply the two single-edge and two matching
completions. Every removed interior entry is nonnegative. -/
theorem border_sum {k : ℕ} (hk : 0<k) (E : CutIndex k k → CutIndex k k → ℝ)
    (hpos : ∀r t,0≤E r t)
    (hl : ∀r t,E (fullCut k) t ≤ ((k+(k-r.val)-1).choose (k-r.val):ℝ)*E r t)
    (hr : ∀r t,E r (fullCut k) ≤ ((k+(k-t.val)-1).choose (k-t.val):ℝ)*E r t) :
    lastWeight k * (E (fullCut k) (zeroCut k)+E (zeroCut k) (fullCut k)+2*E (fullCut k) (fullCut k)) ≤
      ∑ u ∈ (BalancedCorners.corners k)ᶜ, (Bend.weight k k u.1:ℝ)*(Bend.weight k k u.2:ℝ)*E u.1 u.2 := by
  let z := zeroCut k
  let f := fullCut k
  let W (u : CutIndex k k × CutIndex k k) := (Bend.weight k k u.1:ℝ)*(Bend.weight k k u.2:ℝ)*E u.1 u.2
  have ne : z≠f := fun e => hk.ne (congrArg Fin.val e)
  have dz : (Bend.weight k k z:ℝ)=1 := by simp [z,Bend.weight,zeroCut]
  have df : (Bend.weight k k f:ℝ)=1 := by simp [f,Bend.weight,fullCut]
  have pos (u) : 0 ≤ W u := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hpos _ _)
  have d : Disjoint (mid k ×ˢ ends k) (ends k ×ˢ mid k) := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    exact (Finset.mem_compl.mp (Finset.mem_product.mp hx).1) (Finset.mem_product.mp hy).1
  have sub : (mid k ×ˢ ends k) ∪ (ends k ×ˢ mid k) ⊆ (BalancedCorners.corners k)ᶜ := by
    rw [rectangle]; exact Finset.subset_union_left
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f:=W) sub (fun u _ _ => pos u)
  rw [Finset.sum_union d,Finset.sum_product,Finset.sum_product,Finset.sum_comm (s:=ends k)] at bound
  have es (g : CutIndex k k → ℝ) : ∑ i ∈ ends k, g i = g z+g f :=
    by rw [ends,Finset.sum_insert (Finset.not_mem_singleton.mpr ne),Finset.sum_singleton]
  simp_rw [es] at bound
  change lastWeight k*(E f z+E z f+2*E f f) ≤ ∑ u ∈ (BalancedCorners.corners k)ᶜ,W u
  refine le_trans ?_ bound
  rw [←middle_weight,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  change _ ≤ (W (i,z)+W (i,f))+(W (z,i)+W (f,i))
  simp only [W,dz,df,one_mul,mul_one]
  have a := complete_weight hk i _ _ (hl i z)
  have b := complete_weight hk i _ _ (hl i f)
  have c := complete_weight hk i _ _ (hr z i)
  have d' := complete_weight hk i _ _ (hr f i)
  dsimp only [z,f] at *
  linarith only [a,b,c,d']

end
end BlockPermanents.BalancedSupport
