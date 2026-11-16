import BlockPermanents.BalancedPairTrace
import BlockPermanents.BalancedRoutes

/-! The three extreme contractions of the two crossing paired edges. -/
namespace BlockPermanents.BalancedExtremes
open Bend BalancedOpen BalancedPairTrace BalancedTrace BalancedRoutes
noncomputable section

def E {d k} (flip : Bool) (z : Boundary (Word d k) → ℂ) (r t : CutIndex k k) :=
  energy ((productCap flip d k r t).mulVec z)

private theorem empty_join {d k} (a : Word d (k-(zeroCut k).val)) (x : Word d (zeroCut k).val) :
    join (PairBound.cut_le (zeroCut k)) a x = a := by
  funext i
  simp only [BalancedTrace.join,zeroCut,Fin.append_right_nil _ _ rfl,Function.comp_def,Fin.cast_refl,Equiv.refl_apply] <;> rfl

private theorem full_join {d k} (a : Word d (k-(fullCut k).val)) (x : Word d (fullCut k).val) :
    join (PairBound.cut_le (fullCut k)) a x = x := by
  funext i
  simp only [BalancedTrace.join,fullCut,Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def,Fin.cast_refl,Equiv.refl_apply] <;> rfl

private instance {d k} : Unique (Word d (k-(fullCut k).val)) := by
  simp only [fullCut,Nat.sub_self]; infer_instance

theorem first {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (h : Supported U V z) :
    E flip z (fullCut k) (zeroCut k) = energy (if flip then L01 z else L00 z) := by
  have hr := raw_product flip h (fullCut k) (zeroCut k)
  unfold E energy
  simp only [Fintype.sum_prod_type,hr,empty_join,full_join,Finset.sum_const,Finset.card_univ,
    Fintype.card_unique,one_smul]
  simp only [Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,zeroCut,fullCut,Nat.sub_self,pow_zero,mul_one,one_smul]
  cases flip <;> rfl

theorem second {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (h : Supported U V z) :
    E flip z (zeroCut k) (fullCut k) = energy (if flip then L10 z else L11 z) := by
  have hr := raw_product flip h (zeroCut k) (fullCut k)
  unfold E energy
  simp only [Fintype.sum_prod_type,hr,empty_join,full_join,Finset.sum_const,Finset.card_univ,
    Fintype.card_unique,one_smul]
  simp only [Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,zeroCut,fullCut,Nat.sub_self,pow_zero,mul_one,one_smul]
  cases flip <;> rfl

theorem full {d k} (flip : Bool) {U V} {z : Boundary (Word d k) → ℂ} (h : Supported U V z) :
    E flip z (fullCut k) (fullCut k) = Complex.normSq (if flip then Ncross z else Ndirect z) := by
  have hr := raw_product flip h (fullCut k) (fullCut k)
  unfold E energy
  simp only [Fintype.sum_prod_type,hr,full_join,Finset.sum_const,Finset.card_univ,
    Fintype.card_unique,one_smul]
  simp only [Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,zeroCut,fullCut,Nat.sub_self,pow_zero,mul_one,one_smul]
  cases flip <;> rfl

end
end BlockPermanents.BalancedExtremes
