import BlockPermanents.FourThickOpenings

/-! # The original four-packet transfer opened at arbitrary thickness -/
namespace BlockPermanents.FourThickOpenings
open FourTarget FourThickSlots FourThickCompression FourThickJoint FourWireAlgebra
open FourLocalCompression (absorb_conjugate)
open TransferBlocks SchurNormalization Bend
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 750000
attribute [local irreducible] FourTarget.localClasp FourTarget.fineClasp FourTarget.packets FourThickCompression.W FourThickOpenings.proper

def a (k : ℕ) : ℚ := (k+k).choose k
def b (k : ℕ) : ℚ := (3*k).choose k
def scale (n k : ℕ) : ℚ := ((n*k).factorial : ℚ) / k.factorial^n

theorem scale_next (n k : ℕ) : scale (n+1) k = scale n k * ((n*k+k).choose (n*k) : ℚ) := by
  have hf : (((n*k+k).choose (n*k) : ℕ) : ℚ) * (n*k).factorial * k.factorial = (n*k+k).factorial :=
    by rw [Nat.choose_symm_add]; exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial (n*k) k
  have h : (k.factorial:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  unfold scale
  rw [Nat.succ_mul,pow_succ]
  field_simp
  linear_combination hf * -(k.factorial:ℚ)^n

theorem two_scale (k : ℕ) : scale 2 k = a k := by
  rw [show 2=1+1 by rfl,scale_next]
  simp [scale,a,Nat.factorial_ne_zero]

theorem three_choose (k : ℕ) : (2*k+k).choose (2*k) = (3*k).choose k := by
  rw [Nat.choose_symm_add]
  congr 1; omega

theorem three_scale (k : ℕ) : scale 3 k = a k*b k := by
  rw [show 3=2+1 by rfl,scale_next,two_scale,three_choose,b]

def U (d k : ℕ) := sand (ordinary (packets d k)) (proper d k 1 (by decide))
def W₂ (d k : ℕ) := sand (ordinary (packets d k)) (proper d k 2 (by decide))
def V (d k : ℕ) := proper d k 3 (by decide)

theorem opened {d k : ℕ} (hk : 0<k) (h₁ : HomogeneousSchur d (1*k) k)
    (h₂ : HomogeneousSchur d (2*k) k) (h₃ : HomogeneousSchur d (3*k) k) :
    FourSymbolic.Opened (sand (W d k)) (packets d k) (localClasp d k 2) (localClasp d k 3)
      (fineClasp d k) (U d k) (W₂ d k) (V d k) (a k) (b k) (scale 3 k) (scale 4 k) := by
  let F := ordinary (packets d k)
  let C := sand (W d k)
  have op (n : ℕ) (hn : n≤3) (h0 : 0<n) (h : HomogeneousSchur d (n*k) k) :=
    opened_local hk hn h0 h (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right k h0)
      (exchange_zero k n hn) (exchange_full k n hn h0)
  have ff : F*F=F := by
    apply triple_idem
    · rw [← map_mul,show swap12*swap12=1 by decide,map_one]
    · rw [← map_mul,show swap23*swap23=1 by decide,map_one]
    · simp only [← map_mul]; congr 1; decide
  have wf : W d k*F=F*W d k := W_comm_triple d k
  have fx : sand F (sand (packets d k swap12) (joint d k 1)) = sand F (joint d k 1) :=
    absorb_conjugate _ _ _ _ (triple_right _ _ (by rw [←map_mul,show swap12*swap12=1 by decide,map_one]))
      (triple_left _ _ (by rw [←map_mul,show swap12*swap12=1 by decide,map_one])) rfl
  constructor
  · have step := op 3 (by decide) (by decide) h₃
    rw [joint_three] at step
    have eq := congrArg (fun x => scale 3 k • x) step
    rw [show scale 4 k = _ from scale_next 3 k]
    simp only [V,b,map_add,map_smul,smul_add,smul_smul] at eq ⊢
    exact eq
  · have step := surround (F:=F) (op 2 (by decide) (by decide) h₂) wf
    rw [←joint_two] at step
    have eq := congrArg (fun x => a k • x) step
    rw [three_scale]
    simp only [W₂,three_choose,show (2*k).choose k = (k+k).choose k by rw [two_mul],
      a,b,F,map_smul,map_add,smul_add,smul_smul,pow_two] at eq ⊢
    have exp (P t : Op d k) : sand (ordinary (packets d k)) (P*t*P) =
        ordinary (packets d k)*P*t*P*ordinary (packets d k) := by
      change _ * (P*t*P) * _ = _; simp only [mul_assoc]
    simpa only [exp] using eq
  · have step := op 1 (by decide) (by decide) h₁
    have step' : C (a k • joint d k 1) =
        C (1+proper d k 1 (by decide)+packets d k swap14) := by
      simpa only [C,a,one_mul,Nat.choose_self,Nat.cast_one,one_smul,map_add,
        first_compress,compressed_identity] using step
    have eq := surround (F:=F) step' wf
    have id : sand F (1 : Op d k)=F := by change F*1*F=F; rw [mul_one,ff]
    rw [joint_one,fx]
    simpa only [U,map_smul,map_add,id] using eq

/-- The original marked transfer, compressed on independently symmetric packets,
equals the sum of its three proper-cut families and four full-cut terms. -/
theorem actual_open {d k : ℕ} (hk : 0<k) (h₁ : HomogeneousSchur d (1*k) k)
    (h₂ : HomogeneousSchur d (2*k) k) (h₃ : HomogeneousSchur d (3*k) k) :
    sand (W d k) (Q d k) = sand (W d k)
      (FourSymbolic.raw (ordinary (packets d k)) (localClasp d k 3) (localClasp d k 2)
        (movedPair (packets d k) (localClasp d k 2)) (U d k) (W₂ d k) (V d k)
        (packets d k swap14) (a k) (b k) (scale 3 k)) := by
  have hb : b k ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  unfold Q X₃ X₄
  exact FourSymbolic.opened_transfer _ _ _ _ _ _ _ _ _ _ _ _ hb (three_scale k)
    (FourActualAlgebra.fine_clasps d k) (opened hk h₁ h₂ h₃)

end
end BlockPermanents.FourThickOpenings
