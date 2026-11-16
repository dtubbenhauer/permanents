import BlockPermanents.ThreeOriginal
import BlockPermanents.ThreeWire

/-! Averaging the original corrected three-packet representative over a
simultaneous relabelling of its three physical packets. -/
namespace BlockPermanents.ThreeMarkedAverage
open Bend ThreeGeneralOpen ThreeTransfer TransferBlocks Equiv
open scoped Matrix BigOperators
noncomputable section

abbrev G := Perm (Fin 3)
def firstSwap : G := swap 0 1
def lastSwap : G := swap 1 2

def tuple (T : Type*) : (T×T)×T ≃ (Fin 3 → T) where
  toFun w := ![w.1.1,w.1.2,w.2]
  invFun w := ((w 0,w 1),w 2)
  left_inv w := rfl
  right_inv w := by funext i;fin_cases i <;> rfl

def reorder {T : Type*} (p : G) (w : (T×T)×T) :=
  (tuple T).symm ((tuple T w) ∘ p.symm)

theorem reorder_mul {T : Type*} (p q : G) (w : (T×T)×T) :
    reorder (p*q) w = reorder p (reorder q w) := by
  simp [reorder,Function.comp_def];rfl

@[simp] theorem reorder_one {T : Type*} (w : (T×T)×T) : reorder 1 w=w := by simp [reorder]

def rep (T : Type*) [Fintype T] [DecidableEq T] : G →* Matrix ((T×T)×T) ((T×T)×T) ℂ where
  toFun p := fun i j => if i = reorder p j then 1 else 0
  map_one' := by ext i j; simp [Matrix.one_apply]
  map_mul' p q := by ext i j; simp [Matrix.mul_apply,mul_ite,reorder_mul]

theorem rep_left {T I : Type*} [Fintype T] [DecidableEq T] (p : G)
    (M : Matrix ((T×T)×T) I ℂ) (i : (T×T)×T) (j : I) :
    (rep T p * M) i j=M (reorder p⁻¹ i) j := by
  have h (x) : i = reorder p x ↔ x = reorder p⁻¹ i := by
    constructor
    · rintro rfl;simp [←reorder_mul]
    · rintro rfl;simp [←reorder_mul]
  simp [rep,Matrix.mul_apply,ite_mul,h]

theorem rep_right {T I : Type*} [Fintype T] [DecidableEq T] (p : G)
    (M : Matrix I ((T×T)×T) ℂ) (i : I) (j : (T×T)×T) :
    (M * rep T p) i j=M i (reorder p j) := by simp [rep,Matrix.mul_apply,mul_ite]

theorem front (d k : ℕ) : rep (K d k) firstSwap = swapFront d k := by
  ext ⟨⟨a,b⟩,c⟩ ⟨⟨i,j⟩,m⟩
  change (if ((a,b),c)=((j,i),m) then _ else _) = (if ((b,a),c)=((i,j),m) then _ else _)
  simp [Prod.ext_iff,and_comm]
theorem back (d k : ℕ) : rep (K d k) lastSwap = ThreeTransfer.cross := rfl

theorem six (f : G → ℂ) : (∑ p, f p) =
    f 1 + f firstSwap + f lastSwap + f (firstSwap*lastSwap) + f (lastSwap*firstSwap) +
      f (firstSwap*lastSwap*firstSwap) := by
  rw [← ThreeWire.sum_permutations]
  have a : (ThreeWire.permutations 3).Perm [1,firstSwap,lastSwap,firstSwap*lastSwap,lastSwap*firstSwap,
    firstSwap*lastSwap*firstSwap] := by decide
  simpa [add_assoc] using (a.map f).sum_eq (M:=ℂ)

theorem whole_clasp (d k : ℕ) :
    Transfer.clasp (rep (K d k)) = triple (swapFront d k) ThreeTransfer.cross := by
  let ρ := rep (K d k)
  ext i j
  have h := six (fun p => ρ p i j)
  simp only [Transfer.clasp,triple,Matrix.smul_apply,Matrix.sum_apply,Matrix.add_apply,Fintype.card_perm,
    Fintype.card_fin]
  have ha := congrArg (fun x : Matrix (ThreeWords d k) (ThreeWords d k) ℂ => x i j) (ρ.map_one)
  simp only [← front d k,←back d k,← map_mul]
  change ((↑(Nat.factorial 3):ℚ)⁻¹ • _) = (1/6:ℚ) • _
  norm_num only [show (3:ℕ).factorial=6 by decide,Nat.cast_ofNat]
  simpa only [ρ,map_one] using congrArg ((1/6:ℚ) • ·) h

theorem shifted (d k : ℕ) :
    let u := swapFront d k
    let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
    (u*t*u)*firstFine d k*(u*t*u)=secondFine d k := by
  dsimp only
  let P := firstFine d k
  let u := swapFront d k
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  have up := first_front d k
  have pu : P*u=P := by simpa only [Matrix.conjTranspose_mul,front_star,fine_star] using congrArg Matrix.conjTranspose up
  change (u*t*u)*P*(u*t*u)=_
  calc
    _ = (u*t)*(u*P*u)*(t*u) := by simp only [mul_assoc]
    _ = (u*t)*P*(t*u) := by rw [show u*P=P from up,pu]
    _ = _ := by
      rw [show u = rep (K d k) firstSwap from (front d k).symm,
        show t=rep (K d k) lastSwap from (back d k).symm, ←map_mul,←map_mul]
      ext i j
      rw [rep_right,rep_left]
      rfl

private theorem kill_right {R G : Type*} [Ring R] [Group G] [Fintype G] [Algebra ℚ R]
    (ρ : G →* R) (A J : R) (h : J*Transfer.clasp ρ=0) :
    Transfer.bracket ρ (Transfer.clasp ρ*A*J) = 0 := by
  let F := Transfer.clasp ρ
  have one (p : G) : ρ p * (F*A*J) * ρ p⁻¹ = (F*A)*(J*ρ p⁻¹) := by
    rw [← mul_assoc,← mul_assoc (ρ p),Transfer.absorb_left]
    simp only [F,mul_assoc]
  change ((Fintype.card G:ℚ)⁻¹) • ∑ p, ρ p*(F*A*J)*ρ p⁻¹=0
  simp_rw [one]
  rw [← Finset.mul_sum,← Finset.mul_sum,← mul_smul_comm,← mul_smul_comm]
  have inv := Equiv.sum_comp (Equiv.inv G) ρ
  change (∑ p : G, ρ p⁻¹) = _ at inv; rw [inv];change F*A*(J*Transfer.clasp ρ)=0;rw [h,mul_zero]

private theorem kill_left {R G : Type*} [Ring R] [Group G] [Fintype G] [Algebra ℚ R]
    (ρ : G →* R) (A J : R) (h : Transfer.clasp ρ*J=0) :
    Transfer.bracket ρ (J*A*Transfer.clasp ρ) = 0 := by
  let F := Transfer.clasp ρ
  have one (p : G) : ρ p * (J*A*F) * ρ p⁻¹ = ((ρ p*J)*A)*F := by
    rw [mul_assoc, mul_assoc (J*A),Transfer.absorb_right]
    simp only [F,mul_assoc]
  change ((Fintype.card G:ℚ)⁻¹) • ∑ p, ρ p*(J*A*F)*ρ p⁻¹=0
  simp_rw [one]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul,← smul_mul_assoc,← smul_mul_assoc,← smul_mul_assoc]
  change Transfer.clasp ρ*J*A*F=0
  rw [h,zero_mul,zero_mul]

/-- Averaging both ends kills the full/off-diagonal correction. -/
theorem average_correction (d k : ℕ) :
    let u := swapFront d k
    let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
    let p := firstFine d k
    Transfer.bracket (rep (K d k)) (movedDifference u t p) = 0 := by
  dsimp only
  let u := swapFront d k
  let t : Matrix (ThreeWords d k) (ThreeWords d k) ℂ := ThreeTransfer.cross
  let F := triple u t
  let J := other u t
  have L : F*J=0 := by
    change F*(pair u-F)=0
    rw [mul_sub,show F*pair u=F from triple_pair u t (front_sq d k)]
    change triple (swapFront d k) cross-triple (swapFront d k) cross*triple (swapFront d k) cross=0
    rw [←whole_clasp,Transfer.clasp_sq,sub_self]
  have R : J*F=0 := by
    change (pair u-F)*F=0
    rw [sub_mul,show pair u*F=F from pair_triple u t (front_sq d k)]
    change triple (swapFront d k) cross-triple (swapFront d k) cross*triple (swapFront d k) cross=0
    rw [←whole_clasp,Transfer.clasp_sq,sub_self]
  rw [movedDifference_eq _ _ _ (front_sq d k) (first_pair d k) (pair_first d k),
    correction_mixed _ _ _ (front_sq d k) (first_pair d k) (pair_first d k),map_smul,map_add]
  change _ • (Transfer.bracket _ (F*firstFine d k*J) + Transfer.bracket _ (J*firstFine d k*F)) = _
  rw [show F=Transfer.clasp (rep (K d k)) from (whole_clasp d k).symm]
  rw [show F=Transfer.clasp (rep (K d k)) from (whole_clasp d k).symm] at L R
  rw [kill_right _ _ _ R,kill_left _ _ _ L,add_zero,smul_zero]

end
end BlockPermanents.ThreeMarkedAverage
