import BlockPermanents.FourNativeFull
import BlockPermanents.FourNativeSurvivor

/-! # The four full-cap contributions in equation (5C.3) -/
namespace BlockPermanents.FourNative
open Bend FourTarget FourRoutes FourExchangeKernel FourWireAlgebra FourAdjoints
open ThreeTransfer FourNativeCap FourThickOpenings TransferBlocks
open scoped Matrix BigOperators
noncomputable section

variable {I J : Type*} {d k : ℕ}

private def uprightPart (A : Op d k) (h : A ∈ ordinaryAlgebra d k) : Matrix (Triple d k) (Triple d k) ℂ :=
  Classical.choose (getUpright h)

private theorem part_spec (A : Op d k) (h : A ∈ ordinaryAlgebra d k) :
    matrix d k A = upright (uprightPart A h) :=
  Classical.choose_spec (getUpright h)

private def Fmat (d k : ℕ) := uprightPart _ (average_ordinary d k)
private def Pmat (d k : ℕ) := uprightPart _ (local_ordinary d k 2 (by decide))
private def Emat (d k : ℕ) := uprightPart _ (local_ordinary d k 3 (by decide))

/-- The three full-cap halves LF, LPF and LE on a pair of rectangular feet. -/
def terminalU (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :=
  half (Fmat d k*M) N

def terminalW (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :=
  half ((Pmat d k*Fmat d k)*M) N

def terminalV (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :=
  half (Emat d k*M) N

/-- With all outputs ordered as packets 2 and 3, the final clasp is the actual fine 2k-clasp. -/
def terminalSquares (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :=
  let u := terminalU M N
  let w := terminalW M N
  let v := terminalV M N
  let pu := totalClasp d k k * u
  let z := v - (b k)⁻¹ • pu
  (scale 3 k*b k) • (zᴴ*z) + (3*(a k)^2) • (wᴴ*w) - (12:ℚ) • (uᴴ*u) - (4*a k) • (puᴴ*pu)

private theorem upright_mul {A B C K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (P : Matrix A B ℂ) (Q : Matrix B C ℂ) :
    upright (K:=K) P * upright Q = upright (P*Q) := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [upright,Matrix.mul_apply,Fintype.sum_prod_type,mul_ite,ite_mul,h]

private theorem upright_diff {A B K : Type*} [DecidableEq K] (P Q : Matrix A B ℂ) (c : ℚ) :
    upright (K:=K) P - c • upright Q = upright (P - c • Q) := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [upright,h]

/-- The native opened transfer has exactly the full-cap terms of (5C.3). -/
theorem read_raw [Fintype I] (M : Matrix (Triple d k) I ℂ) (N : Matrix (Word d k) J ℂ) :
    read M N (FourSymbolic.raw (ordinary (packets d k)) (localClasp d k 3) (localClasp d k 2)
      (movedPair (packets d k) (localClasp d k 2)) (U d k) (W₂ d k) (V d k)
      (packets d k swap14) (a k) (b k) (scale 3 k)) =
      (6:ℚ) • read M N (U d k) + (3*a k) • read M N (W₂ d k) + scale 3 k • read M N (V d k) +
      terminalSquares M N := by
  let F := ordinary (packets d k)
  let P := localClasp d k 2
  let E := localClasp d k 3
  let R := movedPair (packets d k) P
  let t := packets d k swap14
  let p := totalClasp d k k
  have hF : matrix d k F = upright (Fmat d k) := part_spec _ _
  have hP : matrix d k P = upright (Pmat d k) := part_spec _ _
  have hE : matrix d k E = upright (Emat d k) := part_spec _ _
  have hR : matrix d k R = upright (survivor p) := FourNativeSurvivor.matrix_moved d k
  have hPF : matrix d k (P*F) = upright (Pmat d k*Fmat d k) := by rw [map_mul,hP,hF,upright_mul]
  have hRF : matrix d k (R*F) = upright (survivor p*Fmat d k) := by rw [map_mul,hR,hF,upright_mul]
  let Z := Emat d k - (b k)⁻¹ • (survivor p*Fmat d k)
  have hZ : matrix d k (E-(b k)⁻¹ • (R*F)) = upright Z := by rw [map_sub,map_smul,hE,hRF,upright_diff]
  have f : Reflected F F := ordinary_self _ _
  have q : Reflected P P := local_self _ _ _
  have e : Reflected E E := local_self _ _ _
  have r : Reflected R R := moved_self _ _
  have pull : half ((survivor p*Fmat d k)*M) N = p*terminalU M N := by
    rw [Matrix.mul_assoc,half_survivor]; rfl
  have corr : half (Z*M) N = terminalV M N - (b k)⁻¹ • (p*terminalU M N) := by
    dsimp only [Z]; rw [Matrix.sub_mul,Matrix.smul_mul,half_sub_smul,pull]; rfl
  have hu := read_full M N f hF
  have hw := read_full M N (q.mul f) hPF
  have hp := read_full M N (r.mul f) hRF
  have hz := read_full M N (e.sub (Reflected.scale _ (r.mul f))) hZ
  change read M N (FourSymbolic.raw F E P R (U d k) (W₂ d k) (V d k) t (a k) (b k) (scale 3 k)) = _
  dsimp only [FourSymbolic.raw]
  simp only [map_add,map_sub,map_smul]
  change _ + (scale 3 k*b k) • read M N ((E-(b k)⁻¹ • (F*R))*t*(E-(b k)⁻¹ • (R*F))) +
    (3*(a k)^2) • read M N (F*P*t*P*F) - (12:ℚ) • read M N (F*t*F) -
    (4*a k) • read M N (F*R*t*R*F) = _
  rw [mul_assoc (F*P*t) P F, mul_assoc (F*R*t) R F]
  rw [hz,hw,hu,hp,pull,corr]
  dsimp only [terminalSquares,terminalU,terminalW,terminalV,p]
  abel

end
end BlockPermanents.FourNative
