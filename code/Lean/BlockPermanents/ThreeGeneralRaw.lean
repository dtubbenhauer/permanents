import BlockPermanents.ThreeGeneralEnds

/-! The two Schur openings and the two orders of the mixed full-cap gluing.
The upright coefficient families and marked map may have any input labels.
For the canonical three packets the upright coefficients are the two-order
packet average and the fine two-packet clasp. -/
namespace BlockPermanents.ThreeGeneralOpen
open Bend SchurNormalization
open scoped BigOperators Matrix
noncomputable section
variable {I J : Type*}

/-- Linear extension of the marked bend, including signed transfers. -/
def turn {I J : Type*} : Matrix (I×J) (I×J) ℂ →ₗ[ℂ] Matrix (I×J) (I×J) ℂ where
  toFun := partialTranspose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def properSquares {d p k : ℕ} {S : Type*} [Fintype S] (hp : k≤p)
    (M : S → Matrix (K d p) I ℂ) (N : Matrix (K d k) J ℂ) :=
  ∑ r ∈ middle p k hp, (weight p k r : ℂ) • ∑ s, Support.reflected (routed M N r s)

/-- The diagonal part of the packet clasp has two terms and the marked
interchange has four placements under the two-order ordinary average. -/
def coarse {d k : ℕ} (M : K d k → Matrix (K d k) I ℂ) (N : Matrix (K d k) J ℂ) :=
  (2:ℂ) • straight M N + (4:ℂ) • mixed (stack M) (stack M) N

/-- The original marked correction, written before bending: the fine
three-packet term, the packet subtraction, and the two straight/mixed exits
from expanding the packet average g=(I+t)/2 on each side. -/
def corrected {d k : ℕ} (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) :=
  let a : ℂ := (k+k).choose k
  let b : ℂ := (k+k+k).choose (k+k)
  let V := stackedFine P
  let U := stack M
  a • (b • opened (fun _ : Unit => P) N) - coarse M N +
    a • ((2:ℂ) • opened M N - straight (fun _ : Unit => P) N -
      (1/2:ℂ) • (mixed V U N + mixed U V N))

private theorem complete {I T : Type*} [Fintype T] (v u : Matrix T I ℂ) (a : ℕ) :
    (a:ℂ) • ((a:ℂ) • Support.reflected v) - (2:ℂ) • Support.reflected u -
       (a:ℂ) • ((1/2:ℂ) • (vᴴ*u+uᴴ*v)) =
      Support.reflected ((a:ℂ) • v - (1/2:ℂ) • u) - (9/4:ℂ) • Support.reflected u := by
  simp only [Support.reflected,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    star_natCast,star_div₀,star_one,star_ofNat,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,
    Matrix.mul_smul]
  module

theorem general_raw {d k : ℕ} (hk : 0<k)
    (hsmall : HomogeneousSchur d k k) (hbig : HomogeneousSchur d (k+k) k)
    (M : K d k → Matrix (K d k) I ℂ) (P : Matrix (K d (k+k)) I ℂ)
    (N : Matrix (K d k) J ℂ) (hM : ∀ s i, Symmetric (fun w => M s w i))
    (hP : ∀ i, Symmetric (fun w => P w i)) (hN : ∀ j, Symmetric (fun w => N w j)) :
    let a : ℂ := (k+k).choose k
    let v := terminal (stackedFine P) N
    let u := terminal (stack M) N
    partialTranspose (corrected M P N) =
      (2:ℂ) • properSquares le_rfl M N + a • properSquares (by omega) (fun _ : Unit => P) N +
      Support.reflected (a • v - (1/2:ℂ) • u) - (9/4:ℂ) • Support.reflected u := by
  dsimp only
  let a : ℂ := (k+k).choose k
  let b : ℂ := (k+k+k).choose (k+k)
  let V := fun _ : Unit => P
  let v := terminal (stackedFine P) N
  let u := terminal (stack M) N
  have e (p : ℕ) (hp : k≤p) : weight p k (lastCut p k hp) = p.choose k := by
    simp [weight,lastCut]
  have zz (p : ℕ) : weight p k (emptyCut p k) = 1 := by simp [weight,emptyCut]
  have es := schur_open hsmall M N
  rw [ends_sum hk le_rfl,zz,e,Nat.choose_self,zero_straight M N hM hN,small_terminal M N hM hN] at es
  have eb := schur_open hbig V N
  rw [ends_sum hk (by omega),zz,e,zero_straight V N (fun _ => hP) hN,big_terminal P N hP hN] at eb
  change a • partialTranspose (opened M N) = _ at es
  change b • partialTranspose (opened V N) = _ at eb
  simp only [Nat.cast_one,one_smul] at es eb
  change a • partialTranspose (opened M N) = partialTranspose (straight M N) +
    Support.reflected u + properSquares le_rfl M N at es
  change b • partialTranspose (opened V N) = partialTranspose (straight V N) +
    a • Support.reflected v + properSquares (by omega) V N at eb
  change turn (corrected M P N) = _
  simp only [corrected,coarse,map_add,map_sub,map_smul]
  change a • (b • partialTranspose (opened V N)) -
    ((2:ℂ) • partialTranspose (straight M N)+(4:ℂ) • partialTranspose (mixed (stack M) (stack M) N)) +
    a • ((2:ℂ) • partialTranspose (opened M N)-partialTranspose (straight V N)-
    (1/2:ℂ) • (partialTranspose (mixed (stackedFine P) (stack M) N)+
      partialTranspose (mixed (stack M) (stackedFine P) N))) = _
  rw [eb,smul_sub,smul_sub,smul_comm a (2:ℂ),es]
  simp only [bend_mixed]
  have hh := complete v u ((k+k).choose k)
  change a • (a • Support.reflected v) - (2:ℂ) • Support.reflected u -
    a • ((1/2:ℂ) • (vᴴ*u+uᴴ*v)) = _ at hh
  change _ = (2:ℂ) • properSquares le_rfl M N + a • properSquares _ V N +
    Support.reflected (a • v-(1/2:ℂ) • u) - (9/4:ℂ) • Support.reflected u
  rw [show ∀ (l m n o : Matrix (I×J) (I×J) ℂ), l+m+n-o=l+m+(n-o) from fun _ _ _ _ => by abel,← hh]
  dsimp [u,v,Support.reflected]
  module

end
end BlockPermanents.ThreeGeneralOpen
