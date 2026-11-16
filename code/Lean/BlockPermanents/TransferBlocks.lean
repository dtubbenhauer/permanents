import BlockPermanents.Transfer
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Module

/-!
# The two blocks in the second packet transfer

Used in Section 5B (lem: moving the mark to packet four). The adjacent
interchanges `u=(12)` and `v=(23)` act in any rational algebra, including
the endomorphisms of tensor powers over the complex numbers.
-/

namespace BlockPermanents.TransferBlocks

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- The average over the two orders of a pair. -/
def pair (u : R) : R := (1/2 : ℚ) • (1+u)

/-- The average over the six orders of the first three packets. -/
def triple (u v : R) : R := (1/6 : ℚ) • (1+u+v+u*v+v*u+u*v*u)

/-- The complementary block of the pair projector. -/
def other (u v : R) : R := pair u - triple u v

theorem pair_idem (u : R) (hu : u*u=1) : pair u * pair u = pair u := by
  simp only [pair, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hu]
  module

theorem pair_right (u : R) (hu : u*u=1) : pair u * u = pair u := by
  simp only [pair, smul_mul_assoc, add_mul, one_mul, hu]
  module

theorem pair_left (u : R) (hu : u*u=1) : u * pair u = pair u := by
  simp only [pair, mul_smul_comm, mul_add, mul_one, hu]
  module

theorem triple_flip (u v : R) (braid : u*v*u=v*u*v) :
    triple u v = triple v u := by
  unfold triple
  rw [braid]
  module

theorem triple_left (u v : R) (hu : u*u=1) : u * triple u v = triple u v := by
  simp only [triple, mul_smul_comm, mul_add, mul_one, ← mul_assoc, hu, one_mul]
  module

theorem triple_right (u v : R) (hu : u*u=1) : triple u v * u = triple u v := by
  simp only [triple, smul_mul_assoc, add_mul, one_mul, mul_assoc, hu, mul_one]
  module

theorem triple_idem (u v : R) (hu : u*u=1) (hv : v*v=1) (braid : u*v*u=v*u*v) :
    triple u v * triple u v = triple u v := by
  have h1 := triple_right u v hu
  have h2 : triple u v * v = triple u v := by rw [triple_flip u v braid, triple_right _ _ hv]
  let f := triple u v
  change f * ((1/6 : ℚ) • (1+u+v+u*v+v*u+u*v*u)) = f
  change f * u = f at h1
  change f * v = f at h2
  simp only [mul_smul_comm, mul_add, mul_one, ← mul_assoc, h1, h2]
  module

theorem pair_triple (u v : R) (hu : u*u=1) :
    pair u * triple u v = triple u v := by
  simp only [pair, smul_mul_assoc, add_mul, one_mul, triple_left _ _ hu]
  module

theorem triple_pair (u v : R) (hu : u*u=1) :
    triple u v * pair u = triple u v := by
  simp only [pair, mul_smul_comm, mul_add, mul_one, triple_right _ _ hu]
  module

/-- The three exits give `A=F-J/2`. -/
theorem sandwiched_crossing (u v : R) :
    pair u * v * pair u = triple u v - (1/2 : ℚ) • other u v := by
  simp only [pair, triple, other, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    one_mul, mul_one]
  module

/-- Averaging the identity and the sandwiched crossing gives `D=F+J/4`. -/
theorem sandwiched_average (u v : R) (hu : u*u=1) :
    pair u * pair v * pair u = triple u v + (1/4 : ℚ) • other u v := by
  calc
    _ = (1/2 : ℚ) • (pair u * pair u + pair u * v * pair u) := by
      unfold pair
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_one, one_mul]
      module
    _ = _ := by
      rw [pair_idem u hu, sandwiched_crossing]
      unfold other
      module

/-- The correction `2APA-PD-DP`, with A and D given by the actual
sandwiched permutation operators. -/
def correction (u v P : R) : R :=
  (2 : ℚ) • ((pair u * v * pair u) * P * (pair u * v * pair u)) -
  P * (pair u * pair v * pair u) - (pair u * pair v * pair u) * P

/-- The numerical coefficient of each of the two mixed blocks is `-9/4`.
Only absorption by the two-packet projector is required of P. -/
theorem correction_mixed (u v P : R) (hu : u*u=1)
    (hl : pair u * P = P) (hr : P * pair u = P) :
    correction u v P = (-9/4 : ℚ) •
      (triple u v * P * other u v + other u v * P * triple u v) := by
  let F := triple u v
  let J := other u v
  have h : F+J = pair u := by
    change triple u v + (pair u - triple u v) = pair u
    module
  have hL : (F+J)*P = P := h ▸ hl
  have hR : P*(F+J) = P := h ▸ hr
  unfold correction
  rw [sandwiched_crossing, sandwiched_average u v hu]
  change (2 : ℚ) • ((F - (1/2 : ℚ) • J)*P*(F - (1/2 : ℚ) • J)) -
    P*(F + (1/4 : ℚ) • J) - (F + (1/4 : ℚ) • J)*P =
    (-9/4 : ℚ) • (F*P*J+J*P*F)
  calc
    _ = (2 : ℚ) • ((F - (1/2 : ℚ) • J)*P*(F - (1/2 : ℚ) • J)) -
      ((F+J)*P)*(F + (1/4 : ℚ) • J) - (F + (1/4 : ℚ) • J)*(P*(F+J)) := by rw [hL,hR]
    _ = _ := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]
      module

/-- The three-packet correction in its original moving-mark form:
P is moved from 12 to 23 by the interchange (13) = u v u. -/
def movedDifference (u v P : R) : R :=
  (2 : ℚ) • (pair u * (u*v*u) * P * (u*v*u) * pair u) -
    P * pair v * pair u - pair u * pair v * P

theorem movedDifference_eq (u v P : R) (hu : u*u=1)
    (hl : pair u * P = P) (hr : P * pair u = P) :
    movedDifference u v P = correction u v P := by
  let H := pair u
  change H * P = P at hl
  change P * H = P at hr
  have ul : u*H=H := pair_left _ hu
  have ur : H*u=H := pair_right _ hu
  have up : u*P=P := by
    calc
      _ = u*(H*P) := by rw [hl]
      _ = (u*H)*P := (mul_assoc ..).symm
      _ = _ := by rw [ul,hl]
  have pu : P*u=P := by
    calc
      _ = (P*H)*u := by rw [hr]
      _ = P*(H*u) := mul_assoc ..
      _ = _ := by rw [ur,hr]
  have leftTurn : H*(u*v*u)*P = H*v*P := by
    calc
      _ = (H*u)*v*(u*P) := by simp only [mul_assoc]
      _ = _ := by rw [ur,up]
  have rightTurn : P*(u*v*u)*H = P*v*H := by
    calc
      _ = (P*u)*v*(u*H) := by simp only [mul_assoc]
      _ = _ := by rw [pu,ul]
  have middle : H*(u*v*u)*P*(u*v*u)*H = (H*v*H)*P*(H*v*H) := by
    rw [leftTurn]
    calc
      _ = H*v*(P*(u*v*u)*H) := by simp only [mul_assoc]
      _ = H*v*(H*P*H)*v*H := by rw [rightTurn,hl,hr]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have leftTerm : P*(H*pair v*H) = P*pair v*H := by rw [← mul_assoc, ← mul_assoc, hr]
  have rightTerm : (H*pair v*H)*P = H*pair v*P := by rw [mul_assoc (H*pair v),hl]
  unfold movedDifference correction
  rw [middle,leftTerm,rightTerm]

/-- The full operator B in the paper's second transfer. -/
def corrected (a : ℚ) (u v P X : R) : R := X + a • movedDifference u v P

/-- With C=2B-X, the paper uses FC+CF=2B to cancel its crossed exits.
The hypotheses give the permutation relations, the pair support of P,
and the three-packet support of X. The numerical identity is derived. -/
theorem crossed_exits (a : ℚ) (u v P X : R)
    (hu : u*u=1) (hv : v*v=1) (braid : u*v*u=v*u*v)
    (hP₁ : pair u*P=P) (hP₂ : P*pair u=P)
    (hX₁ : triple u v * X = X) (hX₂ : X * triple u v = X) :
    let F := triple u v
    let B := corrected a u v P X
    let C := (2 : ℚ) • B - X
    F*C+C*F = (2 : ℚ) • B := by
  let F := triple u v
  let J := other u v
  have hFF : F*F=F := triple_idem _ _ hu hv braid
  have hFJ : F*J=0 := by
    change triple u v * (pair u - triple u v) = 0
    rw [mul_sub, triple_pair _ _ hu, triple_idem _ _ hu hv braid, sub_self]
  have hJF : J*F=0 := by
    change (pair u - triple u v) * triple u v = 0
    rw [sub_mul, pair_triple _ _ hu, triple_idem _ _ hu hv braid, sub_self]
  let M := F*P*J + J*P*F
  have hFL : F*M = F*P*J := by
    dsimp only [M]
    simp only [mul_add, ← mul_assoc, hFF, hFJ, zero_mul, add_zero]
  have hFR : M*F = J*P*F := by
    dsimp only [M]
    simp only [add_mul, mul_assoc, hJF, hFF, mul_zero, zero_add]
  have hB : corrected a u v P X = X + a • ((-9/4 : ℚ) • M) := by
    rw [corrected, movedDifference_eq _ _ _ hu hP₁ hP₂, correction_mixed _ _ _ hu hP₁ hP₂]
  change F*((2 : ℚ) • corrected a u v P X-X)+((2 : ℚ) • corrected a u v P X-X)*F =
    (2 : ℚ) • corrected a u v P X
  rw [hB]
  change F * X = X at hX₁
  change X * F = X at hX₂
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    hFL, hFR, hX₁, hX₂]
  dsimp only [M]
  module

/-- An operator that can pass around the simultaneous permutation average. -/
private def Slides (T : R →ₗ[ℚ] R) (A : R) : Prop := ∀ y, T (A*y) = T (y*A)

private theorem slides_add {T : R →ₗ[ℚ] R} {A B : R} (hA : Slides T A) (hB : Slides T B) :
    Slides T (A+B) := by intro y; simp [add_mul,mul_add,hA y,hB y]

private theorem slides_sub {T : R →ₗ[ℚ] R} {A B : R} (hA : Slides T A) (hB : Slides T B) :
    Slides T (A-B) := by intro y; simp [sub_mul,mul_sub,hA y,hB y]

private theorem slides_mul {T : R →ₗ[ℚ] R} {A B : R} (hA : Slides T A) (hB : Slides T B) :
    Slides T (A*B) := by
  intro y
  rw [mul_assoc, hA, mul_assoc, hB, mul_assoc]

private theorem slides_smul {T : R →ₗ[ℚ] R} {A : R} (hA : Slides T A) (a : ℚ) :
    Slides T (a • A) := by intro y; simp [smul_mul_assoc,mul_smul_comm,hA y]

private theorem slides_one (T : R →ₗ[ℚ] R) : Slides T 1 := by intro y; rw [one_mul,mul_one]

private theorem slides_pair {T : R →ₗ[ℚ] R} {u : R} (hu : Slides T u) : Slides T (pair u) :=
  slides_smul (slides_add (slides_one _) hu) _

private theorem slides_triple {T : R →ₗ[ℚ] R} {u v : R} (hu : Slides T u) (hv : Slides T v) :
    Slides T (triple u v) :=
  slides_smul (slides_add (slides_add (slides_add (slides_add (slides_add (slides_one _) hu) hv)
    (slides_mul hu hv)) (slides_mul hv hu)) (slides_mul (slides_mul hu hv) hu)) _

private theorem squeeze {T : R →ₗ[ℚ] R} {F : R} (hf : Slides T F) (hsq : F*F=F) (Y : R) :
    T (F*Y*F) = T (Y*F) := by rw [mul_assoc, hf, mul_assoc, hsq]

/-- Opening the three exits after relabeling 3 and 4. The two non-straight
exits are u-conjugate; we keep them apart until taking the average. -/
theorem three_exits (u b : R) (hu : u*u=1) :
    (3 : ℚ) • triple u b = pair u + b*pair u + (u*b*u)*pair u := by
  unfold pair triple
  simp only [mul_smul_comm, mul_add, mul_one, mul_assoc, hu]
  module

theorem conjugate_triple (w u v : R) (hw : w*w=1) (uw : w*u*w=u) :
    w*triple u v*w = triple u (w*v*w) := by
  have prod (x y : R) : w*(x*y)*w = (w*x*w)*(w*y*w) := by
    calc
      _ = w*x*(w*w)*y*w := by rw [hw,mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  unfold triple
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, hw, uw, prod]

/-- The averaged three-packet term on four upright cables. The two sides of B
are absorbed by (12); the third ordinary packet is still distinguished. -/
private theorem averaged_move {T : R →ₗ[ℚ] R} (u v w B : R)
    (hu : u*u=1) (hv : v*v=1) (hw : w*w=1) (braid : u*v*u=v*u*v) (uw : w*u*w=u)
    (su : Slides T u) (sv : Slides T v) (sw : Slides T w)
    (bl : u*B=B) (br : B*u=B) :
    let F := triple u v
    let t := u*(w*v*w)*u
    (3 : ℚ) • T (F*(w*B*w)*F) = T B + (2 : ℚ) • T (B*t) := by
  let F := triple u v
  let b := w*v*w
  let t := u*b*u
  have hF : Slides T F := slides_triple su sv
  have hH : Slides T (pair u) := slides_pair su
  have HB : pair u * B = B := by simp only [pair,smul_mul_assoc,add_mul,one_mul,bl]; module
  have BH : B * pair u = B := by simp only [pair,mul_smul_comm,mul_add,mul_one,br]; module
  have exitTerm (e : R) : T (B*(e*pair u)) = T (B*e) := by
    rw [← mul_assoc, ← hH, ← mul_assoc, HB]
  have identify : T (B*t) = T (B*b) := by
    change T (B*(u*b*u)) = T (B*b)
    rw [← mul_assoc, ← mul_assoc,br, ← su, ← mul_assoc,bl]
  change (3 : ℚ) • T (F*(w*B*w)*F) = T B + (2 : ℚ) • T (B*t)
  rw [squeeze hF (triple_idem u v hu hv braid)]
  have relabel : T ((w*B*w)*F) = T (B*(w*F*w)) := by
    rw [mul_assoc w B w, mul_assoc, sw]; simp only [mul_assoc]
  rw [relabel, ← map_smul, conjugate_triple w u v hw uw]
  calc
    _ = T (B*((3 : ℚ) • triple u b)) := by rw [mul_smul_comm]
    _ = T B + T (B*b) + T (B*t) := by
      rw [three_exits _ _ hu, mul_add, mul_add, map_add, map_add, BH, exitTerm, exitTerm]
    _ = _ := by rw [← identify]; module

/-- The operator Q in (eq:fourQ). -/
def fourOperator (a : ℚ) (u v w t P X₃ X₄ : R) : R :=
  let F := triple u v
  let B := corrected a u v P X₃
  let C := (2 : ℚ) • B - X₃
  X₄-X₃ + (3 : ℚ) • (F*(w*B*w)*F) - F*(C*t+t*C)*F

abbrev FourPerm := Equiv.Perm (Fin 4)
def swap12 : FourPerm := Equiv.swap 0 1
def swap23 : FourPerm := Equiv.swap 1 2
def swap34 : FourPerm := Equiv.swap 2 3
def swap14 : FourPerm := Equiv.swap 0 3

/-- Equation (fourQ), simultaneous-average part. Packet permutations act
through any representation of the actual symmetric group on four letters.
P is supported on the 12 pair, X₃ on the triple. -/
theorem four_average (ρ : FourPerm →* R) (a : ℚ) (P X₃ X₄ : R)
    (pL : pair (ρ swap12) * P = P) (pR : P * pair (ρ swap12) = P)
    (xL : triple (ρ swap12) (ρ swap23) * X₃ = X₃)
    (xR : X₃ * triple (ρ swap12) (ρ swap23) = X₃)
    (invariant : Transfer.bracket ρ X₄ = X₄) :
    Transfer.bracket ρ (fourOperator a (ρ swap12) (ρ swap23) (ρ swap34) (ρ swap14) P X₃ X₄) =
      X₄ := by
  let T := Transfer.bracket ρ
  let u := ρ swap12
  let v := ρ swap23
  let w := ρ swap34
  let t := ρ swap14
  let F := triple u v
  let J := other u v
  let B := corrected a u v P X₃
  let C := (2 : ℚ) • B-X₃
  have hu : u*u=1 := by dsimp [u]; rw [← map_mul, show swap12*swap12=1 by decide, map_one]
  have hv : v*v=1 := by dsimp [v]; rw [← map_mul, show swap23*swap23=1 by decide, map_one]
  have hw : w*w=1 := by dsimp [w]; rw [← map_mul, show swap34*swap34=1 by decide, map_one]
  have braid : u*v*u=v*u*v := by
    dsimp [u,v]; simp only [← map_mul]; apply congrArg; decide
  have uw : w*u*w=u := by
    dsimp [w,u]; simp only [← map_mul]; apply congrArg; decide
  have t_eq : t = u*(w*v*w)*u := by
    dsimp [t,u,v,w]; simp only [← map_mul]; apply congrArg; decide
  have su : Slides T u := Transfer.slide _ _
  have sv : Slides T v := Transfer.slide _ _
  have sw : Slides T w := Transfer.slide _ _
  have st : Slides T t := Transfer.slide _ _
  have sF : Slides T F := slides_triple su sv
  have sJ : Slides T J := slides_sub (slides_pair su) sF
  have ff : F*F=F := triple_idem _ _ hu hv braid
  have fj : F*J=0 := by
    change F*(pair u - F)=0
    rw [mul_sub, show F*pair u=F from triple_pair _ _ hu, ff, sub_self]
  have jf : J*F=0 := by
    change (pair u - F)*F=0
    rw [sub_mul, show pair u*F=F from pair_triple _ _ hu, ff, sub_self]
  have uf : u*F=F := triple_left _ _ hu
  have fu : F*u=F := triple_right _ _ hu
  have uj : u*J=J := by change u*(pair u-F)=pair u-F; rw [mul_sub,pair_left _ hu,uf]
  have ju : J*u=J := by change (pair u-F)*u=pair u-F; rw [sub_mul,pair_right _ hu,fu]
  change F*X₃=X₃ at xL
  change X₃*F=X₃ at xR
  have ux : u*X₃=X₃ := by calc
    _ = u*(F*X₃) := by rw [xL]
    _ = _ := by rw [← mul_assoc,uf,xL]
  have xu : X₃*u=X₃ := by calc
    _ = (X₃*F)*u := by rw [xR]
    _ = _ := by rw [mul_assoc,fu,xR]
  have hB : B = X₃ + a • ((-9/4 : ℚ) • (F*P*J+J*P*F)) := by
    unfold B corrected
    rw [movedDifference_eq _ _ _ hu pL pR, correction_mixed _ _ _ hu pL pR]
  have bl : u*B=B := by rw [hB]; simp only [mul_add,mul_smul_comm,← mul_assoc,uf,uj,ux]
  have br : B*u=B := by rw [hB]; simp only [add_mul,smul_mul_assoc,mul_assoc,fu,ju,xu]
  have avgB : T B=T X₃ := by
    have z₁ : T (F*P*J) = 0 := by rw [mul_assoc, sF, mul_assoc, jf, mul_zero, map_zero]
    have z₂ : T (J*P*F) = 0 := by rw [mul_assoc, sJ, mul_assoc, fj, mul_zero, map_zero]
    rw [hB]; simp [z₁,z₂]
  have three : (3 : ℚ) • T (F*(w*B*w)*F) = T B+(2 : ℚ) • T (B*t) := by
    rw [t_eq]
    exact averaged_move _ _ _ _ hu hv hw braid uw su sv sw bl br
  have c : F*C+C*F=(2 : ℚ) • B := crossed_exits _ _ _ _ _ hu hv braid pL pR xL xR
  have crossed : T (F*(C*t+t*C)*F) = (2 : ℚ) • T (B*t) := by
    rw [squeeze sF ff, add_mul, map_add]
    have h₁ : T (C*t*F) = T (F*C*t) := by rw [← sF, mul_assoc]
    have h₂ : T (t*C*F) = T (C*F*t) := by rw [mul_assoc, st]
    rw [h₁,h₂,← map_add, ← add_mul,c,smul_mul_assoc,map_smul]
  change T (X₄-X₃ + (3 : ℚ) • (F*(w*B*w)*F) - F*(C*t+t*C)*F) = X₄
  change T X₄ = X₄ at invariant
  rw [map_sub,map_add,map_sub,map_smul,three,crossed,avgB,invariant]
  module

/-- Equation (fourQ), two-sided support part. The entire corrected operator
absorbs the 123-clasp on its upright boundary. -/
theorem four_supported (a : ℚ) (u v w t P X₃ X₄ : R)
    (hu : u*u=1) (hv : v*v=1) (braid : u*v*u=v*u*v)
    (xL : triple u v*X₃=X₃) (xR : X₃*triple u v=X₃)
    (yL : triple u v*X₄=X₄) (yR : X₄*triple u v=X₄) :
    triple u v * fourOperator a u v w t P X₃ X₄ * triple u v =
      fourOperator a u v w t P X₃ X₄ := by
  let F := triple u v
  have ff : F*F=F := triple_idem _ _ hu hv braid
  have absorb (Y : R) : F*(F*Y*F)*F = F*Y*F := by
    calc
      _ = (F*F)*Y*(F*F) := by simp only [mul_assoc]
      _ = _ := by rw [ff]
  dsimp only [F] at absorb
  unfold fourOperator
  simp only [mul_sub, mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, absorb,
    xL,xR,yL,yR]

end BlockPermanents.TransferBlocks
