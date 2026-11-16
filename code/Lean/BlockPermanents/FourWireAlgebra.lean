import BlockPermanents.TransferBlocks
import BlockPermanents.ThreeWire

/-! # The upright four-quadratic calculation before bending
Here e exchanges one thin strand with the mark, and t exchanges the whole packet.
-/
namespace BlockPermanents.FourWireAlgebra
open TransferBlocks
variable {R : Type*} [Ring R] [Algebra ℚ R]

private theorem right_placement (A F t u v : R) (au : A*u=A) (vt : v*t=t*v) (vf : v*F=F) :
    A * triple u v * t * F = (2/3:ℚ) • (A*t*F) + (1/3:ℚ) • (A*v*u*t*F) := by
  have av : A*v*t*F=A*t*F := by rw [mul_assoc A v t, vt, ← mul_assoc A t v, mul_assoc (A*t), vf]
  simp only [triple,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,← mul_assoc,mul_one,au,av]
  module

private theorem left_placement (A F t u v : R) (ua : u*A=A) (tv : t*v=v*t) (fv : F*v=F) :
    F*t*triple u v*A = (2/3:ℚ) • (F*t*A) + (1/3:ℚ) • (F*t*(u*v)*A) := by
  have av : F*(t*(v*A))=F*(t*A) := by
    rw [← mul_assoc t v A, tv, mul_assoc v t A, ← mul_assoc F v, fv]
  simp only [triple,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_assoc,one_mul,ua,av]
  module

/-- The three placements of P under the upright packet clasp. -/
theorem off_diagonal_placements (F H P R' u v t : R)
    (hF : F=triple u v) (pu : P*u=P) (up : u*P=P) (vf : v*F=F) (fv : F*v=F)
    (vt : v*t=t*v) (ph : P*H=P) (hp : H*P=P)
    (rL : F*R'=F*P*v*u) (rR : R'*F=u*v*P*F) (rt : R'*t=t*R') :
    F*P*(H-F)*t*F + F*t*(H-F)*P*F =
      (1/3:ℚ) • (F*P*t*F + F*t*P*F - (2:ℚ) • (F*R'*t*F)) := by
  have a := right_placement (F*P) F t u v (by rw [mul_assoc,pu]) vt vf
  have b := left_placement (P*F) F t u v (by rw [← mul_assoc,up]) vt.symm fv
  rw [← hF,← rL] at a
  rw [← hF, show F*t*(u*v)*(P*F)=F*t*(R'*F) by rw [rR]; simp only [mul_assoc]] at b
  have br : F*t*(R'*F)=F*R'*t*F := by simp only [mul_assoc]; rw [← mul_assoc t R' F,← rt,mul_assoc]
  rw [br] at b
  have lift : F*t*F*P*F=F*t*F*(P*F) := mul_assoc _ _ _
  simp only [mul_sub, sub_mul, show F*P*H=F*P by rw [mul_assoc, ph], a,lift,b]
  rw [show F*t*H*P*F=F*t*P*F by rw [mul_assoc (F*t) H P,hp]]
  simp only [mul_assoc]
  module

private def orders3 : List FourPerm :=
  [1,swap12,swap23,swap12*swap23,swap23*swap12,swap12*swap23*swap12]

private theorem coset_orders :
    ((ThreeWire.permutations 4)++(ThreeWire.permutations 4)).Perm
      (orders3 ++ orders3 ++ (orders3.flatMap fun p => orders3.map fun q => p*swap14*q)) := by
  decide +kernel

private theorem sum_triple (ρ : FourPerm →* R) :
    (orders3.map ρ).sum = (6:ℚ) • triple (ρ swap12) (ρ swap23) := by
  simp [orders3,triple,map_mul]
  module

omit [Algebra ℚ R] in
private theorem double_sum (ρ : FourPerm →* R) (l : List FourPerm) :
    ((l.flatMap fun p => orders3.map fun q => p*swap14*q).map ρ).sum =
      (l.map ρ).sum * ρ swap14 * (orders3.map ρ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      map_mul, ih, List.map_cons, List.sum_cons, add_mul]
    congr 1
    induction orders3 with
    | nil => simp
    | cons a l ih => simp [ih,mul_add]

theorem coarse_four (ρ : FourPerm →* R) :
    (24:ℚ) • Transfer.clasp ρ = (6:ℚ) • triple (ρ swap12) (ρ swap23) +
      (18:ℚ) • (triple (ρ swap12) (ρ swap23) * ρ swap14 * triple (ρ swap12) (ρ swap23)) := by
  have h := (coset_orders.map ρ).sum_eq
  simp only [List.map_append, List.sum_append, double_sum, sum_triple, ThreeWire.sum_permutations,
    smul_mul_assoc,mul_smul_comm] at h
  have hc : Fintype.card FourPerm = 24 := by simp [FourPerm, Fintype.card_perm, Nat.factorial]
  unfold Transfer.clasp
  rw [hc]
  calc
    _ = (1/2:ℚ) • ((∑ p, ρ p) + (∑ p, ρ p)) := by norm_num; module
    _ = _ := by rw [h]; module

/-- The pre-bend form of the seven quadratic cut terms. The order F R
on the reflected side is essential because the upright half has order R F. -/
def raw (F E P R' e t : R) : R :=
  (24:ℚ) • (F*e*F) + (144:ℚ) • (F*P*e*P*F) + (1080:ℚ) • (E*e*E) +
  (1350:ℚ) • ((E - (1/15:ℚ) • (F*R'))*t*(E - (1/15:ℚ) • (R'*F))) +
  (108:ℚ) • (F*P*t*P*F) - (12:ℚ) • (F*t*F) - (24:ℚ) • (F*R'*t*R'*F)

theorem raw_expand (F E P R' e t : R) (rr : R'*R'=R') (rt : R'*t=t*R')
    (er : E*R'=E) (re : R'*E=E) :
    raw F E P R' e t =
      (24:ℚ) • (F*e*F) + (144:ℚ) • (F*P*e*P*F) + (1080:ℚ) • (E*e*E) +
      (1350:ℚ) • (E*t*E) - (90:ℚ) • (E*t*F + F*t*E) +
      (108:ℚ) • (F*P*t*P*F) - (12:ℚ) • (F*t*F) - (18:ℚ) • (F*R'*t*F) := by
  have i : E*t*R'=E*t := by rw [mul_assoc, ← rt,← mul_assoc,er]
  have j : F*R'*t*E=F*t*E := by simp only [mul_assoc]; rw [← mul_assoc R' t, rt,mul_assoc,re]
  have k : F*R'*t*R'=F*R'*t := by
    calc
      _ = F*((R'*R')*t) := by simp only [mul_assoc]; rw [← rt]
      _ = _ := by rw [rr,mul_assoc]
  simp only [raw,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,← mul_assoc,i,j,k]
  module

/-- Sandwich both ends without identifying its boundary vectors. -/
def sand (F : R) : R →ₗ[ℚ] R where
  toFun A := F*A*F
  map_add' A B := by simp [mul_add,add_mul]
  map_smul' a A := by simp [mul_smul_comm,smul_mul_assoc]

private theorem sandwich_involution (w : R) (ww : w*w=1) (x y : R) :
    sand w (x*y) = (sand w x)*(sand w y) := by
  change w*(x*y)*w=(w*x*w)*(w*y*w)
  calc
    _ = w*x*(w*w)*y*w := by rw [ww,mul_one]; simp [mul_assoc]
    _ = _ := by simp [mul_assoc]

private theorem sandwich_pair (w u : R) (ww : w*w=1) :
    sand w (pair u)=pair (sand w u) := by
  change sand w ((1/2:ℚ) • (1+u)) = _
  rw [map_smul,map_add,show sand w 1=1 by change w*1*w=1; rw [mul_one,ww]]
  rfl

private theorem outer_pair (F H x : R) (fh : F*H=F) (hf : H*F=F) :
    sand F (H*x*H)=sand F x := by
  change F*(H*x*H)*F=F*x*F
  calc
    _ = (F*H)*x*(H*F) := by simp [mul_assoc]
    _ = _ := by rw [fh,hf]

theorem packet_exit (F u b t : R)
    (hu : u*u=1) (fu : F*u=F) (uf : u*F=F) (ff : F*F=F) (ht : t=u*b*u) :
    (3:ℚ) • sand F (triple u b) = F+(2:ℚ) • (F*t*F) := by
  have hf : pair u*F=F := by simp only [pair,smul_mul_assoc,add_mul,one_mul,uf]; module
  have fh : F*pair u=F := by simp only [pair,mul_smul_comm,mul_add,mul_one,fu]; module
  have gb (x : R) : sand F (x*pair u)=F*x*F := by
    change F*(x*pair u)*F=F*x*F
    rw [mul_assoc, mul_assoc x,hf,←mul_assoc]
  have sb : F*b*F=F*t*F := by
    rw [ht]
    calc
      _ = (F*u)*b*(u*F) := by rw [fu,uf]
      _ = _ := by simp [mul_assoc]
  rw [← map_smul, three_exits u b hu, map_add,map_add,gb,gb,←ht,sb]
  rw [show sand F (pair u)=F by change F*pair u*F=F; rw [fh,ff]]
  module

/-- The moved correction, after the two copies of F have absorbed the
12-clasps. The four nontrivial packet permutations are retained explicitly. -/
theorem moved_mark (u v w t P R' F : R) (ww : w*w=1)
    (wu : w*u*w=u) (wp : w*P*w=P)
    (b : w*v*w=u*t*u) (hR : R'=(u*v*u)*P*(u*v*u))
    (fu : F*u=F) (uf : u*F=F) (pu : P*u=P) (up : u*P=P) :
    sand F (sand w (movedDifference u v P)) =
      (2:ℚ) • sand F (sand w R') - sand F P -
      (1/2:ℚ) • (F*P*t*F + F*t*P*F) := by
  let H := pair u
  have fh : F*H=F := by simp only [H,pair,mul_smul_comm,mul_add,mul_one,fu]; module
  have hf : H*F=F := by simp only [H,pair,smul_mul_assoc,add_mul,one_mul,uf]; module
  have wH : sand w H=H := by change sand w (pair u)=pair u; rw [sandwich_pair _ _ ww, show sand w u=u from wu]
  have wg : sand w (pair v)=pair (u*t*u) := by rw [sandwich_pair _ _ ww,show sand w v=u*t*u from b]
  have sf : H*(u*v*u)*P*(u*v*u)*H = H*R'*H := by rw [hR]; simp [mul_assoc]
  have l : sand F (P*pair (u*t*u)*H) = (1/2:ℚ) • (sand F P + F*P*t*F) := by
    change F*(P*((1/2:ℚ) • (1+u*t*u))*H)*F=_
    have ss : F*(P*(u*t*u))*F=F*P*t*F := by
      calc
        _= F*(P*u)*t*(u*F) := by simp [mul_assoc]
        _=_ := by rw [pu,uf]
    calc
      _= F*(P*((1/2:ℚ) • (1+u*t*u)))*(H*F) := by simp [mul_assoc]
      _=_ := by rw [hf]; simp only [mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_one,ss]; rfl
  have r : sand F (H*pair (u*t*u)*P) = (1/2:ℚ) • (sand F P + F*t*P*F) := by
    change F*(H*((1/2:ℚ) • (1+u*t*u))*P)*F=_
    have ss : F*((u*t*u)*P)*F=F*t*P*F := by
      calc
        _=(F*u)*t*(u*P)*F := by simp [mul_assoc]
        _=_ := by rw [fu,up]
    calc
      _= (F*H)*(((1/2:ℚ) • (1+u*t*u))*P)*F := by simp [mul_assoc]
      _=_ := by rw [fh]; simp only [mul_smul_comm,smul_mul_assoc,add_mul,mul_add,one_mul,ss]; rfl
  change sand F (sand w ((2:ℚ) • (H*(u*v*u)*P*(u*v*u)*H) - P*pair v*H-H*pair v*P)) = _
  rw [sf]
  simp only [map_sub,map_smul,sandwich_involution w ww,wH,show sand w P=P from wp,wg,
    outer_pair F H _ fh hf,l,r]
  module

/-- The crossed correction expressed through the two F,J blocks. -/
private theorem corrected_cross (u v t P R' E : R)
    (uu : u*u=1) (pl : pair u*P=P) (pr : P*pair u=P)
    (F J : R) (hF : F=triple u v) (hJ : J=other u v) (ff : F*F=F)
    (fj : F*J=0) (jf : J*F=0) (fe : F*E=E) (ef : E*F=E)
    (placement : F*P*J*t*F+F*t*J*P*F =
      (1/3:ℚ) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F))) :
    let X := (90:ℚ) • E-(6:ℚ) • F
    let C := (2:ℚ) • corrected 6 u v P X-X
    sand F (C*t+t*C) = (90:ℚ) • (E*t*F+F*t*E) - (12:ℚ) • (F*t*F) -
      (9:ℚ) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F)) := by
  let X := (90:ℚ) • E-(6:ℚ) • F
  let M := F*P*J+J*P*F
  have corr : corrected 6 u v P X = X+(-27/2:ℚ) • M := by
    rw [corrected,movedDifference_eq _ _ _ uu pl pr,correction_mixed _ _ _ uu pl pr,←hF,←hJ]
    unfold M
    module
  have fM : F*M=F*P*J := by dsimp only [M]; simp only [mul_add,←mul_assoc,ff,fj,zero_mul,add_zero]
  have Mf : M*F=J*P*F := by dsimp only [M]; simp only [add_mul,mul_assoc,ff,jf,mul_zero,zero_add]
  have fx : F*X=X := by simp only [X,mul_sub,mul_smul_comm,fe,ff]
  have xf : X*F=X := by simp only [X,sub_mul,smul_mul_assoc,ef,ff]
  let C := (2:ℚ) • corrected 6 u v P X-X
  have cL : F*C=X-(27:ℚ) • (F*P*J) := by simp only [C,corr,mul_sub,mul_smul_comm,mul_add,fx,fM]; module
  have cR : C*F=X-(27:ℚ) • (J*P*F) := by simp only [C,corr,sub_mul,smul_mul_assoc,add_mul,xf,Mf]; module
  change sand F (C*t+t*C)=_
  calc
    _=(F*C)*t*F+F*t*(C*F) := by change F*(C*t+t*C)*F = _; simp only [mul_add,add_mul,mul_assoc]
    _=(90:ℚ) • (E*t*F+F*t*E) - (12:ℚ) • (F*t*F) -
      (27:ℚ) • (F*P*J*t*F+F*t*J*P*F) := by
      rw [cL,cR]
      simp only [X,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,mul_assoc,ff]
      module
    _=_ := by rw [placement]; module

/-- Packet 23's fine clasp obtained by moving the original pair 12. -/
def movedPair (ρ : FourPerm →* R) (P : R) : R :=
  ρ (Equiv.swap 0 2) * P * ρ (Equiv.swap 0 2)

abbrev ordinary (ρ : FourPerm →* R) : R := triple (ρ swap12) (ρ swap23)

/-- The three ordinary unbent Schur openings, already in the linear image
where the internal two-slot packet clasps have been applied. -/
structure Openings {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : R →ₗ[ℚ] M)
    (ρ : FourPerm →* R) (P E big e : R) : Prop where
  six_two : φ ((2520:ℚ) • big) = φ ((90:ℚ) • E+(1080:ℚ) • (E*e*E)+
    (1350:ℚ) • (E*(ρ swap14)*E))
  four_two : φ ((90:ℚ) • sand (ordinary ρ) (sand (ρ swap34) E)) =
    φ ((6:ℚ) • sand (ordinary ρ) P+
       (48:ℚ) • (ordinary ρ*P*e*P*ordinary ρ)+
       (36:ℚ) • (ordinary ρ*P*(ρ swap14)*P*ordinary ρ))
  two_two : φ ((6:ℚ) • sand (ordinary ρ) (sand (ρ swap34) (movedPair ρ P))) =
    φ (ordinary ρ+(4:ℚ) • (ordinary ρ*e*ordinary ρ)+ordinary ρ*(ρ swap14)*ordinary ρ)

/-- Structural support and absorption of the ordinary fine clasps. -/
structure FineClasps (ρ : FourPerm →* R) (P E : R) : Prop where
  pp : P*P=P
  lp : ρ swap12*P=P
  rp : P*ρ swap12=P
  spectator : ρ swap34*P*ρ swap34=P
  pe : P*E=E
  ep : E*P=E
  uE : ρ swap12*E=E
  Eu : E*ρ swap12=E
  vE : ρ swap23*E=E
  Ev : E*ρ swap23=E

/-- The complete fixed four-packet reduction. Only the three local Schur
openings are used besides support of the fine clasps. -/
theorem four_quadratic_open {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : R →ₗ[ℚ] M)
    (ρ : FourPerm →* R) (P E big e : R) (hc : FineClasps ρ P E)
    (h : Openings φ ρ P E big e) :
    φ (fourOperator 6 (ρ swap12) (ρ swap23) (ρ swap34) (ρ swap14) P
      ((90:ℚ) • E-(6:ℚ) • ordinary ρ) ((2520:ℚ) • big-(24:ℚ) • Transfer.clasp ρ)) =
    φ (raw (ordinary ρ) E P (movedPair ρ P) e (ρ swap14)) := by
  let u := ρ swap12
  let v := ρ swap23
  let w := ρ swap34
  let t := ρ swap14
  let s := ρ (Equiv.swap 0 2)
  let F := ordinary ρ
  let H := pair u
  let J := H-F
  let R' := movedPair ρ P
  let X := (90:ℚ) • E-(6:ℚ) • F
  let B := corrected 6 u v P X
  let C := (2:ℚ) • B-X
  rcases hc with ⟨pp,up,pu,wp,pe,ep,ue,eu,ve,ev⟩
  change u*P=P at up
  change P*u=P at pu
  change v*E=E at ve
  change u*E=E at ue
  change E*u=E at eu
  change E*v=E at ev
  have uu : u*u=1 := by dsimp [u]; rw [←map_mul, show swap12*swap12=1 by decide,map_one]
  have vv : v*v=1 := by dsimp [v]; rw [←map_mul, show swap23*swap23=1 by decide,map_one]
  have ww : w*w=1 := by dsimp [w]; rw [←map_mul, show swap34*swap34=1 by decide,map_one]
  have ss : s*s=1 := by dsimp [s]; rw [←map_mul, show (Equiv.swap 0 2 : FourPerm)*Equiv.swap 0 2=1 by decide,map_one]
  have braid : u*v*u=v*u*v := by dsimp [u,v]; simp only [← map_mul]; apply congrArg; decide
  have sw : s*t*s=w := by dsimp [s,t,w]; simp only [← map_mul]; apply congrArg; decide
  have wu : w*u*w=u := by dsimp [u,w]; simp only [← map_mul]; apply congrArg; decide
  have bv : w*v*w=u*t*u := by dsimp [w,v,u,t]; simp only [← map_mul]; apply congrArg; decide
  have tb : t=u*(w*v*w)*u := by dsimp [w,v,u,t]; simp only [← map_mul]; apply congrArg; decide
  have vt : v*t=t*v := by dsimp [v,t]; simp only [← map_mul]; apply congrArg; decide
  have eqs : s=u*v*u := by dsimp [s,u,v]; simp only [← map_mul]; apply congrArg; decide
  have uf : u*F=F := triple_left u v uu
  have fu : F*u=F := triple_right u v uu
  have vf : v*F=F := by change v*triple u v=triple u v; rw [triple_flip _ _ braid, triple_left _ _ vv]
  have fv : F*v=F := by change triple u v*v=triple u v; rw [triple_flip _ _ braid, triple_right _ _ vv]
  have ff : F*F=F := triple_idem _ _ uu vv braid
  have fe : F*E=E := by
    change triple u v*E=E
    simp only [triple,smul_mul_assoc,add_mul,mul_assoc,one_mul,ue,ve]; module
  have ef : E*F=E := by
    change E*triple u v=E
    simp only [triple,mul_smul_comm,mul_add,← mul_assoc,mul_one,eu,ev]; module
  have hP : H*P=P := by simp only [H,pair,smul_mul_assoc,add_mul,one_mul,up]; module
  have Ph : P*H=P := by simp only [H,pair,mul_smul_comm,mul_add,mul_one,pu]; module
  have FJ : F*J=0 := by rw [show F*J=F*pair u-F*F from mul_sub ..,triple_pair _ _ uu,ff,sub_self]
  have JF : J*F=0 := by rw [show J*F=pair u*F-F*F from sub_mul ..,pair_triple _ _ uu,ff,sub_self]
  have fs : F*s=F := by rw [eqs]; simp only [← mul_assoc,fu,fv]
  have sf : s*F=F := by rw [eqs]; simp only [mul_assoc,uf,vf]
  have es : E*s=E := by rw [eqs]; simp only [← mul_assoc,eu,ev]
  have se : s*E=E := by rw [eqs]; simp only [mul_assoc,ue,ve]
  have dr : R'=s*P*s := rfl
  have rL : F*R'=F*P*v*u := by
    calc
      _ = (F*s)*P*s := by rw [dr]; simp only [mul_assoc]
      _ = F*(P*u)*v*u := by rw [fs,eqs]; simp only [mul_assoc]
      _ = _ := by rw [pu]
  have rR : R'*F=u*v*P*F := by
    calc
      _ = s*P*(s*F) := by rw [dr,mul_assoc _ s F]
      _ = u*v*(u*P)*F := by rw [sf,eqs]; simp only [mul_assoc]
      _ = _ := by rw [up]
  have rr : R'*R'=R' := by
    rw [dr]
    calc
      _ = s*(P*(s*s)*P)*s := by simp [mul_assoc]
      _ = _ := by rw [ss,mul_one,pp]
  have er : E*R'=E := by rw [dr,←mul_assoc,←mul_assoc,es,ep,es]
  have re : R'*E=E := by rw [dr,mul_assoc _ s E,se,mul_assoc,pe,se]
  have rt : R'*t=t*R' := by
    have wp' : w*P=P*w := by
      calc
        _ = (w*P*w)*w := by rw [mul_assoc (w*P) w w,ww,mul_one]
        _ = _ := by rw [wp]
    have st : s*t=w*s := by rw [←sw,mul_assoc (s*t) s s,ss,mul_one]
    have ts : t*s=s*w := by rw [←sw,←mul_assoc,←mul_assoc,ss,one_mul]
    calc
      _ = s*P*(s*t) := by rw [dr,mul_assoc]
      _ = (s*w)*P*s := by rw [st]; simp only [mul_assoc]; rw [←mul_assoc P w s,←wp',mul_assoc]
      _ = _ := by rw [←ts,dr]; simp only [mul_assoc]
  have placement := off_diagonal_placements F H P R' u v t rfl pu up vf fv vt Ph hP rL rR rt
  have cc : sand F (C*t+t*C) = (90:ℚ) • (E*t*F+F*t*E)-(12:ℚ) • (F*t*F)-
      (9:ℚ) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F)) :=
    corrected_cross _ _ _ _ _ _ uu hP Ph F J rfl rfl ff FJ JF fe ef placement
  have mw := moved_mark u v w t P R' F ww wu wp bv (by rw [←eqs,dr]) fu uf pu up
  have exit := packet_exit F u (w*v*w) t uu fu uf ff tb
  rw [← conjugate_triple w u v ww wu] at exit
  change (3:ℚ) • sand F (sand w F)=_ at exit
  have moved : (3:ℚ) • sand F (sand w B) =
      (3:ℚ) • ((90:ℚ) • sand F (sand w E)) + (6:ℚ) • ((6:ℚ) • sand F (sand w R')) -
      (6:ℚ) • F - (12:ℚ) • (F*t*F) - (18:ℚ) • sand F P -
      (9:ℚ) • (F*P*t*F+F*t*P*F) := by
    change (3:ℚ) • sand F (sand w (X+(6:ℚ) • movedDifference u v P)) = _
    simp only [X,map_add,map_sub,map_smul,mw]
    calc
      _ = (3:ℚ) • ((90:ℚ) • sand F (sand w E)) + (6:ℚ) • ((6:ℚ) • sand F (sand w R')) -
        (6:ℚ) • ((3:ℚ) • sand F (sand w F)) - (18:ℚ) • sand F P -
        (9:ℚ) • (F*P*t*F+F*t*P*F) := by module
      _ = _ := by rw [exit]; module
  have coarse : (24:ℚ) • Transfer.clasp ρ = (6:ℚ) • F + (18:ℚ) • (F*t*F) := coarse_four ρ
  change φ (((2520:ℚ) • big-(24:ℚ) • Transfer.clasp ρ)-X + (3:ℚ) • sand F (sand w B) -
    sand F (C*t+t*C)) = φ (raw F E P R' e t)
  rw [moved,cc,coarse,raw_expand _ _ _ _ _ _ rr rt er re]
  rcases h with ⟨h₆,h₄,h₂⟩
  change φ ((90:ℚ) • sand F (sand w E))=_ at h₄
  change φ ((6:ℚ) • sand F (sand w R'))=_ at h₂
  simp only [X,map_add,map_sub,map_smul] at h₆ h₄ h₂ ⊢
  change (90:ℚ) • φ (sand F (sand w E)) = (6:ℚ) • φ (sand F P) +
    (48:ℚ) • φ (F*P*e*P*F) + (36:ℚ) • φ (F*P*t*P*F) at h₄
  change (6:ℚ) • φ (sand F (sand w R')) = φ F+(4:ℚ) • φ (F*e*F)+φ (F*t*F) at h₂
  change (2520:ℚ) • φ big = (90:ℚ) • φ E + (1080:ℚ) • φ (E*e*E) + (1350:ℚ) • φ (E*t*E) at h₆
  rw [h₆,h₄,h₂]
  module

end BlockPermanents.FourWireAlgebra
