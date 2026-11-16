import BlockPermanents.FourActualAlgebra

/-! # The four-packet transfer before specializing the thickness

U, W, V denote the complete sums over proper cuts of their respective
local Schur openings. Full and zero cuts are kept as actual operators. -/
namespace BlockPermanents.FourSymbolic
open TransferBlocks FourWireAlgebra
variable {R : Type*} [Ring R] [Algebra ℚ R]
private theorem corrected_cross (a c : ℚ) (u v t P R' E : R)
    (uu : u*u=1) (pl : pair u*P=P) (pr : P*pair u=P)
    (F J : R) (hF : F=triple u v) (hJ : J=other u v) (ff : F*F=F)
    (fj : F*J=0) (jf : J*F=0) (fe : F*E=E) (ef : E*F=E)
    (placement : F*P*J*t*F+F*t*J*P*F =
      (1/3:ℚ) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F))) :
    let X := c • E-(6:ℚ) • F
    let C := (2:ℚ) • corrected a u v P X-X
    sand F (C*t+t*C) = c • (E*t*F+F*t*E) - (12:ℚ) • (F*t*F) -
      (3*a/2) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F)) := by
  let X := c • E-(6:ℚ) • F
  let M := F*P*J+J*P*F
  have corr : corrected a u v P X = X+(-9*a/4) • M := by
    rw [corrected,movedDifference_eq _ _ _ uu pl pr,correction_mixed _ _ _ uu pl pr,←hF,←hJ]
    unfold M
    module
  have fM : F*M=F*P*J := by dsimp only [M]; simp only [mul_add,←mul_assoc,ff,fj,zero_mul,add_zero]
  have Mf : M*F=J*P*F := by dsimp only [M]; simp only [add_mul,mul_assoc,ff,jf,mul_zero,zero_add]
  have fx : F*X=X := by simp only [X,mul_sub,mul_smul_comm,fe,ff]
  have xf : X*F=X := by simp only [X,sub_mul,smul_mul_assoc,ef,ff]
  let C := (2:ℚ) • corrected a u v P X-X
  have cL : F*C=X-(9*a/2) • (F*P*J) := by simp only [C,corr,mul_sub,mul_smul_comm,mul_add,fx,fM]; module
  have cR : C*F=X-(9*a/2) • (J*P*F) := by simp only [C,corr,sub_mul,smul_mul_assoc,add_mul,xf,Mf]; module
  change sand F (C*t+t*C)=_
  calc
    _=(F*C)*t*F+F*t*(C*F) := by change F*(C*t+t*C)*F = _; simp only [mul_add,add_mul,mul_assoc]
    _=c • (E*t*F+F*t*E) - (12:ℚ) • (F*t*F) -
      (9*a/2) • (F*P*J*t*F+F*t*J*P*F) := by
      rw [cL,cR]
      simp only [X,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,mul_assoc,ff]
      module
    _=_ := by rw [placement]; module


structure Opened {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : R →ₗ[ℚ] M)
    (ρ : FourPerm →* R) (P E big U W V : R) (a b c bigScale : ℚ) : Prop where
  last_three : φ (bigScale • big) = φ (c • E+c • V+
    (c*b) • (E*(ρ swap14)*E))
  last_two : φ (c • sand (ordinary ρ) (sand (ρ swap34) E)) =
    φ (a • sand (ordinary ρ) P+a • W+a^2 • (ordinary ρ*P*(ρ swap14)*P*ordinary ρ))
  last_one : φ (a • sand (ordinary ρ) (sand (ρ swap34) (movedPair ρ P))) =
    φ (ordinary ρ+U+ordinary ρ*(ρ swap14)*ordinary ρ)

def raw (F E P R' U W V t : R) (a b c : ℚ) : R :=
  (6:ℚ) • U + (3*a) • W + c • V +
  (c*b) • ((E - b⁻¹ • (F*R'))*t*(E - b⁻¹ • (R'*F))) +
  (3*a^2) • (F*P*t*P*F) - (12:ℚ) • (F*t*F) - (4*a) • (F*R'*t*R'*F)

private theorem expand (F E P R' U W V t : R) (a b : ℚ) (hb : b≠0)
    (rr : R'*R'=R') (rt : R'*t=t*R') (er : E*R'=E) (re : R'*E=E) :
    raw F E P R' U W V t a b (a*b) =
      (6:ℚ) • U + (3*a) • W + (a*b) • V +
      (a*b*b) • (E*t*E) - (a*b) • (E*t*F + F*t*E) +
      (3*a^2) • (F*P*t*P*F) - (12:ℚ) • (F*t*F) - (3*a) • (F*R'*t*F) := by
  have i : E*t*R'=E*t := by rw [mul_assoc, ← rt,← mul_assoc,er]
  have j : F*R'*t*E=F*t*E := by simp only [mul_assoc]; rw [← mul_assoc R' t, rt,mul_assoc,re]
  have k : F*R'*t*R'=F*R'*t := by
    calc
      _ = F*((R'*R')*t) := by simp only [mul_assoc]; rw [← rt]
      _ = _ := by rw [rr,mul_assoc]
  simp only [raw,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,← mul_assoc,i,j,k]
  match_scalars <;> field_simp [hb] <;> ring

theorem opened_transfer {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : R →ₗ[ℚ] M)
    (ρ : FourPerm →* R) (P E big U W V : R) (a b c bigScale : ℚ) (hb : b≠0) (hcab : c=a*b)
    (hc : FineClasps ρ P E) (h : Opened φ ρ P E big U W V a b c bigScale) :
    φ (fourOperator a (ρ swap12) (ρ swap23) (ρ swap34) (ρ swap14) P
      (c • E-(6:ℚ) • ordinary ρ) (bigScale • big-(24:ℚ) • Transfer.clasp ρ)) =
    φ (raw (ordinary ρ) E P (movedPair ρ P) U W V (ρ swap14) a b c) := by
  let u := ρ swap12
  let v := ρ swap23
  let w := ρ swap34
  let t := ρ swap14
  let s := ρ (Equiv.swap 0 2)
  let F := ordinary ρ
  let H := pair u
  let J := H-F
  let R' := movedPair ρ P
  let X := c • E-(6:ℚ) • F
  let B := corrected a u v P X
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
  have cc : sand F (C*t+t*C) = c • (E*t*F+F*t*E)-(12:ℚ) • (F*t*F)-
      (3*a/2) • (F*P*t*F+F*t*P*F-(2:ℚ) • (F*R'*t*F)) :=
    corrected_cross a c _ _ _ _ _ _ uu hP Ph F J rfl rfl ff FJ JF fe ef placement
  have mw := moved_mark u v w t P R' F ww wu wp bv (by rw [←eqs,dr]) fu uf pu up
  have exit := packet_exit F u (w*v*w) t uu fu uf ff tb
  rw [← conjugate_triple w u v ww wu] at exit
  change (3:ℚ) • sand F (sand w F)=_ at exit
  have moved : (3:ℚ) • sand F (sand w B) =
      (3:ℚ) • (c • sand F (sand w E)) + (6:ℚ) • (a • sand F (sand w R')) -
      (6:ℚ) • F - (12:ℚ) • (F*t*F) - (3*a) • sand F P -
      (3*a/2) • (F*P*t*F+F*t*P*F) := by
    change (3:ℚ) • sand F (sand w (X+a • movedDifference u v P)) = _
    simp only [X,map_add,map_sub,map_smul,mw]
    calc
      _ = (3:ℚ) • (c • sand F (sand w E)) + (6:ℚ) • (a • sand F (sand w R')) -
        (6:ℚ) • ((3:ℚ) • sand F (sand w F)) - (3*a) • sand F P -
        (3*a/2) • (F*P*t*F+F*t*P*F) := by module
      _ = _ := by rw [exit]; module
  have coarse : (24:ℚ) • Transfer.clasp ρ = (6:ℚ) • F + (18:ℚ) • (F*t*F) := coarse_four ρ

  change φ ((bigScale • big-(24:ℚ) • Transfer.clasp ρ)-X + (3:ℚ) • sand F (sand w B) -
    sand F (C*t+t*C)) = φ (raw F E P R' U W V t a b c)
  have eraw := expand F E P R' U W V t a b hb rr rt er re
  rw [←hcab] at eraw
  rw [moved,cc,coarse,eraw]
  obtain ⟨h3,h2,h1⟩ := h
  change φ (c • sand F (sand w E)) = φ (a • sand F P+a • W+a^2 • (F*P*t*P*F)) at h2
  change φ (a • sand F (sand w R')) = φ (F+U+F*t*F) at h1
  change φ (bigScale • big) = φ (c • E+c • V+(c*b) • (E*t*E)) at h3
  simp only [X,map_add,map_sub,map_smul] at h3 h2 h1 ⊢
  rw [h3,h2,h1]
  module

end BlockPermanents.FourSymbolic
