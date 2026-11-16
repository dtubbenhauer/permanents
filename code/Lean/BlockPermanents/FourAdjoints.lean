import BlockPermanents.FourActualAlgebra
import BlockPermanents.FourLocalCompression
import BlockPermanents.FourWireCutDefs

/-! # Reflected upright factors and relabeling the marked crossing

The scalar in this module is the full complex coefficient. Conjugation
of the opened operator exchanges the first and third ordinary packets.
-/
namespace BlockPermanents.FourAdjoints
open Closures FourTarget FourWireAlgebra TransferBlocks
open scoped BigOperators
noncomputable section

variable {I : Type*} [Fintype I]

def rightPair (u : I → ℂ) : (I → ℂ) →ₗ[ℚ] ℂ where
  toFun := bracket u
  map_add' v w := by simp [bracket,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by
    change bracket u (c • v) = c • bracket u v
    simp only [bracket,Pi.smul_apply,Rat.smul_def,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros;ring

def leftPair (v : I → ℂ) : (I → ℂ) →ₗ[ℚ] ℂ where
  toFun u := bracket u v
  map_add' u w := by simp [bracket,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by
    change bracket (c • u) v = c • bracket u v
    simp [bracket,Rat.smul_def,Finset.mul_sum,mul_assoc]

abbrev End (I : Type*) := Module.End ℂ (I → ℂ)

/-- The reflected word-coordinate operator. -/
def Reflected (A B : End I) : Prop := ∀ x y, bracket x (A y) = bracket (B x) y

private theorem id_pair : Reflected (1 : End I) 1 := fun _ _ => rfl

theorem Reflected.add {A B C D : End I} (h : Reflected A B) (k : Reflected C D) :
    Reflected (A+C) (B+D) := by
  intro x y
  change rightPair x (A y+C y) = leftPair y (B x+D x)
  rw [map_add,map_add]; exact congrArg₂ (·+·) (h _ _) (k _ _)

theorem Reflected.sub {A B C D : End I} (h : Reflected A B) (k : Reflected C D) :
    Reflected (A-C) (B-D) := by
  intro x y
  change rightPair x (A y-C y) = leftPair y (B x-D x)
  rw [map_sub,map_sub]; exact congrArg₂ (·-·) (h _ _) (k _ _)

theorem Reflected.scale {A B : End I} (c : ℚ) (h : Reflected A B) :
    Reflected (c • A) (c • B) := by
  intro x y
  change rightPair x (c • A y) = leftPair y (c • B x)
  rw [map_smul,map_smul]; exact congrArg (c • ·) (h _ _)

theorem Reflected.mul {A B C D : End I} (h : Reflected A B) (k : Reflected C D) :
    Reflected (A*C) (D*B) := fun x y => (h x (C y)).trans (k (B x) y)

theorem perm_reflect {K D : Type*} [Fintype K] [DecidableEq K] [Fintype D] (p : Equiv.Perm K) :
    Reflected (Transfer.tensorAction K D p) (Transfer.tensorAction K D p⁻¹) := by
  intro z y
  let e := p.symm.arrowCongr (Equiv.refl D)
  simpa [e,bracket,Function.comp_def,Transfer.tensorAction] using
    e.sum_comp (fun w => (starRingEnd ℂ) (z (w ∘ p.symm)) * y w)

theorem average_self {G K D : Type*} [Group G] [Fintype G] [Fintype K] [DecidableEq K] [Fintype D]
    (ρ : G →* Equiv.Perm K) :
    let a := Transfer.clasp ((Transfer.tensorAction K D).comp ρ)
    Reflected a a := by
  dsimp only
  intro x y
  let c : ℚ := (Fintype.card G : ℚ)⁻¹
  simp only [Transfer.clasp,LinearMap.smul_apply,LinearMap.sum_apply,MonoidHom.comp_apply]
  change rightPair x (c • ∑ g, Transfer.tensorAction K D (ρ g) y) =
    leftPair y (c • ∑ g, Transfer.tensorAction K D (ρ g) x)
  simp only [map_smul,map_sum]
  apply congrArg (c • ·)
  change (∑ g, bracket x (Transfer.tensorAction K D (ρ g) y)) =
    ∑ g, bracket (Transfer.tensorAction K D (ρ g) x) y
  have hh (g : G) : bracket x (Transfer.tensorAction K D (ρ g) y) =
      bracket (Transfer.tensorAction K D (ρ g⁻¹) x) y := by
    rw [map_inv]; exact perm_reflect _ _ _
  simp_rw [hh]
  exact Equiv.sum_comp (Equiv.inv G) (fun g => bracket (Transfer.tensorAction K D (ρ g) x) y)

theorem local_self (d k n : ℕ) : Reflected (localClasp d k n) (localClasp d k n) := by
  letI : Fintype (group k n) := Fintype.ofFinite _
  exact average_self (D := Fin d) (group k n).subtype

theorem swap_self (d k : ℕ) (i j : Fin 4) :
    Reflected (packets d k (Equiv.swap i j)) (packets d k (Equiv.swap i j)) := by
  have h := perm_reflect (D := Fin d) (wires k (Equiv.swap i j))
  rwa [← map_inv,Equiv.Perm.inv_def,Equiv.symm_swap] at h

theorem ordinary_self (d k : ℕ) :
    Reflected (ordinary (packets d k)) (ordinary (packets d k)) := by
  let u := packets d k swap12
  let v := packets d k swap23
  have hu : Reflected u u := swap_self d k 0 1
  have hv : Reflected v v := swap_self d k 1 2
  have h := (((((id_pair.add hu).add hv).add (hu.mul hv)).add (hv.mul hu)).add
    ((hu.mul hv).mul hu)).scale (1/6:ℚ)
  change Reflected ((1/6:ℚ) • (1+u+v+u*v+v*u+u*v*u)) ((1/6:ℚ) • (1+u+v+u*v+v*u+u*v*u))
  convert h using 2; noncomm_ring

theorem moved_self (d k : ℕ) :
    let R := movedPair (packets d k) (localClasp d k 2)
    Reflected R R := by
  let s := packets d k (Equiv.swap 0 2)
  let P := localClasp d k 2
  have h : Reflected (s*P*s) (s*(P*s)) :=
    ((swap_self d k 0 2).mul (local_self d k 2)).mul (swap_self d k 0 2)
  simpa only [movedPair,mul_assoc,s,P] using h

theorem entire_ordinary (d k : ℕ) :
    localClasp d k 3 * ordinary (packets d k) = localClasp d k 3 := by
  let h := FourActualAlgebra.fine_clasps d k
  simp only [ordinary,triple,mul_smul_comm,mul_add,← mul_assoc,mul_one,h.Eu,h.Ev]
  module

private def turn (d : ℕ) := packets d 2 (Equiv.swap 0 2)

private theorem turn_sq (d : ℕ) : turn d * turn d = 1 := by
  rw [turn,← map_mul,show (Equiv.swap 0 2 : FourPerm)*Equiv.swap 0 2=1 by decide,map_one]

private theorem turn_ordinary (d : ℕ) :
    sand (turn d) (ordinary (packets d 2)) = ordinary (packets d 2) := by
  let ρ := packets d 2
  let u := ρ swap12
  let v := ρ swap23
  let F := ordinary ρ
  have uu : u*u=1 := by dsimp [u];rw [← map_mul,show swap12*swap12=1 by decide,map_one]
  have vv : v*v=1 := by dsimp [v];rw [← map_mul,show swap23*swap23=1 by decide,map_one]
  have braid : u*v*u=v*u*v := by dsimp [u,v];simp only [← map_mul];congr 1;decide
  have ts : turn d = u*v*u := by change ρ _ = ρ _ * ρ _ * ρ _;simp only [← map_mul];congr 1;decide
  have uf : u*F=F := triple_left u v uu
  have fu : F*u=F := triple_right u v uu
  have vf : v*F=F := by change v*triple u v=triple u v;rw [triple_flip _ _ braid,triple_left _ _ vv]
  have fv : F*v=F := by change triple u v*v=triple u v;rw [triple_flip _ _ braid,triple_right _ _ vv]
  change turn d * F * turn d = F
  rw [ts]; simp only [mul_assoc,uf,vf];simp only [←mul_assoc,fu,fv]

private theorem turn_entire (d : ℕ) :
    sand (turn d) (localClasp d 2 3) = localClasp d 2 3 := by
  let ρ := packets d 2
  have ts : turn d = ρ swap12 * ρ swap23 * ρ swap12 := by
    change ρ _ = ρ _ * ρ _ * ρ _;simp only [← map_mul];congr 1;decide
  let h := FourActualAlgebra.fine_clasps d 2
  change turn d * localClasp d 2 3 * turn d = localClasp d 2 3
  rw [ts]
  simp only [mul_assoc,ρ,h.uE,h.vE];simp only [←mul_assoc,h.Eu,h.Ev]

private theorem sandwich_map {R : Type*} [Ring R] [Algebra ℚ R] {s : R} (hs : s*s=1) (A B : R) :
    sand s (A*B) = sand s A * sand s B := by
  change s*(A*B)*s = (s*A*s)*(s*B*s)
  calc
    _ = s*A*(s*s)*B*s := by rw [hs,mul_one];simp [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- Reverse the three upright packets. The original thick and thin
marked exchanges now act on the last ordinary packet, as in the coordinates
of the half diagrams. The two ordinary pair projectors exchange places. -/
theorem oriented_operator (d : ℕ) :
    let J := ordinary (packets d 2)
    let E := localClasp d 2 3
    let P := localClasp d 2 2
    let R := movedPair (packets d 2) P
    sand (packets d 2 (Equiv.swap 0 2)) (raw J E P R (act d 2 FourLocalCompression.eWire) (packets d 2 swap14)) =
      raw J E R P (act d 2 FourWireCut.single) (act d 2 FourWireCut.double) := by
  let P := localClasp d 2 2
  let R := movedPair (packets d 2) P
  have rev : sand (turn d) R = P := by
    change turn d * (turn d * P * turn d) * turn d = P
    calc
      _ = (turn d * turn d) * P * (turn d * turn d) := by simp only [mul_assoc]
      _ = P := by rw [turn_sq,one_mul,mul_one]
  have thin : sand (turn d) (act d 2 FourLocalCompression.eWire) = act d 2 FourWireCut.single := by
    change act d 2 (wires 2 (Equiv.swap 0 2)) * act d 2 _ * act d 2 _ = act d 2 _
    simp only [←map_mul];apply congrArg;decide
  have thick : sand (turn d) (packets d 2 swap14) = act d 2 FourWireCut.double := by
    change packets d 2 (Equiv.swap 0 2) * packets d 2 swap14 * packets d 2 (Equiv.swap 0 2) = packets d 2 swap34
    simp only [←map_mul];apply congrArg;decide
  have pre : sand (turn d) P = R := rfl
  dsimp only
  change sand (turn d) (raw _ _ P R _ _) = raw _ _ R P _ _
  simp only [raw,map_add,map_smul,map_sub,sandwich_map (turn_sq d),turn_ordinary,turn_entire,thin,thick,pre,rev]

private theorem sandwich_bracket {I : Type*} [Fintype I] {s : End I}
    (hs : Reflected s s) (hss : s*s=1) (A : End I) (z : I → ℂ) :
    bracket z (A z) = bracket (s z) (sand s A (s z)) := by
  have sq (y : I → ℂ) : s (s y) = y := congrArg (fun B : End I => B y) hss
  change bracket z (A z) = bracket (s z) (s (A (s (s z))))
  rw [sq,hs,sq]

private theorem transport {I : Type*} [Fintype I] (s A B : End I)
    (eqn : sand s A = B) (hs : Reflected s s) (hss : s*s=1) (z : I → ℂ) :
    bracket z (A z) = bracket (s z) (B (s z)) :=
  (sandwich_bracket hs hss A z).trans
    (congrArg (fun T : End I => bracket (s z) (T (s z))) eqn)

theorem oriented_raw (d : ℕ) (z : (Slot 2 → Fin d) → ℂ) :
    let J := ordinary (packets d 2)
    let E := localClasp d 2 3
    let P := localClasp d 2 2
    let R := movedPair (packets d 2) P
    let s := packets d 2 (Equiv.swap 0 2)
    bracket z (raw J E P R (act d 2 FourLocalCompression.eWire) (packets d 2 swap14) z) =
      bracket (s z) (raw J E R P (act d 2 FourWireCut.single) (act d 2 FourWireCut.double) (s z)) := by
  let J := ordinary (packets d 2)
  let E := localClasp d 2 3
  let P := localClasp d 2 2
  let R := movedPair (packets d 2) P
  let s := packets d 2 (Equiv.swap 0 2)
  let A := raw J E P R (act d 2 FourLocalCompression.eWire) (packets d 2 swap14)
  let B := raw J E R P (act d 2 FourWireCut.single) (act d 2 FourWireCut.double)
  exact transport s A B (oriented_operator d) (swap_self d 2 0 2) (turn_sq d) z

end
end BlockPermanents.FourAdjoints
