import BlockPermanents.ThreeGeneralEnds
import BlockPermanents.PairBound

/-! The packet-scale Schur opening of the balanced cut. The alphabet of
the two-letter packet words can itself be an entire thin word space. -/
namespace BlockPermanents.BalancedPacket
open Bend Support SchurNormalization Equiv
open scoped BigOperators Matrix
noncomputable section

abbrev Boundary (D : Type*) := (D×D)×(D×D)

variable (K : Type*) [Fintype K]

def letters : K×K ≃ Word (Fintype.card K) 2 :=
  ((Fintype.equivFin K).prodCongr (Fintype.equivFin K)).trans (finTwoArrowEquiv _).symm

def read (p : Boundary K) := (letters K p.1, letters K p.2)

def total : Matrix (Boundary K) (Boundary K) ℂ :=
  fun x y => totalClasp (Fintype.card K) 2 2 (read K x) (read K y)

def half (r : CutIndex 2 2) : Matrix
    (Word (Fintype.card K) (2-r) × Word (Fintype.card K) (2-r)) (Boundary K) ℂ :=
  fun a x => wordCap (Fintype.card K) 2 2 r a (read K x)

def packetPair (u v : K×K) := symClasp (Fintype.card K) 2 (letters K u) (letters K v)

def straight : Matrix (Boundary K) (Boundary K) ℂ := fun x y =>
  packetPair K x.1 y.1 * packetPair K x.2 y.2

private theorem real_clasp (d n : ℕ) (u v : Word d n) : star (symClasp d n u v) = symClasp d n u v := by
  simp [symClasp,star_mul',mul_comm,apply_ite star]

private theorem clasp_adjoint (d n : ℕ) : (symClasp d n)ᴴ=symClasp d n := by
  ext x y
  rw [Matrix.conjTranspose_apply,real_clasp]
  simp only [symClasp]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Perm (Fin n)))
  intro σ
  congr 1
  change (y=x ∘ σ)=(x=y ∘ σ.symm)
  apply propext
  constructor <;> rintro rfl <;> funext i <;> simp

private theorem clasp_gram (d n : ℕ) (x y : Word d n) :
    ∑ w, star (symClasp d n w x) * symClasp d n w y = symClasp d n x y := by
  let D := symClasp d n
  have sq : D*D=D := by
    apply Matrix.ext_of_mulVec_single
    intro i; rw [← Matrix.mulVec_mulVec]
    exact PairBound.projected_symmetric d n (Pi.single i 1)
  change ((Dᴴ*D) x y) = _
  rw [show Dᴴ=D from clasp_adjoint d n,sq]

private theorem zero_apply (a : Word (Fintype.card K) 2 × Word (Fintype.card K) 2) (x : Boundary K) :
    half K 0 a x = symClasp _ 2 a.1 (letters K x.1) * symClasp _ 2 a.2 (letters K x.2) := by
  simp [half,wordCap,cap,wordFork,read,Fin.append_right_nil _ _ rfl,Function.comp_def,real_clasp]

theorem zero_square : reflected (half K 0) = straight K := by
  ext x y
  let A := symClasp (Fintype.card K) 2
  have hh (a b : Word (Fintype.card K) 2) :
      star (half K 0 (a,b) x)*half K 0 (a,b) y =
      (star (A a (letters K x.1))*A a (letters K y.1)) *
      (star (A b (letters K x.2))*A b (letters K y.2)) := by
    simp only [zero_apply,star_mul',A];ring
  change (∑ w,star (half K 0 w x) * half K 0 w y) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hh,← Finset.mul_sum,←Finset.sum_mul]
  exact congrArg₂ (·*·) (clasp_gram _ _ (letters K x.1) (letters K y.1))
    (clasp_gram _ _ (letters K x.2) (letters K y.2))

theorem opening (h : HomogeneousSchur (Fintype.card K) 2 2) :
    (24:ℂ) • partialTranspose (total K) = (4:ℂ) • straight K +
      (16:ℂ) • reflected (half K 1) + (4:ℂ) • reflected (half K 2) := by
  have ho : (6:ℂ) • partialTranspose (total K) =
      ∑ r : CutIndex 2 2, (weight 2 2 r : ℂ) • reflected (half K r) := by
    ext i j; simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
    exact bent_schur (Fintype.card K) 2 2 (homogeneousSchur_implies_unbent _ _ _ h) (read K i) (read K j)
  rw [show (24:ℂ) = 4*6 by norm_num,← smul_smul,ho]
  change (4:ℂ) • (∑ r : Fin 3, _) = _
  rw [Fin.sum_univ_three]
  simp only [show weight 2 2 ((0:Fin 3):ℕ)=1 by decide,
    show weight 2 2 ((1:Fin 3):ℕ)=4 by decide,show weight 2 2 ((2:Fin 3):ℕ)=1 by decide,
    Nat.cast_one,Nat.cast_ofNat,one_smul,zero_square]
  module

end
end BlockPermanents.BalancedPacket
