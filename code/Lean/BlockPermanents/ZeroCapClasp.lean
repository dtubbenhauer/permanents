import BlockPermanents.ZeroCap

/-! Identify the two defects of the zero-cap opening directly with the full
upright clasps on the thin and packet alphabets. -/
namespace BlockPermanents.ZeroCap
open Bend ThreeGeneralOpen Support
open scoped BigOperators Matrix
noncomputable section

def thinInput (d k m : ℕ) : Matrix (Word d (m*k)) (Packets d k m) ℂ :=
  fun w x => if w=flat d k m x then 1 else 0
def packetInput (d k m : ℕ) : Matrix (Word (dim d k) m) (Packets d k m) ℂ :=
  Matrix.of (fun w i => inner d k m ((letters d k m).symm w) i)

theorem merge_eq (d k m : ℕ) : merge d k m = symClasp d (m*k) * thinInput d k m := by
  ext x y; simp [merge,thinInput,Matrix.mul_apply,mul_ite]

private theorem legs_mul {A B C D I J : Type*} [Fintype C] [Fintype D]
    (P : Matrix A C ℂ) (Q : Matrix B D ℂ) (M : Matrix C I ℂ) (N : Matrix D J ℂ) :
    legs (P*M) (Q*N)=legs P Q * legs M N := by
  ext ⟨a,b⟩ ⟨i,j⟩
  simp only [legs,Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro x _
  apply Finset.sum_congr rfl;intro y _
  ring

private theorem clasp_self (d p : ℕ) : (symClasp d p)ᴴ = symClasp d p := by
  ext x y;exact column_star _ _
private theorem clasp_sq (d p : ℕ) : symClasp d p * symClasp d p = symClasp d p := by
  ext x y;exact congrFun (column_symmetric d p y) x

private theorem opened_absorbs {d p q : ℕ} {I J : Type*}
    (M : Matrix (Word d p) I ℂ) (N : Matrix (Word d q) J ℂ) :
    opened (fun _ : Unit => symClasp d p * M) (symClasp d q * N) =
      (legs M N)ᴴ * totalClasp d p q * legs M N := by
  have hh : (legs (symClasp d p) (symClasp d q))ᴴ = legs (symClasp d p) (symClasp d q) := by
    ext x y; simp only [Matrix.conjTranspose_apply,legs,star_mul',column_star]
  simp only [opened,Finset.univ_unique,Finset.sum_singleton,legs_mul,Matrix.conjTranspose_mul,hh]
  rw [Matrix.mul_assoc _ _ (totalClasp d p q),total_absorbs_left,
    Matrix.mul_assoc,← Matrix.mul_assoc (totalClasp d p q),total_absorbs,←Matrix.mul_assoc]

/-- The typed full clasps at both scales give the usual unbent new defect. On
the packet scale each thin-word input is compressed to its symmetric cable. -/
theorem newX_clasps (d k m : ℕ) :
    let thin := legs (thinInput d k m) (1 : Matrix (Packet d k) (Packet d k) ℂ)
    let packet := legs (packetInput d k m) (coarseMark d k)
    newX d k m = a (m+1) k • (thinᴴ * totalClasp d (m*k) k * thin) -
      ((m+1).factorial:ℂ) • (packetᴴ * totalClasp (dim d k) m 1 * packet) := by
  dsimp only
  unfold newX
  congr 2
  · simpa only [←merge_eq,Matrix.mul_one,mark] using
      opened_absorbs (thinInput d k m) (1 : Matrix (Packet d k) (Packet d k) ℂ)
  · simpa only [singleton_clasp,Matrix.one_mul] using opened_absorbs (packetInput d k m) (coarseMark d k)

private theorem reflected_project {d p : ℕ} {I : Type*} (M : Matrix (Word d p) I ℂ) :
    reflected (symClasp d p*M)=Mᴴ*symClasp d p*M := by
  rw [reflected,Matrix.conjTranspose_mul,clasp_self,Matrix.mul_assoc,←Matrix.mul_assoc (symClasp d p),
    clasp_sq,←Matrix.mul_assoc]

theorem oldX_clasps (d k m : ℕ) :
    let thin := thinInput d k m
    let packet := packetInput d k m
    oldX d k m = a m k • (thinᴴ * symClasp d (m*k) * thin) -
      (m.factorial:ℂ) • (packetᴴ * symClasp (dim d k) m * packet) := by
  dsimp only
  rw [oldX,merge_eq,reflected_project]
  change _ - _ • reflected (symClasp (dim d k) m * packetInput d k m) = _
  rw [reflected_project]

end
end BlockPermanents.ZeroCap
