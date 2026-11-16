import BlockPermanents.FullCapBoundary
import BlockPermanents.ZeroCap

/-! # The full and proper cuts on the actual packet word boundary -/
namespace BlockPermanents.TwoFullCaps
open Bend ZeroCap ThreeGeneralOpen Matrix
open scoped Matrix BigOperators
noncomputable section

private def readRows {K I : Type*} {n : ℕ} (P : Matrix (Fin (n+1)→K) I ℂ) :=
  fun (t : (Fin n→K)×K) (i : I) => P (Fin.snoc t.1 t.2) i

abbrev Bound (d k n : ℕ) := Packets d k (n+1) × Packet d k

def stationary (d k n : ℕ) : Matrix (Bound d k n) (Bound d k n) ℂ :=
  legs (oldX d k (n+1)) (mark d k)

/-- Interchange the marked packet with any chosen ordinary packet. -/
def packetSwap (d k n : ℕ) (q : Fin (n+1)) : Matrix (Bound d k n) (Bound d k n) ℂ :=
  fun i j => if i=(Function.update j.1 q j.2,j.1 q) then 1 else 0

def ordinary (d k n : ℕ) : Matrix (Packets d k (n+1)) (Packets d k (n+1)) ℂ :=
  Support.reflected (coarseMerge d k (n+1))

def moved (d k n : ℕ) (q : Fin (n+1)) : Matrix (Bound d k n) (Bound d k n) ℂ :=
  let B := stationary d k n
  let s := packetSwap d k n q
  let F : Matrix (Bound d k n) (Bound d k n) ℂ := ThreeTransfer.upright (ordinary d k n)
  F*(s*B*s)*F

/-- Corrected bend on the full ambient word space. Each mixed crossing maps
the ordinary words to the marked and surviving coordinates before crossing
and reflecting, with the internal marked projection on its two boundaries. -/
def correctedWords (d k n : ℕ) (q : Fin (n+1)) :=
  boundaryCorrection (n+1) k (newX d k (n+1)) (stationary d k n) (moved d k n q)
    (readRows (thinRows d k n)) (readRows (packetRows d k n)) (mark d k)

private theorem bend_stationary (d k n : ℕ) : partialTranspose (stationary d k n) = stationary d k n := by
  ext ⟨i,j⟩ ⟨u,v⟩
  change _ * symClasp d k v j = _ * symClasp d k j v
  rw [← column_star j v]
  congr 1
  simp only [symClasp,star_mul',star_inv₀,star_natCast,star_sum,apply_ite,star_one,star_zero]

private theorem cast_factor (n k : ℕ) : (fineFactor n k : ℂ) = a n k := by
  simp [fineFactor,a]

/-- Bend the actual signed word-operator summands, retaining the zero-cap
remainder as input for this algebraic step. -/
theorem full_words_from_zero (d k n : ℕ) (q : Fin (n+1))
    (hzero : partialTranspose (newX d k (n+1)) = stationary d k n + a (n+1) k • proper d k n +
      (a (n+1) k * (((n+1)*k).choose k : ℂ)) • Support.reflected (fullCut (thinRows d k n) (mark d k)) -
      (((n+1:ℂ))*(n+1).factorial) • Support.reflected (fullCut (packetRows d k n) (mark d k))) :
    let v := fullCut (thinRows d k n) (mark d k)
    let u := fullCut (packetRows d k n) (mark d k)
    partialTranspose (correctedWords d k n q) =
      (n+1:ℂ) • partialTranspose (moved d k n q) + a (n+1) k • proper d k n +
      ((a (n+1) k)^2/a n k) • (vᴴ*v) - ((n+1).factorial:ℂ) • (uᴴ*u) -
      ((n:ℂ)*a (n+1) k/2) • (vᴴ*u+uᴴ*v) := by
  let P : Matrix ((Fin n→Packet d k)×Packet d k) (Packets d k (n+1)) ℂ := readRows (thinRows d k n)
  let F : Matrix ((Fin n→Packet d k)×Packet d k) (Packets d k (n+1)) ℂ := readRows (packetRows d k n)
  have step := boundary_full_caps (n:=n+1) (k:=k) (Nat.succ_pos n) (newX d k (n+1)) (stationary d k n)
    (moved d k n q) (a (n+1) k • proper d k n) P F (mark d k)
  have vp : full P (mark d k) = fullCut (thinRows d k n) (mark d k) := rfl
  have uf : full F (mark d k) = fullCut (packetRows d k n) (mark d k) := rfl
  have convertScalar (r : ℚ) (M : Matrix (Bound d k n) (Bound d k n) ℂ) : r • M = (r:ℂ) • M := by
    ext i j; simp only [Matrix.smul_apply,Rat.smul_def,smul_eq_mul]
  simp only [convertScalar,Rat.cast_add,Rat.cast_natCast,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_one,cast_factor,Nat.cast_succ,Nat.succ_sub_one,add_sub_cancel_right,
    bend_stationary,vp,uf] at step
  exact step hzero

/-- The two full caps for arbitrary thickness and arbitrary positive ordinary
packet count, as an identity of matrices on all the ordinary and marked word
coordinates. Its two inputs are precisely the homogeneous Schur relations
on the thin and packet alphabets. -/
theorem full_words (d k n : ℕ) (q : Fin (n+1)) (hk : 0<k)
    (thin : SchurNormalization.HomogeneousSchur d ((n+1)*k) k)
    (packet : SchurNormalization.HomogeneousSchur (dim d k) (n+1) 1) :
    let v := fullCut (thinRows d k n) (mark d k)
    let u := fullCut (packetRows d k n) (mark d k)
    partialTranspose (correctedWords d k n q) =
      (n+1:ℂ) • partialTranspose (moved d k n q) + a (n+1) k • proper d k n +
      ((a (n+1) k)^2/a n k) • (vᴴ*v) - ((n+1).factorial:ℂ) • (uᴴ*u) -
      ((n:ℂ)*a (n+1) k/2) • (vᴴ*u+uᴴ*v) := by
  apply full_words_from_zero
  simpa only [Nat.cast_succ] using opening d k n hk thin packet

end
end BlockPermanents.TwoFullCaps
