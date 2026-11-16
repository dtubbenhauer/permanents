import BlockPermanents.ThreeCanonical
import BlockPermanents.ClaspAbsorb

/-! Ordinary and marked boundary coordinates for a bend at the thin and packet scales.
The packet alphabet indexes all thin words; projecting each incoming word realizes
the symmetric packet space inside these ambient coordinates. -/
namespace BlockPermanents.ZeroCap
open Bend ThreeGeneralOpen
open scoped BigOperators Matrix
noncomputable section

abbrev Packet (d k : ℕ) := Word d k
abbrev Packets (d k m : ℕ) := Fin m → Packet d k
abbrev dim (d k : ℕ) := Fintype.card (Packet d k)
def flat (d k m : ℕ) : Packets d k m ≃ Word d (m*k) :=
  (Equiv.curry _ _ _).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl (Fin d)))
def letters (d k m : ℕ) : Packets d k m ≃ Word (dim d k) m :=
  (Equiv.refl _).arrowCongr (Fintype.equivFin _)
def single (d k : ℕ) : Packet d k ≃ Word (dim d k) 1 :=
  (Fintype.equivFin _).trans (Equiv.funUnique _ _).symm

def mark (d k : ℕ) := symClasp d k
def merge (d k m : ℕ) : Matrix (Word d (m*k)) (Packets d k m) ℂ :=
  fun w i => symClasp d (m*k) w (flat d k m i)
def inner (d k m : ℕ) : Matrix (Packets d k m) (Packets d k m) ℂ :=
  fun w i => ∏ t, symClasp d k (w t) (i t)
def coarseMerge (d k m : ℕ) : Matrix (Word (dim d k) m) (Packets d k m) ℂ :=
  symClasp (dim d k) m * Matrix.of (fun w i => inner d k m ((letters d k m).symm w) i)
def coarseMark (d k : ℕ) : Matrix (Word (dim d k) 1) (Packet d k) ℂ :=
  fun w i => mark d k ((single d k).symm w) i

/-- A complete cap with the last packet after the chosen ordinary map. -/
def fullCut {K I J : Type*} [Fintype K] {n : ℕ}
    (F : Matrix (Fin (n+1)→K) I ℂ) (N : Matrix K J ℂ) :
    Matrix (Fin n→K) (I×J) ℂ :=
  fun t x => ∑ a, F (Fin.snoc t a) x.1 * star (N a x.2)

def appendLast {D p k : ℕ} (h : k≤p) (a : Word D (p-k)) (t : Word D k) : Word D p :=
  fun i => Fin.append a t (Fin.cast (Nat.sub_add_cancel h).symm i)
def termRows {D p k n : ℕ} {K I : Type*} (h : k≤p) (front : (Fin n→K) ≃ Word D (p-k))
    (letter : K ≃ Word D k) (M : Matrix (Word D p) I ℂ) : Matrix (Fin (n+1)→K) I ℂ :=
  fun t i => M (appendLast h (front (Fin.init t)) (letter (t (Fin.last n)))) i

theorem thin_le (n k : ℕ) : k ≤ (n+1)*k := by rw [Nat.add_mul,one_mul];omega
def thinFront (d k n : ℕ) : Packets d k n ≃ Word d ((n+1)*k-k) :=
  (flat d k n).trans ((finCongr (by rw [Nat.add_mul,one_mul,Nat.add_sub_cancel])).symm.arrowCongr (Equiv.refl _))
def coarseFront (d k n : ℕ) : Packets d k n ≃ Word (dim d k) ((n+1)-1) :=
  letters d k n
def thinRows (d k n : ℕ) := termRows (thin_le n k) (thinFront d k n) (Equiv.refl _) (merge d k (n+1))
def packetRows (d k n : ℕ) := termRows (show 1≤n+1 by omega) (coarseFront d k n)
  (single d k) (coarseMerge d k (n+1))

def a (m k : ℕ) : ℂ := ((m*k).factorial : ℂ) / (k.factorial:ℂ)^m
def oldX (d k m : ℕ) := a m k • Support.reflected (merge d k m) -
  (m.factorial : ℂ) • Support.reflected (coarseMerge d k m)
def newX (d k m : ℕ) := a (m+1) k • opened (fun _ : Unit => merge d k m) (mark d k) -
  ((m+1).factorial : ℂ) • opened (fun _ : Unit => coarseMerge d k m) (coarseMark d k)
def proper (d k n : ℕ) := properSquares (thin_le n k) (fun _ : Unit => merge d k (n+1)) (mark d k)

end
end BlockPermanents.ZeroCap
