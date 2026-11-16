import BlockPermanents.ThreeCertificateData

namespace BlockPermanents.ThreeWire

/-- Fold one consecutive group of wire terms into the current coefficient table. -/
def insertTerm (b : Bins) (e : ℤ × Wire) := addBin (code (normal e.2)) e.1 b

def through (l : Terms) (k : ℕ) : ℕ → Bins
  | 0 => []
  | n+1 => (((l.drop (k*n)).take k).foldl insertTerm (through l k n))

theorem through_spec (l : Terms) (k n : ℕ) :
    through l k n = (l.take (k*n)).foldl insertTerm [] := by
  induction n with
  | zero => simp [through]
  | succ n ih =>
    rw [through, ih, ← List.foldl_append, Nat.mul_succ]
    congr 1
    exact List.take_add.symm

theorem table_at (l : Terms) (k n : ℕ) (h : l.length ≤ k*n) :
    table l = (through l k n).filter (fun e => e.2 ≠ 0) := by
  rw [through_spec, List.take_of_length_le h]
  rfl

end BlockPermanents.ThreeWire
