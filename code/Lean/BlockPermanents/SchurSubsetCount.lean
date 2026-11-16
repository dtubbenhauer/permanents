import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! Counting possible images of the first packet, grouped by the number of crossing slots. -/

namespace BlockPermanents.SchurSubsetCount

/-- An image of size p with r slots on the right is uniquely determined by
p−r slots on the left and r slots on the right. -/
def split {p q r : ℕ} (hr : r ≤ p) :
    {s : Finset (Fin p ⊕ Fin q) // s.card = p ∧ s.toRight.card = r} ≃
      {a : Finset (Fin p) // a.card = p-r} × {b : Finset (Fin q) // b.card = r} where
  toFun s :=
    (⟨s.1.toLeft, by
      have h := Finset.card_toLeft_add_card_toRight (u := s.val)
      rw [s.property.1, s.property.2] at h
      omega⟩, ⟨s.1.toRight, s.property.2⟩)
  invFun x := ⟨x.1.val.disjSum x.2.val, by
    simp [x.1.property, x.2.property, Nat.sub_add_cancel hr]⟩
  left_inv s := Subtype.ext Finset.toLeft_disjSum_toRight
  right_inv := by rintro ⟨a,b⟩; apply Prod.ext <;> apply Subtype.ext <;> simp

/-- The two choices of crossing slots contribute the binomial coefficient
from each packet in the Schur exchange. -/
theorem card_subsets {p q r : ℕ} (hr : r ≤ p) :
    Fintype.card {s : Finset (Fin p ⊕ Fin q) // s.card = p ∧ s.toRight.card = r} =
      p.choose r * q.choose r := by
  rw [Fintype.card_congr (split hr), Fintype.card_prod]
  simp only [Fintype.card_finset_len, Fintype.card_fin, Nat.choose_symm hr]

end BlockPermanents.SchurSubsetCount
