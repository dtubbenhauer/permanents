import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Weights of ordered maximum matchings (Section 7B)

Consecutive pairs of a permuted ordering form a maximum matching.
For odd cardinality the last position is the spectator.
-/

namespace BlockPermanents.MatchingFine
open scoped BigOperators

/-- Position of endpoint j in the e-th adjacent pair. -/
def partner (m : ℕ) (e : Fin (m/2)) (j : Fin 2) : Fin m :=
  ⟨j.val + 2 * e.val, by omega⟩

/-- Position of the unmatched label, if present. -/
def spectator (m : ℕ) (t : Fin (m%2)) : Fin m :=
  ⟨(m/2)*2 + t.val, by omega⟩

/-- A pair can pass through on both sides or form the reflected cap. -/
noncomputable def edgeFactor {I : Type*} (b : ℝ) (v : I → ℝ) (p : I → I → ℝ) (i j : I) : ℝ :=
  v i * v j + b * p i j

/-- Product of the pair bounds and the energy of the possible spectator. -/
noncomputable def orderedWeight (m : ℕ) (b : ℝ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) : ℝ :=
  (∏ e : Fin (m/2), edgeFactor b v p (σ (partner m e 0)) (σ (partner m e 1))) *
    ∏ t : Fin (m%2), v (σ (spectator m t))

end BlockPermanents.MatchingFine
