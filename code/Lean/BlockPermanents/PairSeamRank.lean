import BlockPermanents.SupportCup

/-! # The surviving support at a cut of a decomposable packet -/

namespace BlockPermanents.PairResidual
open Closures Bend
open scoped BigOperators
noncomputable section

/-- The surviving positive cable is spanned by the uncontracted atom products. -/
def space {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :=
  PacketSupport.splitSupport x r (PairBound.cut_le r)

/-- Dimension of the surviving positive cable in orthonormal seam coordinates. -/
abbrev rank {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :=
  SupportCup.Rank (space x r)

/-- Freezing the contracted word gives a vector in the surviving support. -/
theorem slice_mem {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k) (t : Word d r) :
    (fun a => packet x (PairBound.splitWords d k r (a,t))) ∈ space x r := by
  classical
  have h := PacketSupport.split_contraction_mem x r (PairBound.cut_le r)
    (fun u => if u = t then (1 : ℂ) else 0)
  simpa [space, PairBound.splitWords, ite_mul] using h

/-- If all surviving slices vanished, the original packet would vanish on every word. -/
theorem rank_pos {d k : ℕ} (x : Fin k → Fin d → ℂ) (hx : packet x ≠ 0) (r : CutIndex k k) :
    0 < rank x r := by
  rw [rank, SupportCup.rank_eq]
  apply Submodule.one_le_finrank_iff.mpr
  intro hzero
  apply hx
  funext w
  obtain ⟨⟨a,t⟩,rfl⟩ := (PairBound.splitWords d k r).surjective w
  have h := slice_mem x r t
  rw [hzero, Submodule.mem_bot] at h
  exact congrFun h a

/-- There is at most one generator for each choice of contracted slots. -/
theorem rank_le {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : CutIndex k k) :
    rank x r ≤ k.choose r := by
  rw [rank, SupportCup.rank_eq]
  exact PacketSupport.splitSupport_dimension x r (PairBound.cut_le r)

end
end BlockPermanents.PairResidual
