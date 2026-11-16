import BlockPermanents.Digon

/-! The ordinary fork in a routed cap absorbs the orthogonal symmetric merge. -/
namespace BlockPermanents.FourNative
open Bend ThreeGeneralOpen
open scoped BigOperators Matrix
noncomputable section

private theorem fork_merge_clasp {d p r : ℕ} (hr : r ≤ p) :
    wordFork d p r hr * symClasp d p = wordFork d p r hr := by
  ext x y
  simp only [Matrix.mul_apply, Digon.fork_entry]
  exact congrFun (column_symmetric d p y) (Digon.join hr x)

/-- After concatenating the active ordinary words one can insert the symmetric
merge before their cap. In orthonormal word coordinates there is no scalar. -/
theorem routed_merge_clasp {d p k : ℕ} {S I J : Type*}
    (M : S → Matrix (Word d p) I ℂ) (N : Matrix (Word d k) J ℂ)
    (r : CutIndex p k) (s : S) :
    routed (fun t => symClasp d p * M t) N r s = routed M N r s := by
  ext ⟨a,b⟩ ⟨i,j⟩
  let m := fun w => M s w i
  let n := fun w => N w j
  change (wordCap d p k r).mulVec (product ((symClasp d p).mulVec m) (fun t => star (n t))) (a,b) =
         (wordCap d p k r).mulVec (product m (fun t => star (n t))) (a,b)
  simp only [wordCap, cap_product, Matrix.mulVec_mulVec, fork_merge_clasp]

end
end BlockPermanents.FourNative
