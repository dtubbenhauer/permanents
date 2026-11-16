import BlockPermanents.ThreeCanonical

/-! Removing a square-fork digon and opening a clasp by one thin strand. -/
namespace BlockPermanents.Digon
open Bend WireSchur ThreeGeneralOpen SchurNormalization
open scoped Matrix BigOperators
noncomputable section

def join {d n r : ℕ} (h : r ≤ n) : Word d (n-r) × Word d r ≃ Word d n :=
  (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans ((splitSlot h).arrowCongr (Equiv.refl _))

theorem join_eq {d n r : ℕ} (h : r ≤ n) (a : Word d (n-r)) (b : Word d r) :
    join h (a,b) = fun i => Fin.append a b (Fin.cast (Nat.sub_add_cancel h).symm i) := by
  funext i
  obtain ⟨i,rfl⟩ := (splitSlot h).surjective i
  cases i <;> simp [join,splitSlot,finCongr,-Fin.natAdd_eq_addNat]

theorem fork_entry {d n r : ℕ} (h : r≤n) (a : Word d (n-r) × Word d r) (x : Word d n) :
    wordFork d n r h a x = symClasp d n (join h a) x := by
  cases a; rw [join_eq];rfl

/-- Split and then merge. The ambient matrix for the identity of Symⁿ is its clasp. -/
theorem merge_split {d n r : ℕ} (h : r≤n) :
    (wordFork d n r h)ᴴ * wordFork d n r h = symClasp d n := by
  ext x y
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,fork_entry,symClasp_star]
  exact ((join h).sum_comp (fun a => symClasp d n x a * symClasp d n a y)).trans
    (congrFun (column_symmetric d n y) x)

/-- Merge and then split. Both ends retain their grouped ordinary word coordinates. -/
theorem split_merge {d n r : ℕ} (h : r≤n) :
    wordFork d n r h * (wordFork d n r h)ᴴ = (symClasp d n).submatrix (join h) (join h) := by
  ext x y
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,fork_entry,symClasp_star,Matrix.submatrix_apply]
  exact congrFun (column_symmetric d n (join h y)) (join h x)

theorem empty_exchange (p q : ℕ) : exchangePerm p q (emptyCut p q)=1 := by
  ext (i|j)
  · obtain ⟨i|i,rfl⟩ := (splitSlot (leftLe (emptyCut p q))).surjective i
    · rw [exchange_left_prefix];rfl
    · exact Fin.elim0 i
  · obtain ⟨j|j,rfl⟩ := (splitSlot (rightLe (emptyCut p q))).surjective j
    · rw [exchange_right_prefix];rfl
    · exact Fin.elim0 j

/-- One placement retains the marked strand. The other p placements give the
same exchange between the two copies of the p-clasp. -/
theorem clasp_recursion (d p : ℕ) (hp : 0<p) (h : HomogeneousSchur d p 1) :
    ((p+1:ℕ):ℚ) • Transfer.clasp (action d p 1) = blockOp d p 1 +
    (p:ℚ) • (blockOp d p 1 * action d p 1 (exchangePerm p 1 (lastCut p 1 hp)) * blockOp d p 1) := by
  have hm : middle p 1 hp = ∅ := by
    apply Finset.eq_empty_of_forall_not_mem
    intro r hr
    obtain ⟨hn,hr⟩ := Finset.mem_erase.mp hr
    obtain ⟨hz,_⟩ := Finset.mem_erase.mp hr
    have h1 : r.val ≠ 1 := fun e => hn (Fin.ext e)
    have h0 : r.val ≠ 0 := fun e => hz (Fin.ext e)
    have hl := rightLe r
    omega
  have hs := wire_schur_operator h
  rw [ends_sum (by decide : 0<1) hp,hm,Finset.sum_empty,add_zero,empty_exchange,map_one,mul_one,
    show blockOp d p 1 * blockOp d p 1=blockOp d p 1 from Transfer.clasp_sq _] at hs
  simpa [weight,emptyCut,lastCut,Nat.choose_succ_self_right] using hs

end
end BlockPermanents.Digon
