import BlockPermanents.FourMarked
import BlockPermanents.FourMatrixHalves
import BlockPermanents.FourAdjoints
import BlockPermanents.FourWireAssembly

/-! # Marcus's inequality for four quadratic blocks (Theorem 5D.1) -/
namespace BlockPermanents.FourMatrix
open Closures FourTarget FourWireAlgebra FourWireCut FourMatrixHalves FourAdjoints FourUpright
open FourFullValues TransferBlocks SchurNormalization
noncomputable section

private lemma eval_reflected {d : ℕ} {A : Op d 2} (h : Reflected A A) :
    AdjointableHere A := fun z v => congrArg Complex.re (h z v)

set_option maxHeartbeats 1200000 in
/-- On normalized matrix packets, the original marked operator evaluates to
the three-family cut form, with the ordinary packet order read from the marked end. -/
theorem marked_cutForm {d : ℕ} (x : Fin 4 → Fin 2 → Fin d → ℂ)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2) :
    let a := x ∘ ori.symm
    (bracket (flatPackets x) (Q d 2 (flatPackets x))).re =
      cutForm (unmarked a) (packet (a 3)) := by
  let a := x ∘ ori.symm
  let E := localClasp d 2 3
  let P := localClasp d 2 2
  let J := ordinary (packets d 2)
  let R := movedPair (packets d 2) P
  obtain ⟨u,w,v,s⟩ := halves a (entire_ordinary d 2)
  have rp : R = suffix d 1 := reversed_pair d
  have he := raw_cutForm J E R P (flatPackets a) (unmarked a) (packet (a 3)) (Bridges.packet_symmetric _ _ _)
    (eval_reflected (ordinary_self d 2)) (eval_reflected (local_self d 2 3))
    (eval_reflected (moved_self d 2)) (eval_reflected (local_self d 2 2)) u (rp ▸ w) v s
  have orient := congrArg Complex.re (oriented_raw d (flatPackets x))
  dsimp only at orient ⊢
  change _ = (bracket (packets d 2 ori (flatPackets x))
    (raw J E R P (act d 2 single) (act d 2 double) (packets d 2 ori (flatPackets x)))).re at orient
  rw [oriented_flat] at orient
  exact (FourMarked.open_marked x h₂ h₄ h₆).trans (orient.trans he)

/-- The sole literature input is the homogeneous Schur switch on the
active ordinary cable and the marked quadratic cable. -/
theorem marcus_four_quadratic (h₂ : ∀ d, HomogeneousSchur d 2 2) (h₄ : ∀ d, HomogeneousSchur d 4 2)
    (h₆ : ∀ d, HomogeneousSchur d 6 2) : MarcusAt 4 2 := by
  apply FourRestricted.matrix_of_supported
  intro d x S hc hs
  rw [marked_cutForm x (h₂ d) (h₄ d) (h₆ d)]
  let a := x ∘ ori.symm
  change 0 ≤ cutForm (unmarked a) (packet (a 3))
  apply packet_cutForm S hc (fun i => a i.castSucc)
  exact hs

end
end BlockPermanents.FourMatrix
