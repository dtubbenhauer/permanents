import BlockPermanents.FourCapValues
import BlockPermanents.FourSpectator

/-! # Reindexing the quadratic proper-cut energies -/
namespace BlockPermanents.FourCapValues
open Bend FourRoutes FourLastCaps Equiv
open scoped BigOperators Matrix
noncomputable section

private def properSlots (r : Fin 3) : U r ⊕ Fin ((r.val+1)*2-1) ≃ Port :=
  Equiv.ofBijective (Sum.elim (spectatorPort r) (activePort r)) (by fin_cases r <;> decide)

/-- The five positive coordinates of a proper cut are its spectator word
together with the uncontracted positive part of the merged active cable. -/
def properWords (d : ℕ) (r : Fin 3) : (Port → Fin d) ≃
    Spectator d 2 (r.val+1) × Word d ((r.val+1)*2-1) :=
  ((properSlots r).symm.arrowCongr (Equiv.refl _)).trans
    ((sumArrowEquivProdArrow _ _ _).trans ((Equiv.curry _ _ _).prodCongr (Equiv.refl _)))

private def properCut (r : Fin 3) : CutIndex ((r.val+1)*2) 2 :=
  ⟨1, by have := r.isLt; omega⟩

/-- The routed, contracted half as a matrix on the unspecialized input and
all spectator-sliced coordinates of its output. -/
def properEnergy {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) : ℝ :=
  ∑ s, energy ((capHalf d 2 (r.val+1) (by have := r.isLt;omega) (properCut r) s).mulVec
    (product F (fun z => star (H z))))

theorem proper_eq_raw {d : ℕ} (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) :
    properEnergy r F H = rawEnergy Finset.univ (raw r F H) := by
  let v (s : Spectator d 2 (r.val+1)) (a : Word d ((r.val+1)*2-1)) (t : Word d 1) :=
    (capHalf d 2 (r.val+1) (by have := r.isLt;omega) (properCut r) s).mulVec
      (product F (fun z => star (H z))) (a,t)
  let eb : Word d 1 ≃ Fin d := Equiv.funUnique _ _
  have he (w : Port → Fin d) (c : Fin d) :
      v ((properWords d r w).1) ((properWords d r w).2) (eb.symm c) = raw r F H w c := rfl
  have h := (properWords d r).sum_comp (fun sa =>
    ∑ c : Fin d, Complex.normSq (v sa.1 sa.2 (eb.symm c)))
  simp only [he,Fintype.sum_prod_type] at h
  change _ = ∑ w, ∑ c, Complex.normSq (raw r F H w c)
  rw [h]
  apply Finset.sum_congr rfl; intro s _
  unfold energy; rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  exact (eb.symm.sum_comp (fun t => Complex.normSq (v s a t))).symm

/-- Dropping supported dual coordinates loses a sum of nonnegative squares. -/
theorem supported_proper_le {d : ℕ} (S : Finset (Fin d)) (r : Fin 3) (F : Triple d 2 → ℂ) (H : Word d 2 → ℂ) :
    rawEnergy S (raw r F H) ≤ properEnergy r F H := by
  rw [proper_eq_raw]
  apply Finset.sum_le_sum; intro w _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun _ _ _ => Complex.normSq_nonneg _

open FourCapOrbit FourQuadratic in
/-- All three actual proper-cut matrices and their scalar weights, with
the full-cap output of the first row and the labelled same/mixed amplitudes. -/
theorem proper_and_full {d : ℕ} (S : Finset (Fin d)) (hS : S.card = 2)
    {F : Triple d 2 → ℂ} (hF : Inner F) (H : Word d 2 → ℂ) (hH : Bend.Symmetric H)
    (fullW : Word d 4 → ℂ)
    (hwFull : ∀ t, Closures.clasp fullW t =
      (value S F H sameChart t + 2*value S F H mixedChart t)/3) :
    let x := value S F H sameChart
    let y := value S F H mixedChart
    0 ≤ 24*properEnergy 0 F H + 144*properEnergy 1 F H + 1080*properEnergy 2 F H +
      1350*energy (fun t => (x t+4*y t)/5-x t/15) + 108*energy fullW -
      12*energy (lastTrace S (some 3) (raw 0 F H)) - 24*energy x := by
  let x := value S F H sameChart
  let y := value S F H mixedChart
  have h (w) := five_values S hF H hH w
  have ha : activeSet 0 = {some 3} := by decide
  have hu₀ t : portCap S ({some 3} : Finset Slots)ᶜ (raw 0 F H) t = y t := by
    rw [← ha]; exact (h t).1
  have hu₁ t : portCap S {some 3} (raw 0 F H) t = x t := by
    rw [← ha]; exact (h t).2.1
  have hw (i : Fin 2) (t) : portCap S (PW i) (raw 1 F H) t = ![y t,fullCapMean 2 (x t) (y t)] i := by
    fin_cases i
    · exact (h t).2.2.1
    · exact (h t).2.2.2.1.trans (fullCapMeans _ _).1.symm
  have hv (i : Fin 1) t : portCap S (PV i) (raw 2 F H) t = fullCapMean 3 (x t) (y t) :=
    (h t).2.2.2.2.trans (fullCapMeans _ _).2.symm
  have hc := full_word_bound S hS (some 3) PW PV (by decide) (by decide) (by decide)
    (raw 0 F H) (raw 1 F H) (raw 2 F H) x y fullW hu₀ hu₁ hw hv
    (fun t => (hwFull t).trans (fullCapMeans _ _).1.symm)
  simp_rw [fun a b => (fullCapMeans a b).2] at hc
  dsimp only
  change 0 ≤ 24*properEnergy 0 F H + 144*properEnergy 1 F H + 1080*properEnergy 2 F H +
    1350*energy (fun t => (x t+4*y t)/5-x t/15)+108*energy fullW-
    12*energy (lastTrace S (some 3) (raw 0 F H))-24*energy x
  linarith only [hc,supported_proper_le S 0 F H,supported_proper_le S 1 F H,supported_proper_le S 2 F H]

end
end BlockPermanents.FourCapValues
