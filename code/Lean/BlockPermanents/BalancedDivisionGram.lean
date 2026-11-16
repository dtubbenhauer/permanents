import BlockPermanents.BalancedLastAverage

/-! The two balanced total clasps, evaluated on actual four-packet Gram
data. The thin-slot clasp has the multinomial normalization, whereas
the whole-packet clasp carries the factor 4!. -/
namespace BlockPermanents.BalancedDivision
open Bend Closures Bridges BalancedAssembly
noncomputable section

private def slots (k : ℕ) : Fin 4 × Fin k ≃ Fin (k+k+(k+k)) :=
  finProdFinEquiv.trans (finCongr (by omega))

private def joinFour (d k : ℕ) : B d k ≃ Word d (k+k+(k+k)) :=
  ((joinWords d k).prodCongr (joinWords d k)).trans (joinWords d (k+k))

private theorem selector (k : ℕ) (j : Fin k) :
    slots k (0,j) = Fin.castAdd (k+k) (Fin.castAdd k j) ∧
    slots k (1,j) = Fin.castAdd (k+k) (Fin.natAdd k j) ∧
    slots k (2,j) = Fin.natAdd (k+k) (Fin.castAdd k j) ∧
    slots k (3,j) = Fin.natAdd (k+k) (Fin.natAdd k j) := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;>
    simp [slots, finProdFinEquiv] <;> omega

private theorem flat_join {d k} (x : Fin 4 → Fin k → Fin d → ℂ) (y : B d k) :
    flatPackets x (joinFour d k y ∘ slots k) =
      packetProduct (packet (x 0)) (packet (x 1)) (packet (x 2)) (packet (x 3)) y := by
  have h := selector k
  simp only [flatPackets, Fin.prod_univ_four, Function.comp_apply, fun j => (h j).1,
    fun j => (h j).2.1, fun j => (h j).2.2.1, fun j => (h j).2.2.2,
    joinFour, Equiv.trans_apply, Equiv.prodCongr_apply, joinWords, Equiv.coe_fn_mk,
    Prod.map_fst, Prod.map_snd, Fin.append_left, Fin.append_right, packetProduct]
  ring

private theorem coefficient (k : ℕ) : a k ^ 2 * bigCoefficient k =
    ((4*k).factorial : ℂ) / (k.factorial : ℂ)^4 := by
  have h₁ := Nat.add_choose_mul_factorial_mul_factorial k k
  have h₂ := Nat.add_choose_mul_factorial_mul_factorial (k+k) (k+k)
  have ha : ((k+k).choose k : ℂ) * k.factorial * k.factorial = (k+k).factorial := by exact_mod_cast h₁
  have hb : ((k+k+(k+k)).choose (k+k) : ℂ) * (k+k).factorial * (k+k).factorial = (4*k).factorial := by
    rw [show 4*k = k+k+(k+k) by omega]
    exact_mod_cast h₂
  apply (eq_div_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))).mpr
  unfold a bigCoefficient
  linear_combination ((k+k+(k+k)).choose (k+k) : ℂ) *
    (((k+k).choose k : ℂ) * k.factorial * k.factorial + (k+k).factorial) * ha + hb

theorem fine_gram {d k : ℕ} (x : Fin 4 → Fin k → Fin d → ℂ) :
    (a k ^ 2 * bigCoefficient k) * quadratic (BalancedOpen.totalFine d k)
        (packetProduct (packet (x 0)) (packet (x 1)) (packet (x 2)) (packet (x 3))) =
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent := by
  let z := fun w : Word d (k+k+(k+k)) => flatPackets x (w ∘ slots k)
  have hv : packetProduct (packet (x 0)) (packet (x 1)) (packet (x 2)) (packet (x 3)) =
      z ∘ joinFour d k := funext fun y => (flat_join x y).symm
  have q := quadratic_reindex (joinFour d k) (symClasp d (k+k+(k+k))) z
  change quadratic (BalancedOpen.totalFine d k) _ = _ at q
  rw [hv, q, quadratic_bracket, symClasp_action]
  dsimp only [z]
  rw [bracket_transport, ← bracket_clasp, coefficient]
  simpa only [Fintype.card_fin] using fine_closure x x

private def encode (K : Type*) [Fintype K] : BalancedOpen.Boundary K ≃ Word (Fintype.card K) 4 :=
  ((BalancedPacket.letters K).prodCongr (BalancedPacket.letters K)).trans
    (joinWords (Fintype.card K) 2)

private theorem packet_encode {K : Type*} [Fintype K] (X : Fin 4 → K → ℂ)
    (y : BalancedOpen.Boundary K) :
    pureWord (fun i => X i ∘ (Fintype.equivFin K).symm) (encode K y) =
      packetProduct (X 0) (X 1) (X 2) (X 3) y := by
  rw [pureWord, Fin.prod_univ_four]
  let e := Fintype.equivFin K
  change X 0 (e.symm (e y.1.1)) * X 1 (e.symm (e y.1.2)) *
    X 2 (e.symm (e y.2.1)) * X 3 (e.symm (e y.2.2)) = _
  simp only [Equiv.symm_apply_apply,packetProduct]
  ring

theorem coarse_gram {K : Type*} [Fintype K] (X : Fin 4 → K → ℂ) :
    24 * quadratic (BalancedPacket.total K) (packetProduct (X 0) (X 1) (X 2) (X 3)) =
      (crossGram X X).permanent := by
  let e := Fintype.equivFin K
  let Y (i : Fin 4) := X i ∘ e.symm
  have hv : packetProduct (X 0) (X 1) (X 2) (X 3) =
      pureWord Y ∘ encode K := funext fun y => (packet_encode X y).symm
  have q := quadratic_reindex (encode K) (symClasp (Fintype.card K) 4) (pureWord Y)
  change quadratic (BalancedPacket.total K) _ = _ at q
  rw [hv,q,quadratic_bracket,symClasp_action,← bracket_clasp]
  have hc : (24 : ℂ) = ((Fintype.card (Fin 4)).factorial : ℂ) := by norm_num [Nat.factorial]
  rw [hc,clasp_pure_closure]
  congr 1
  ext i j
  exact e.symm.sum_comp (fun t => star (X i t) * X j t)

theorem defect_gram {d k : ℕ} (x : Fin 4 → Fin k → Fin d → ℂ) :
    quadratic (BalancedAssembly.defect d k)
        (packetProduct (packet (x 0)) (packet (x 1)) (packet (x 2)) (packet (x 3))) =
      (crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
        (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent := by
  let X := fun i => packet (x i)
  let v := packetProduct (X 0) (X 1) (X 2) (X 3)
  have ev (M N : Matrix (B d k) (B d k) ℂ) (a b : ℂ) :
      quadratic (a • M - b • N) v = a * quadratic M v - b * quadratic N v := by
    simp only [quadratic, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intros <;> ring
  change quadratic (BalancedAssembly.defect d k) v = _
  rw [BalancedAssembly.defect, ev, fine_gram x, coarse_gram X]

end
end BlockPermanents.BalancedDivision
