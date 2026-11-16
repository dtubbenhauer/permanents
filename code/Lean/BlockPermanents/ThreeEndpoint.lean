import BlockPermanents.ThreeCertificateData
import BlockPermanents.Bridges
import BlockPermanents.MatchingThreshold
import Mathlib.Tactic.LinearCombination

/-! # Relabeling and closing the six-wire certificate on matrix packets -/
namespace BlockPermanents.ThreeEndpoint
open ThreeWire Closures

noncomputable section
abbrev Family (D : Type*) := Fin 3 → (Fin 2 → D) → ℂ
def bdy {D : Type*} (Y : Family D) : Words D → ℂ := boundary (Y 0) (Y 1) (Y 2)
def slots : (Fin 3 × Fin 2) ≃ Fin 6 := finProdFinEquiv

private def readWord {D : Type*} (w : Words D) (i : Fin 3) (t : Fin 2) := w (slots (i,t))

private theorem bdy_prod {D : Type*} (Y : Family D) (w : Words D) :
    bdy Y w = ∏ i, Y i (readWord w i) := by
  have h₀ : readWord w 0 = ![w 0,w 1] := by funext t; fin_cases t <;> rfl
  have h₁ : readWord w 1 = ![w 2,w 3] := by funext t; fin_cases t <;> rfl
  have h₂ : readWord w 2 = ![w 4,w 5] := by funext t; fin_cases t <;> rfl
  rw [Fin.prod_univ_three, h₀, h₁, h₂]
  rfl

private def lift (p : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 6) :=
  slots.symm.trans ((p.prodCongr (Equiv.refl _)).trans slots)

private theorem wire_lift (p : Equiv.Perm (Fin 3)) : packetOrder p = (lift p : Wire) := by
  funext i
  apply Fin.ext
  change 2*(p _).val + i.val%2 = i.val%2 + 2*(p _).val
  exact Nat.add_comm _ _

private theorem lift_slot (p : Equiv.Perm (Fin 3)) (i : Fin 3) (t : Fin 2) :
    lift p (slots (i,t)) = slots (p i,t) := by simp [lift]

private theorem lift_inv (p : Equiv.Perm (Fin 3)) : lift p.symm = (lift p).symm := rfl

private theorem bdy_relabel {D : Type*} (Y : Family D) (p : Equiv.Perm (Fin 3)) (w : Words D) :
    bdy Y (w ∘ lift p.symm) = bdy (Y ∘ p) w := by
  rw [bdy_prod, bdy_prod]
  symm
  apply Fintype.prod_equiv p
  intro i
  change Y (p i) _ = Y (p i) _
  congr 1
  funext t
  simp [readWord, lift_slot]

/-- Simultaneously changing the packet order at the bra and ket boundaries
simply changes the order of the three boundary vectors. -/
theorem evaluate_conjugate {D : Type*} [Fintype D] (Y : Family D) (p : Equiv.Perm (Fin 3)) (a : Wire) :
    evaluateWord (bdy Y) (packetOrder p ∘ a ∘ packetOrder p.symm) =
      evaluateWord (bdy (Y ∘ p)) a := by
  simp only [wire_lift]
  let e := (lift p).arrowCongr (Equiv.refl D)
  unfold evaluateWord bracket
  symm
  apply Fintype.sum_equiv e
  intro w
  change _ = (starRingEnd ℂ) (bdy Y (w ∘ (lift p).symm)) *
    bdy Y ((w ∘ (lift p).symm) ∘ (lift p : Wire) ∘ a ∘ lift p.symm)
  have h : ((w ∘ (lift p).symm) ∘ (lift p : Wire) ∘ a ∘ lift p.symm) =
      (w ∘ a) ∘ lift p.symm := by funext i; simp
  rw [h, ← lift_inv, bdy_relabel, bdy_relabel]

/-- Transport any weighted list of wirings, including the paper's six
correction terms, under an actual packet permutation. -/
theorem eval_relabel {D : Type*} [Fintype D] (Y : Family D) (p : Equiv.Perm (Fin 3)) (l : Terms) :
    evalTerms (evaluateWord (bdy Y))
      (l.map (relabel (tabulate (packetOrder p), tabulate (packetOrder p.symm)))) =
    evalTerms (evaluateWord (bdy (Y ∘ p))) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change _ + evalTerms _ _ = _ + evalTerms _ l
    rw [ih]
    simp only [relabel, tabulate_eq, evaluate_conjugate]
private theorem sum_eval_flat {D : Type*} (l : List D) (h : D → Terms) (f : Wire → ℂ) :
    evalTerms f (l.flatMap h) = (l.map fun d => evalTerms f (h d)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change evalTerms f (h a ++ l.flatMap h) = evalTerms f (h a) + _
    simpa [evalTerms] using congrArg (fun x => evalTerms f (h a) + x) ih

/-- Each of the six summands in the cyclic transfer is a genuine closure
of the correction on a reordered family of input vectors. -/
theorem cyclic_evaluation {D : Type*} [Fintype D] (Y : Family D) :
    evalTerms (evaluateWord (bdy Y)) cyclicTerms =
    ∑ p : Equiv.Perm (Fin 3), evalTerms (evaluateWord (bdy (Y ∘ p))) correctionTerms := by
  rw [cyclicTerms, sum_eval_flat, packetOrders, List.map_map, sum_permutations]
  apply Finset.sum_congr rfl
  intro p _
  exact eval_relabel Y p correctionTerms

private def readEquiv (D : Type*) : Words D ≃ (Fin 3 → Fin 2 → D) :=
  (slots.symm.arrowCongr (Equiv.refl D)).trans (Equiv.curry _ _ _)

private theorem bracket_bdy {D : Type*} [Fintype D] (Y Z : Family D) :
    bracket (bdy Y) (bdy Z) = ∏ i, bracket (Y i) (Z i) := by
  rw [← bracket_pureWord]
  unfold bracket
  apply Fintype.sum_equiv (readEquiv D)
  intro w
  rw [bdy_prod, bdy_prod]
  rfl

/-- Six whole-packet orders close to the Gram permanent of the three
arbitrary boundary vectors. -/
theorem whole_orders {D : Type*} [Fintype D] (Y : Family D) :
    ((packetOrders.map Prod.fst).map (evaluateWord (bdy Y))).sum = (crossGram Y Y).permanent := by
  simp only [packetOrders, List.map_map, Function.comp_def, tabulate_eq]
  rw [sum_permutations]
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro p _
  have h (w : Words D) : bdy Y (w ∘ packetOrder p) = bdy (Y ∘ p.symm) w := by
    rw [wire_lift]
    exact bdy_relabel Y p.symm w
  unfold evaluateWord
  simp only [h, bracket_bdy]
  apply Fintype.prod_equiv p.symm
  intro i
  simp [crossGram]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1800000 in
private theorem sum_evaluate {D : Type*} [Fintype D] (z : Words D → ℂ) :
    (allWires.map (evaluateWord z)).sum = 720 * bracket z (clasp z) := by
  unfold allWires
  rw [bind_pure_comp (fun p : Equiv.Perm (Fin 6) => (p : Wire)) (permutations 6)]
  simp only [List.map_eq_map, List.map_map]
  rw [sum_permutations]
  simp only [Function.comp_apply, tabulate_eq]
  unfold evaluateWord bracket
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.mul_sum]
  have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 6))) (fun p : Equiv.Perm (Fin 6) => z (w ∘ p))
  change (∑ p : Equiv.Perm (Fin 6), z (w ∘ p.symm)) = _ at h
  simp only [clasp, sumSlots, h, Fintype.card_fin]
  norm_num [Nat.factorial]
  ring

/-- All 720 thin-slot orders, evaluated on the normalized matrix packets,
give eight times the permanent of the original six-column Gram matrix. -/
theorem all_orders {D : Type*} [Fintype D] (x : Fin 3 → Fin 2 → D → ℂ) :
    (allWires.map (evaluateWord (bdy (fun i => packet (x i))))).sum =
      8*(crossGram (Function.uncurry x) (Function.uncurry x)).permanent := by
  have hb : bdy (fun i => packet (x i)) = (fun w => flatPackets x (w ∘ slots)) := by
    funext w; exact bdy_prod _ _
  rw [sum_evaluate, hb, Bridges.bracket_transport, ← bracket_clasp]
  have h := fine_closure x x
  norm_num [Nat.factorial] at h
  linear_combination 8*h

private theorem eval_weighted (f : Wire → ℂ) (c : ℤ) (l : List Wire) :
    evalTerms f (weightedWires c l) = (c : ℂ) * (l.map f).sum := by
  induction l with
  | nil => simp [evalTerms, weightedWires]
  | cons p l ih =>
    change (c : ℂ)*f p + evalTerms f (weightedWires c l) = (c : ℂ) * (f p + (l.map f).sum)
    rw [ih, mul_add]

/-- The integer coefficient target is exactly 288 times the permanent gap. -/
theorem target_eq_gap {D : Type*} [Fintype D] (x : Fin 3 → Fin 2 → D → ℂ) :
    evalTerms (evaluateWord (bdy (fun i => packet (x i)))) targetTerms =
    288 * ((crossGram (Function.uncurry x) (Function.uncurry x)).permanent -
      (crossGram (fun i => packet (x i)) (fun i => packet (x i))).permanent) := by
  have happ (f : Wire → ℂ) (l r : Terms) :
      evalTerms f (l++r) = evalTerms f l + evalTerms f r := by simp [evalTerms]
  rw [targetTerms, happ, eval_weighted, eval_weighted, all_orders, whole_orders]
  push_cast
  ring

/-- The second permanent in the target is the matrix of permanents of
the actual 2-by-2 blocks of the six-column Gram matrix. -/
theorem target_eq_matrix_gap {D : Type*} [Fintype D] (x : Fin 3 → Fin 2 → D → ℂ) :
    let A := crossGram (Function.uncurry x) (Function.uncurry x)
    evalTerms (evaluateWord (bdy (fun i => packet (x i)))) targetTerms =
      288 * (A.permanent - (blockPermanentMatrix A).permanent) := by
  dsimp only
  rw [target_eq_gap]
  congr 3
  ext i j
  exact packet_gram (x i) (x j)

/-- The coordinate closure comparison suffices even for singular input
matrices and zero packets. -/
theorem marcus_of_gram_positive
    (h : ∀ x : Fin 3 → Fin 2 → Fin 6 → ℂ,
      0 ≤ (evalTerms (evaluateWord (bdy (fun i => packet (x i)))) targetTerms).re) :
    MarcusAt 3 2 := by
  apply MatchingThreshold.marcusAt_of_gram
  intro x
  have hx := h x
  rw [target_eq_gap, ← Complex.ofReal_ofNat 288, Complex.mul_re,
    Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero, Complex.sub_re] at hx
  linarith

end
end BlockPermanents.ThreeEndpoint
