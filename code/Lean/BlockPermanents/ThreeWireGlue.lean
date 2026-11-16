import BlockPermanents.ThreePos

/-! # Adjoint wire lists in the finite six-slot certificate -/
namespace BlockPermanents.ThreeWireGlue
open ThreeWire ThreePos Closures Bend
open scoped BigOperators
noncomputable section

/-- A wiring of the four upright slots fixes the two coordinates of the mark. -/
def upright (p : Wire) : Prop :=
  (∀ i : Fin 6, i.val < 4 → (p i).val < 4) ∧ p 4 = 4 ∧ p 5 = 5

/-- The wires admit permutation representatives with inverse-invariant sum.
This formulation accommodates multiplicities without testing function-valued
lists by exhaustive enumeration. -/
def valid (l : List Wire) : Prop :=
  (∀ p ∈ l, upright p) ∧ ∃ P : List (Equiv.Perm (Fin 6)),
    l = P.map (fun e : Equiv.Perm (Fin 6) => (e : Wire)) ∧
      ∀ f : Wire → ℂ, (P.map fun e => f e.symm).sum = (l.map f).sum

private def pairPerm : Equiv.Perm (Fin 6) :=
  ⟨packetSwap, packetSwap, by decide, by decide⟩

theorem valid_pair : valid pairList := by
  constructor
  · intro p hp
    simp only [pairList, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl <;> unfold upright <;> decide
  · exact ⟨[Equiv.refl _,pairPerm],rfl,fun _ => rfl⟩

private def liftFour (p : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).permCongr (p.sumCongr (Equiv.refl _))

private theorem liftFour_wire (p : Equiv.Perm (Fin 4)) : (liftFour p : Wire) = uprightFour p := by
  funext i
  fin_cases i <;> rfl

private theorem four_upright (p : Equiv.Perm (Fin 4)) : upright (uprightFour p) := by
  refine ⟨?_,rfl,rfl⟩
  intro i hi
  fin_cases i <;> first | exact (p _).isLt | contradiction

theorem valid_four : valid fourList := by
  constructor
  · intro q hq
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
    exact four_upright p
  · refine ⟨(permutations 4).map liftFour, ?_, ?_⟩
    · simp only [fourList, List.map_map, Function.comp_def, liftFour_wire]
    · intro f
      simp only [fourList, List.map_map, Function.comp_def]
      have h (p : Equiv.Perm (Fin 4)) : ((liftFour p).symm : Wire) = uprightFour p.symm :=
        liftFour_wire p.symm
      simp only [h, sum_permutations]
      exact inv_involutive.bijective.sum_comp (fun p => f (uprightFour p))

def shift {D : Type*} (z : Words D → ℂ) (p : Wire) (w : Words D) := z (w ∘ p)
def act {D : Type*} (l : List Wire) (z : Words D → ℂ) (w : Words D) :=
  (l.map (fun p => shift z p w)).sum

private theorem bracket_list_left {A B : Type*} [Fintype B] (l : List A) (f : A → B → ℂ) (v : B → ℂ) :
    bracket (fun w => (l.map (fun p => f p w)).sum) v = (l.map (fun p => bracket (f p) v)).sum := by
  induction l with
  | nil => simp [bracket]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    simp [bracket, add_mul, Finset.sum_add_distrib]

private theorem bracket_list_right {A B : Type*} [Fintype B] (l : List A) (v : B → ℂ) (f : A → B → ℂ) :
    bracket v (fun w => (l.map (fun p => f p w)).sum) = (l.map (fun p => bracket v (f p))).sum := by
  induction l with
  | nil => simp [bracket]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    simp [bracket, mul_add, Finset.sum_add_distrib]

private theorem shift_adjoint {D : Type*} [Fintype D] (z v : Words D → ℂ) (e : Equiv.Perm (Fin 6)) :
    bracket (shift z e) v = bracket z (shift v e.symm) := by
  unfold bracket
  apply Fintype.sum_equiv (e.symm.arrowCongr (Equiv.refl D))
  intro w
  change _ = (starRingEnd ℂ) (z (w ∘ e)) * v ((w ∘ e) ∘ e.symm)
  simp [shift,Function.comp_assoc]

theorem act_adjoint {D : Type*} [Fintype D] {l : List Wire} (hl : valid l) (z v : Words D → ℂ) :
    bracket (act l z) v = bracket z (act l v) := by
  obtain ⟨P, he, hp⟩ := hl.2
  unfold act
  rw [bracket_list_left, bracket_list_right]
  conv_lhs => rw [he, List.map_map]
  simp only [Function.comp_def, shift_adjoint]
  exact hp (fun p => bracket z (shift v p))

/-- Gluing the lists evaluates the form on one superposition from each list. -/
theorem glue_bracket {D : Type*} [Fintype D] (z : Words D → ℂ) (l : List Wire) (hl : valid l)
    (s : Wire) (r : List Wire) :
    glue (evaluateWord z) l s r = bracket (act l z) (shift (act r z) s) := by
  rw [act_adjoint hl]
  unfold act shift glue
  rw [bracket_list_right]
  congr 1
  apply List.map_congr_left; intro a _
  rw [bracket_list_right]
  rfl

/-- The superposition on the four upright slots, independent of the mark. -/
def upperTensor {d : ℕ} (l : List Wire) (F G : W d → ℂ) (t u : W d) : ℂ :=
  act l (boundary F G (fun _ => 1)) (tripleWords d (t,u,t))

private theorem unchanged_top {d : ℕ} (t u h : W d) (i : Fin 6) (hi : i.val < 4) :
    tripleWords d (t,u,h) i = tripleWords d (t,u,t) i := by
  fin_cases i <;> first | rfl | contradiction

private theorem list_product_right {A : Type*} (l : List A) (f : A → ℂ) (a : ℂ) :
    (l.map f).sum * a = (l.map (fun p => f p * a)).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [add_mul, ih]

theorem act_boundary {d : ℕ} {l : List Wire} (hl : valid l) (F G H : W d → ℂ) :
    act l (boundary F G H) = markedProduct (upperTensor l F G) H := by
  funext w
  obtain ⟨⟨t,u,h⟩, rfl⟩ := (tripleWords d).surjective w
  simp only [markedProduct, Equiv.symm_apply_apply, upperTensor, act, list_product_right]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hv := hl.1 p hp
  have he (i : Fin 6) (hi : i.val < 4) : tripleWords d (t,u,h) (p i) = tripleWords d (t,u,t) (p i) :=
    unchanged_top t u h _ (hv.1 i hi)
  simp only [shift, boundary, Function.comp_apply, he 0 (by decide), he 1 (by decide),
    he 2 (by decide), he 3 (by decide), hv.2.1, hv.2.2, mul_one]
  congr 2
  funext i; fin_cases i <;> rfl

theorem act_pair {d : ℕ} (F G H : W d → ℂ) :
    act pairList (boundary F G H) = markedProduct (pairTensor F G) H := by
  funext w
  simp [act, pairList, shift, identity, boundary, packetSwap, markedProduct, tripleWords, pairTensor,
    Function.comp_def]
  ring

/-- The three-packet supported estimate in the unnormalized diagram-list convention. -/
theorem pair_estimate {d : ℕ} (F G : W d → ℂ) (x : Fin 2 → Fin d → ℂ)
    (hF : Bend.Symmetric F) (hG : Bend.Symmetric G) :
    let f := evaluateWord (boundary F G (packet x))
    0 ≤ 8 * (glue f pairList thinSwap pairList).re -
      (9/4:ℝ) * (glue f pairList fullSwap pairList).re := by
  dsimp only
  simp only [glue_bracket _ _ valid_pair, act_pair]
  exact pair_absorbs_full F G x hF hG

/-- Any self-adjoint superposition of upright relabelings can be inserted
on both sides of the thin exchange, including the 24 four-slot wirings. -/
theorem thin_positive {d : ℕ} (F G H : W d → ℂ) (l : List Wire) (hl : valid l) :
    0 ≤ (glue (evaluateWord (boundary F G H)) l thinSwap l).re := by
  rw [glue_bracket _ _ hl, act_boundary hl]
  exact exchange_nonneg _ _ half _ (thin_action d)

/-- The signed difference of two upright lists on either side of the full
interchange closes to a sum of squares, with both mixed terms retained. -/
theorem full_difference_positive {d : ℕ} (F G H : W d → ℂ) (l r : List Wire) (hl : valid l) (hr : valid r) :
    let f := evaluateWord (boundary F G H)
    0 ≤ (glue f l fullSwap l - glue f l fullSwap r - glue f r fullSwap l + glue f r fullSwap r).re := by
  dsimp only
  simp only [glue_bracket _ _ hl, glue_bracket _ _ hr, act_boundary hl, act_boundary hr]
  let U := upperTensor l F G
  let V := upperTensor r F G
  let UV := fun t u => U t u - V t u
  have h := exchange_nonneg UV H full _ (full_action d)
  have he : evaluateWord (markedProduct UV H) fullSwap =
    bracket (markedProduct U H) (shift (markedProduct U H) fullSwap) -
    bracket (markedProduct U H) (shift (markedProduct V H) fullSwap) -
    bracket (markedProduct V H) (shift (markedProduct U H) fullSwap) +
    bracket (markedProduct V H) (shift (markedProduct V H) fullSwap) := by
    simp only [evaluateWord, bracket, shift, markedProduct, UV, sub_mul, map_sub, mul_sub,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel
  rw [he] at h
  exact h

end
end BlockPermanents.ThreeWireGlue
