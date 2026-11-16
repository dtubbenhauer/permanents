import BlockPermanents.RoutedCables

/-! Route counts depend only on the slot permutations. The same witnesses
evaluate all ambient dimensions, support ranks and occupation sectors. -/
namespace BlockPermanents.RoutedUniform
open Equiv Finset RoutedTrace Closures Bend
noncomputable section

variable {I : Type*} [DecidableEq I]

open private close_scale count_step from BlockPermanents.RoutedTrace in
theorem follow (r : ℕ) (p : Perm (Cable I r)) (M : Finset (Cable I r)) :
    ∃ (j : ℕ) (q : Finset I) (u : Perm I), j+q.card ≤ r+M.card ∧
      ∀ (d : ℕ) (S : Finset (Fin d)), close S r (wire S p M) =
        fun f w => (S.card : ℂ)^j * wire S u q f w := by
  induction r with
  | zero => exact ⟨0,M,p,by simp,fun _ _ => by funext f w; simp [close]⟩
  | succ r ih =>
    obtain ⟨j,q,u,hq,he⟩ := ih p.removeNone (nextMarks p M)
    let e := if p none=none then 1 else 0
    have hn : e+(nextMarks p M).card ≤ M.card+1 := count_step p M
    refine ⟨e+j,q,u,by omega,?_⟩
    intro d S
    change close S r (trace S (wire S p M)) = _
    rw [trace_wire,close_scale,he d S]
    funext f w
    change (S.card : ℂ)^e*((S.card : ℂ)^j * wire S u q f w) = (S.card : ℂ)^(e+j)*_
    rw [pow_add,mul_assoc]


open private clasp_scale from BlockPermanents.RoutedSector in
theorem sector_monomial {N : ℕ} (r : ℕ) (p : Perm (Cable (Fin N) r)) :
    ∃ (j q : ℕ), q ≤ N ∧ j+q ≤ r ∧
      ∀ (d : ℕ) (S : Finset (Fin d)) (f : Word d N → ℂ), Symmetric f → ∀ w,
        clasp (close S r (wire S p ∅) f) w =
          (S.card : ℂ)^j * (((occupied S w).card.choose q : ℕ) : ℂ) /
            (N.choose q : ℂ) * f w := by
  obtain ⟨j,M,u,h,he⟩ := RoutedUniform.follow r p ∅
  refine ⟨j,M.card,by simpa using M.card_le_univ,by simpa using h,?_⟩
  intro d S f hf w
  rw [he d S,clasp_scale]
  dsimp only
  rw [clasp_wire S u M hf w]
  ring


theorem cap_sector {N : ℕ} (r : ℕ) (p q : Perm (Cable (Fin N) r)) :
    ∃ j t : ℕ, t≤N ∧ j+t≤r ∧
      ∀ (d : ℕ) (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
        Closures.clasp (routedCap S r p (reflectedCap S r q f)) w =
          (S.card : ℂ)^j * (((occupied S w).card.choose t : ℕ) : ℂ) /
            (N.choose t : ℂ) * f w := by
  simpa only [glued] using RoutedUniform.sector_monomial r (q.symm.trans p)


variable {A B : Type*} [Fintype A] [Fintype B]

theorem intersection_form {N : ℕ} (r : ℕ) (p : A → Perm (Cable (Fin N) r))
    (q : B → Perm (Cable (Fin N) r)) (a : A → ℚ) (b : B → ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ t, 0 ≤ b t) :
    ∃ j k : A → B → ℕ, (∀ i t,k i t ≤ N ∧ j i t+k i t ≤ r ∧ 0≤a i*b t) ∧
      ∀ (d : ℕ) (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
      Closures.clasp (capAverage S r p a (reflectedAverage S r q b f)) w =
        (∑ i, ∑ t, ((a i*b t : ℚ):ℂ) * (S.card : ℂ)^(j i t) *
          (((occupied S w).card.choose (k i t) : ℕ) : ℂ)/(N.choose (k i t) : ℂ)) * f w := by
  choose j k hN hr hs using fun i t => RoutedUniform.cap_sector r (p i) (q t)
  refine ⟨j,k,fun i t => ⟨hN i t,hr i t,mul_nonneg (ha i) (hb t)⟩,?_⟩
  intro d S f hf w
  rw [glued_average,clasp_sum]
  dsimp only
  simp_rw [clasp_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [hs i t d S f hf w]
  push_cast
  ring


variable {H : Type*} [Fintype H] [DecidableEq H]

theorem clasped_intersection {N r : ℕ} (lengths : H → ℕ) (base L K : Layout lengths N r)
    (markSplit : Cable (Fin N) r ≃ Fin N ⊕ Fin r) :
    let P := wiring lengths base L markSplit
    let Q := wiring lengths base K markSplit
    let wt := @claspWeight H _ _ r lengths
    ∃ j k : _ → _ → ℕ, (∀ i t,k i t ≤ N ∧ j i t+k i t ≤ r ∧ 0≤wt i*wt t) ∧
      ∀ (d : ℕ) (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
      Closures.clasp (capAverage S r P wt (reflectedAverage S r Q wt f)) w =
        (∑ i, ∑ t, ((wt i*wt t : ℚ):ℂ) * (S.card : ℂ)^(j i t) *
          (((occupied S w).card.choose (k i t) : ℕ) : ℂ)/(N.choose (k i t) : ℂ)) * f w := by
  apply RoutedUniform.intersection_form
  all_goals intro g; unfold claspWeight; positivity


end
end BlockPermanents.RoutedUniform
