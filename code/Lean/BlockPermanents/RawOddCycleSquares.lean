import BlockPermanents.ConsecutiveCycleSquares
import BlockPermanents.OddMatchingMass

/-! Lemma AB.1 in the unnormalized convention of (AB.2), with each
orientation of a cycle counted once and each matching counted once. -/
namespace BlockPermanents.RawCycleSquares
open CycleMatching CycleComposition CyclePolynomial CycleCuts ReflectedCycles Closures
noncomputable section

/-- The diagonal coefficient B in (AB.2), on all q labels. -/
def oddBudget {q : ℕ} (g : Gram q) (r : ℕ) (u : ℝ) : ℝ :=
  (2:ℝ)^(r-1) * r.factorial / (2*(r:ℝ)+1) *
    ((u + ((q-2*r : ℕ):ℝ)/u) * matchingMass g r +
      (2*((r:ℝ)+1)/u) * matchingMass g (r+1))

private theorem scale_first (a s : ℕ) (f z : ℝ) :
    (2:ℝ)^a * (a+1).factorial / (2*a+3) *
      (f / (2^(a+1) * ((a+1).factorial : ℝ) * (s+1).factorial) * z) =
    f / ((s.factorial : ℝ)*(2*a+3)) / (2*((s:ℝ)+1)) * z := by
  rw [pow_succ, Nat.factorial_succ s]
  push_cast
  field_simp
  ring

private theorem scale_second (a b : ℕ) (f z : ℝ) :
    (2:ℝ)^a * (a+1).factorial / (2*a+3) * (2*((a:ℝ)+2)) *
      (f / (2^(a+2) * ((a+2).factorial : ℝ) * b.factorial) * z) =
    f / (((b+1).factorial : ℝ)*(2*a+3)) * ((b:ℝ)+1)/2 * z := by
  rw [show a+2 = (a+1)+1 by omega, pow_succ, pow_succ,
    Nat.factorial_succ (a+1), Nat.factorial_succ b]
  push_cast
  field_simp
  ring

private theorem budget_eq {a s : ℕ} (g : Gram (2*a+3+s)) (hg : UnitGram g) (u : ℝ) (hu : 0 < u) :
    oddBudget g (a+1) u = ((classSet (2*a+3+s) {2*a+3}).card : ℝ) *
      ((u/((s:ℝ)+1)+1/u)/2 * Z g (a+1) + (s:ℝ)/(2*u) * Z g (a+2)) := by
  let c : ℝ := (classSet (2*a+3+s) {2*a+3}).card
  let p : ℝ := 2^a * (a+1).factorial / (2*(a:ℝ)+3)
  have hc : c = ((2*a+3+s).factorial : ℝ) / (s.factorial*(2*(a:ℝ)+3)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using single_count (2*a+3) s (by omega)
  have h₁ : p * matchingMass g (a+1) = c / (2*((s:ℝ)+1)) * Z g (a+1) := by
    rw [matchingMass_eq g hg _ (by omega), show 2*a+3+s-2*(a+1) = s+1 by omega, hc]
    exact scale_first .. 
  have h₂ : p * (2*((a:ℝ)+2)) * matchingMass g (a+2) = c * (s:ℝ)/2 * Z g (a+2) := by
    cases s with
    | zero => rw [matchingMass_outside _ _ (by omega)]; simp
    | succ b =>
      rw [matchingMass_eq g hg _ (by omega), show 2*a+3+(b+1)-2*(a+2) = b by omega, hc]
      simpa only [Nat.cast_succ] using scale_second a b ((2*a+3+(b+1)).factorial : ℝ) (Z g (a+2))
  unfold oddBudget
  rw [show a+1-1 = a by omega, show 2*a+3+s-2*(a+1) = s+1 by omega]
  push_cast
  rw [show 2*((a:ℝ)+1)+1 = 2*a+3 by ring, show (a:ℝ)+1+1 = a+2 by ring]
  change p * ((u+((s:ℝ)+1)/u)*matchingMass g (a+1) +
    (2*((a:ℝ)+2)/u)*matchingMass g (a+2)) = c * _
  calc
    _ = (u+((s:ℝ)+1)/u) * (p*matchingMass g (a+1)) +
          (p*(2*((a:ℝ)+2))*matchingMass g (a+2))/u := by ring
    _ = _ := by
      rw [h₁,h₂]
      field_simp
      ring

private theorem raw_consecutive {D : Type*} [Fintype D] (a s : ℕ)
    (x : Fin (2*a+3+s) → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) (u : ℝ) (hu : 0 < u) :
    let g := crossGram x x
    oddBudget g (a+1) u + sign plus * (classSum g {2*a+3}).re =
      ((classSet (2*a+3+s) {2*a+3}).card : ℝ) * oddRemainder a s x plus u := by
  let g := crossGram x x
  have hg : UnitGram g := by
    constructor
    · intro i; simp [g,crossGram,Coarse.bracket_self,unit]
    · intro i j; simp [g,crossGram,bracket,star_sum,star_mul',mul_comm]
    · intro i j; simpa [g,sqEdge,crossGram,unit] using FiveProjection.bracket_bound (x i) (x j)
  have hc := class_average g (localPerm (2*a+3) s)
  rw [localPerm_type _ _ (by omega)] at hc
  have h := odd_consecutive_squares a s x unit plus u hu
  dsimp only at h ⊢
  rw [budget_eq g hg u hu, ← h]
  rw [hc]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  ring

/-- The oriented cycle sum is real for the Gram matrix of unit packets. -/
theorem odd_cycle_real {D : Type*} [Fintype D] (q r : ℕ) (hr : 1 ≤ r) (hq : 2*r+1 ≤ q)
    (x : Fin q → D → ℂ) :
    let T := classSum (crossGram x x) {2*r+1}
    T = (T.re : ℂ) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hq
  let g := crossGram x x
  have hτ := class_average g (localPerm (2*r+1) s)
  rw [localPerm_type _ _ (by omega)] at hτ
  have hg (i j) : star (g i j) = g j i := by simp [g,crossGram,bracket,star_sum,star_mul',mul_comm]
  dsimp only
  rw [hτ, mean_real g hg]
  simp

/-- The residual of (AB.2) multiplied by the number of oriented cycles.
Its two contributions are the glued cycle half and the restored two-step
squares on its available middle labels. -/
def oddClassRemainder {q : ℕ} (r : ℕ) (hr : 1 ≤ r) (hq : 2*r+1 ≤ q)
    {D : Type*} [Fintype D] (x : Fin q → D → ℂ) (plus : Bool) (u : ℝ) : ℝ :=
  let a := r-1
  let s := q-(2*r+1)
  let eqsize : 2*a+3+s = q := by dsimp [a,s]; omega
  ((classSet q {2*r+1}).card : ℝ) *
    oddRemainder a s (x ∘ Fin.cast eqsize) plus u

theorem oddClassRemainder_nonneg {q r : ℕ} (hr : 1 ≤ r) (hq : 2*r+1 ≤ q)
    {D : Type*} [Fintype D] (x : Fin q → D → ℂ) (plus : Bool) (u : ℝ) (hu : 0 < u) :
    0 ≤ oddClassRemainder r hr hq x plus u := by
  exact mul_nonneg (Nat.cast_nonneg' _) (oddRemainder_nonneg _ _ _ _ _ hu)

private theorem cast_spare {D : Type*} [Fintype D] (a s t : ℕ) (hs : t = s)
    (x : Fin (2*a+3+s) → D → ℂ) (plus : Bool) (u : ℝ) :
    oddRemainder a t (x ∘ Fin.cast (show 2*a+3+t = 2*a+3+s by omega)) plus u =
      oddRemainder a s x plus u := by
  subst t
  rfl

/-- Lemma AB.1 with the two signs, the actual oriented cycle class sum and
the raw unordered matching sums of (AB.2). At q=2r+1 the last matching
sum is empty. -/
theorem odd_cycle_squares {q r : ℕ} (hr : 1 ≤ r) (hq : 2*r+1 ≤ q)
    {D : Type*} [Fintype D] (x : Fin q → D → ℂ) (unit : ∀ i, Bend.energy (x i) = 1)
    (plus : Bool) (u : ℝ) (hu : 0 < u) :
    oddBudget (crossGram x x) r u + sign plus * (classSum (crossGram x x) {2*r+1}).re =
      oddClassRemainder r hr hq x plus u := by
  cases r with
  | zero => omega
  | succ a =>
    have hq' : 2*a+3 ≤ q := by omega
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hq'
    have h := raw_consecutive a s x unit plus u hu
    dsimp only at h
    simp [oddClassRemainder, show 2*(a+1)+1 = 2*a+3 by omega]
    rw [cast_spare a s _ (by omega)]
    exact h

end
end BlockPermanents.RawCycleSquares
