import BlockPermanents.RoutedGluing

/-! # Intersection form of routed caps with internal permutation clasps -/
namespace BlockPermanents.RoutedTrace
open Equiv Finset
open scoped BigOperators
noncomputable section

variable {I D A B : Type*} [DecidableEq D] [Fintype A] [Fintype B]

private theorem contract_sum (S : Finset D) (r : ℕ) (c : A → ℂ)
    (x : A → (Cable I r → D) → Mark S r → ℂ) :
    contract S r (fun v d => ∑ i,c i*x i v d) = fun w => ∑ i,c i*contract S r (x i) w := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change contract S r (fun v a => ∑ b : S, ∑ i, c i*x i (extendWord v b.val) (a,b)) = _
    have h (v : Cable I r → D) (a : Mark S r) :
        (∑ b : S, ∑ i, c i*x i (extendWord v b.val) (a,b)) =
          ∑ i,c i*(∑ b : S,x i (extendWord v b.val) (a,b)) := by
      rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    simp_rw [h]
    exact ih _

def capAverage (S : Finset D) (r : ℕ) (p : A → Perm (Cable I r)) (a : A → ℚ)
    (x : (Cable I r → D) → Mark S r → ℂ) : Tensor I D :=
  fun w => ∑ i,(a i : ℂ)*routedCap S r (p i) x w

def reflectedAverage (S : Finset D) (r : ℕ) (q : B → Perm (Cable I r)) (b : B → ℚ)
    (f : Tensor I D) (v : Cable I r → D) (c : Mark S r) :=
  ∑ i,(b i : ℂ)*reflectedCap S r (q i) f v c

theorem glued_average (S : Finset D) (r : ℕ) (p : A → Perm (Cable I r))
    (q : B → Perm (Cable I r)) (a : A → ℚ) (b : B → ℚ) (f : Tensor I D) :
    capAverage S r p a (reflectedAverage S r q b f) =
      fun w => ∑ i, (a i : ℂ) * ∑ t, (b t : ℂ) * routedCap S r (p i) (reflectedCap S r (q t) f) w := by
  funext w
  unfold capAverage routedCap reflectedAverage
  simp_rw [contract_sum]

theorem clasp_sum {d N : ℕ} (c : A → ℂ) (f : A → Bend.Word d N → ℂ) :
    Closures.clasp (fun w => ∑ i,c i*f i w) = fun w => ∑ i,c i*Closures.clasp (f i) w := by
  funext w
  simp only [Closures.clasp,Closures.sumSlots]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

/-- Section 4B. Each choice of the internal permutations contributes its
rational clasp weight and one supported loop/occupation monomial. The
loop and path counts are uniform in the ambient dimension and support. -/
theorem intersection_form {d N : ℕ} (r : ℕ) (p : A → Perm (Cable (Fin N) r))
    (q : B → Perm (Cable (Fin N) r)) (a : A → ℚ) (b : B → ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ t, 0 ≤ b t) :
    ∃ j k : A → B → ℕ, (∀ i t,k i t ≤ N ∧ j i t+k i t ≤ r ∧ 0≤a i*b t) ∧
      ∀ (S : Finset (Fin d)) (f : Bend.Word d N → ℂ), Bend.Symmetric f → ∀ w,
      Closures.clasp (capAverage S r p a (reflectedAverage S r q b f)) w =
        (∑ i, ∑ t, ((a i*b t : ℚ):ℂ) * (S.card : ℂ)^(j i t) *
          (((occupied S w).card.choose (k i t) : ℕ) : ℂ)/(N.choose (k i t) : ℂ)) * f w := by
  choose j k hN hr hs using fun i t => cap_sector (d:=d) r (p i) (q t)
  refine ⟨j,k,fun i t => ⟨hN i t,hr i t,mul_nonneg (ha i) (hb t)⟩,?_⟩
  intro S f hf w
  rw [glued_average,clasp_sum]
  dsimp only
  simp_rw [clasp_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [hs i t S f hf w]
  push_cast
  ring

end
end BlockPermanents.RoutedTrace
