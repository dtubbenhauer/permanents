import BlockPermanents.WholeEdges
import BlockPermanents.MarkedAverage

/-! The whole-edge polynomial on the actual thin permutations of quadratic
packets. Both the routing weights and the split ends are computed from the
permutation of the 2m strand slots. -/
namespace BlockPermanents.MarkedEdges
open scoped BigOperators
open WholeEdges Negative
noncomputable section

abbrev Thin (m k : ℕ) := Equiv.Perm (Fin m × Fin k)

/-- The i-th input packet runs as a whole into the j-th output packet. -/
def whole {m k : ℕ} (σ : Thin m k) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => ∀ t, (σ (e.1,t)).1 = e.2)

theorem whole_iff {m k : ℕ} (σ : Thin m k) (i j : Fin m) :
    (i,j) ∈ whole σ ↔ ∀ t, (σ (i,t)).1 = j := by simp [whole]

private theorem reverse_whole {m k : ℕ} (σ : Thin m k) {i j : Fin m} (h : (i,j) ∈ whole σ) :
    (j,i) ∈ whole σ.symm := by
  have he := (whole_iff σ i j).mp h
  let f : Fin k → Fin k := fun t => (σ (i,t)).2
  have hf : Function.Injective f := by
    intro u v huv
    have hp : σ (i,u) = σ (i,v) := Prod.ext ((he u).trans (he v).symm) huv
    exact congrArg Prod.snd (σ.injective hp)
  rw [whole_iff]
  intro t
  obtain ⟨u,hu⟩ := Finite.surjective_of_injective hf t
  have hp : σ (i,u) = (j,t) := Prod.ext (he u) hu
  rw [← hp, σ.symm_apply_apply]

private theorem same_input {m k : ℕ} (hk : 0 < k) {σ : Thin m k} {i j j' : Fin m}
    (hj : (i,j) ∈ whole σ) (hj' : (i,j') ∈ whole σ) : j = j' :=
  ((whole_iff σ i j).mp hj ⟨0,hk⟩).symm.trans ((whole_iff σ i j').mp hj' ⟨0,hk⟩)

private theorem same_output {m k : ℕ} (hk : 0 < k) {σ : Thin m k} {i i' j : Fin m}
    (hi : (i,j) ∈ whole σ) (hi' : (i',j) ∈ whole σ) : i = i' :=
  same_input hk (reverse_whole σ hi) (reverse_whole σ hi')

private theorem whole_card {m k : ℕ} (hk : 0 < k) (σ : Thin m k) : (whole σ).card ≤ m := by
  have hin : Set.InjOn Prod.fst (↑(whole σ) : Set (Fin m × Fin m)) := by
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hc h
    dsimp at h
    subst c
    exact Prod.ext rfl (same_input hk ha hc)
  have hh := ((whole σ).image Prod.fst).card_le_univ
  simpa only [Finset.card_image_of_injOn hin, Fintype.card_fin] using hh

/-- One for each marked endpoint contained in a prescribed edge. An edge
from t to itself accounts for both boundary marks. -/
def ends {m : ℕ} (t : Fin m) (e : Fin m × Fin m) : ℚ :=
  (if e.1=t then 1 else 0) + (if e.2=t then 1 else 0)

private theorem sum_indicator {I J : Type*} [DecidableEq J] (s : Finset I) (f : I → J) (t : J)
    (hi : Set.InjOn f (↑s : Set I)) :
    (∑ e ∈ s, (if f e = t then 1 else 0 : ℚ)) = if t ∈ s.image f then 1 else 0 := by
  classical
  rw [← Finset.sum_image (f := fun i => if i=t then (1:ℚ) else 0) hi]
  simp

/-- The two ends independently split or run whole. -/
def splitEnds {m k : ℕ} (σ : Thin m k) (t : Fin m) : ℚ :=
  (if t ∈ (whole σ).image Prod.fst then 0 else 1) + (if t ∈ (whole σ).image Prod.snd then 0 else 1)

theorem split_count {m k : ℕ} (hk : 0 < k) (σ : Thin m k) (t : Fin m) :
    2 - ∑ e ∈ whole σ, ends t e = splitEnds σ t := by
  have hin : Set.InjOn Prod.fst (↑(whole σ) : Set (Fin m × Fin m)) := by
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hc h; dsimp at h; subst c
    exact Prod.ext rfl (same_input hk ha hc)
  have hout : Set.InjOn Prod.snd (↑(whole σ) : Set (Fin m × Fin m)) := by
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hc h; dsimp at h; subst d
    exact Prod.ext (same_output hk ha hc) rfl
  simp only [ends, Finset.sum_add_distrib, sum_indicator _ _ _ hin, sum_indicator _ _ _ hout, splitEnds]
  split_ifs <;> norm_num

private def flatten {m : ℕ} (x : Fin m → Quad) :
    Fin m × Fin 2 ≃ Fin (2*(List.ofFn x).length) :=
  finProdFinEquiv.trans (finCongr (by simp [Nat.mul_comm]))

def mixedWord {d : ℕ} (x y : Finset (Fin d) → ℚ) (σ : Equiv.Perm (Fin d)) : ℚ :=
  ∑ w, x w * y (w.map σ.toEmbedding)

/-- Expand both packet products in orthonormal word coordinates and
contract along the chosen thin-slot permutation. The fine prefactor
divides by 2^m. Slots of the same quadratic are adjacent under flatten. -/
def routeWeight {m : ℕ} (x y : Fin m → Quad) (σ : Thin m 2) : ℚ :=
  let d := 2*(List.ofFn x).length
  mixedWord (Occupation.packetWordVector d (List.ofFn x))
    (Occupation.packetWordVector d (List.ofFn y)) ((flatten x).permCongr σ) / 2^m

private theorem average_invariant {d : ℕ} (x : Finset (Fin d) → ℚ) (w : Finset (Fin d))
    (σ : Equiv.Perm (Fin d)) : Occupation.permSum x (w.map σ.toEmbedding) = Occupation.permSum x w := by
  unfold Occupation.permSum
  simp only [Finset.map_map]
  exact Equiv.sum_comp (Equiv.mulRight σ) (fun τ : Equiv.Perm (Fin d) => x (w.map τ.toEmbedding))

theorem sum_words {d : ℕ} (x y : Finset (Fin d) → ℚ) :
    (d.factorial : ℚ) * Occupation.wordPair
      (fun w => Occupation.permSum x w / d.factorial)
      (fun w => Occupation.permSum y w / d.factorial) =
    ∑ σ, mixedWord x y σ := by
  let py (w : Finset (Fin d)) := Occupation.permSum y w / d.factorial
  let h := fun (σ : Equiv.Perm (Fin d)) =>
    σ.finsetCongr.sum_comp (fun w => x w * py w)
  have hi (σ : Equiv.Perm (Fin d)) : ∑ w, x (w.map σ.toEmbedding) * py w = ∑ w, x w * py w := by
    convert h σ using 1
    apply Finset.sum_congr rfl
    intro w _
    simp [py, Equiv.finsetCongr_apply, average_invariant]
  have hf : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold Occupation.wordPair
  rw [Finset.powerset_univ, Finset.mul_sum]
  change (∑ w, (d.factorial : ℚ) * (Occupation.permSum x w / d.factorial * py w)) = _
  simp only [← mul_assoc]
  have hcancel (a : ℚ) : (d.factorial : ℚ) * (a / d.factorial) = a := by field_simp
  simp_rw [hcancel]
  unfold Occupation.permSum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  unfold py
  simp_rw [mul_left_comm (d.factorial : ℚ) (x _), hcancel]
  simp only [Occupation.permSum, mixedWord, Finset.mul_sum]
  exact Finset.sum_comm

/-- Summing the concrete routing weights over every thin permutation
reproduces the fine closure for arbitrary bra and ket quadratics. -/
theorem fine_routes {m : ℕ} (x y : Fin m → Quad) :
    Negative.fine (List.ofFn x) (List.ofFn y) = ∑ σ, routeWeight x y σ := by
  rw [Occupation.fine_eq_symmetrized_tensor _ _ (by simp)]
  rw [sum_words]
  unfold routeWeight
  rw [← Finset.sum_div]
  have h := (flatten x).permCongr.sum_comp (fun σ => mixedWord
    (Occupation.packetWordVector _ (List.ofFn x)) (Occupation.packetWordVector _ (List.ofFn y)) σ)
  rw [h]; congr 2; exact List.length_ofFn

/-- The polynomial built from forced whole-edge closures recovers the marked
sum over actual strand permutations. The sum is over split routings only. -/
theorem quadratic_readout {m : ℕ} (x y : Fin m → Quad) (t : Fin m) :
    ∑ h ∈ Finset.range m, (m : ℚ)/(2*(m-h : ℕ)) *
      (certificate (whole (m:=m) (k:=2)) (routeWeight x y) (ends t)).coeff h =
    ∑ σ : Thin m 2, if (whole σ).card < m then
      (m : ℚ)/(2*(m-(whole σ).card : ℕ)) * routeWeight x y σ * splitEnds σ t else 0 := by
  rw [marked_readout]
  simp_rw [split_count (by decide : 0 < 2)]

end
end BlockPermanents.MarkedEdges
