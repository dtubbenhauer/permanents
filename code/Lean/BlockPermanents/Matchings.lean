import BlockPermanents.Threshold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin

/-! Homogeneous matching means. A matching with r edges has two distinguished
positions per edge and one position for each remaining label. Averaging over
bijections of these positions with the label set weights every matching equally. -/

namespace BlockPermanents.Matchings
open scoped BigOperators
noncomputable section

abbrev Shape (P S : Type*) := (P × Fin 2) ⊕ S

def weight {I P S : Type*} [Fintype P] [Fintype S] (v : I → ℝ) (p : I → I → ℝ)
    (f : Shape P S → I) : ℝ :=
  (∏ a : P, p (f (Sum.inl (a,0))) (f (Sum.inl (a,1)))) * ∏ a : S, v (f (Sum.inr a))

def average (m : ℕ) (f : Equiv.Perm (Fin m) → ℝ) : ℝ :=
  (m.factorial : ℝ)⁻¹ * ∑ σ, f σ

def moment (m r : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) : ℝ :=
  (m.factorial : ℝ)⁻¹ * ∑ e : Shape (Fin r) (Fin (m-2*r)) ≃ Fin m, weight v p e

private def shapeCongr {P S P' S' : Type*} (a : P ≃ P') (b : S ≃ S') :
    Shape P S ≃ Shape P' S' :=
  (a.prodCongr (Equiv.refl _)).sumCongr b

private theorem weight_reindex {I P S P' S' : Type*} [Fintype P] [Fintype S]
    [Fintype P'] [Fintype S'] (v : I → ℝ) (p : I → I → ℝ) (a : P ≃ P') (b : S ≃ S')
    (f : Shape P' S' → I) :
    weight v p (f ∘ shapeCongr a b) = weight v p f := by
  unfold weight
  congr 1
  · apply Fintype.prod_equiv a; intro i; rfl
  · apply Fintype.prod_equiv b; intro i; rfl

/-- Any fixed choice of disjoint ordered edges and unused labels realizes the
same matching mean when all m labels are permuted uniformly. -/
theorem average_weight_eq_moment {P S : Type*} [Fintype P] [Fintype S] {m r : ℕ}
    (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) (e : Shape P S ≃ Fin m)
    (hp : Fintype.card P = r) :
    average m (fun σ => weight v p (σ ∘ e)) = moment m r v p := by
  classical
  have hc := Fintype.card_congr e
  simp only [Shape, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hp] at hc
  let a : P ≃ Fin r := Fintype.equivOfCardEq (by simpa using hp)
  let b : S ≃ Fin (m-2*r) := Fintype.equivOfCardEq (by rw [Fintype.card_fin]; omega)
  let d := shapeCongr a b
  let g : Shape (Fin r) (Fin (m-2*r)) ≃ Fin m := d.symm.trans e
  unfold average moment
  congr 1
  apply Fintype.sum_equiv (Equiv.equivCongr g.symm (Equiv.refl _))
  intro σ
  rw [← weight_reindex v p a b (Equiv.equivCongr g.symm (Equiv.refl _) σ)]
  congr 1
  funext i
  simp [g, d, Function.comp_def]

theorem moment_nonneg {m r : ℕ} {v : Fin m → ℝ} {p : Fin m → Fin m → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i j, 0 ≤ p i j) : 0 ≤ moment m r v p := by
  unfold moment
  refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
  exact fun _ _ => mul_nonneg (Finset.prod_nonneg (fun _ _ => hp ..))
    (Finset.prod_nonneg (fun _ _ => hv _))

theorem average_const (m : ℕ) (a : ℝ) : average m (fun _ => a) = a := by
  simp [average, Fintype.card_perm, ← mul_assoc, Nat.factorial_ne_zero]

theorem average_le {m : ℕ} {f g : Equiv.Perm (Fin m) → ℝ}
    (h : ∀ σ, f σ ≤ g σ) : average m f ≤ average m g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => h σ)) (by positivity)


theorem average_add {m} (f g : Equiv.Perm (Fin m) → ℝ) :
    average m (fun σ => f σ + g σ) = average m f + average m g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_smul {m} (c : ℝ) (f : Equiv.Perm (Fin m) → ℝ) :
    average m (fun σ => c * f σ) = c * average m f := by
  simp only [average, ← Finset.mul_sum, mul_left_comm]

theorem average_sum {T : Type*} {m} (s : Finset T) (f : T → Equiv.Perm (Fin m) → ℝ) :
    average m (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, average m (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.mul_sum]

theorem moment_zero (m : ℕ) (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ) :
    moment m 0 v p = ∏ i, v i := by
  let e : Shape (Fin 0) (Fin m) ≃ Fin m := Equiv.emptySum _ _
  rw [← average_weight_eq_moment v p e (by simp : Fintype.card (Fin 0) = 0)]
  convert average_const m (∏ i, v i) using 2
  funext σ
  change (∏ _i : Fin 0, _) * (∏ a : Fin m, v (σ a)) = _
  simp [σ.prod_comp]

theorem pathCoeff_outside {m r : ℕ} (h : m < 2*r) : Threshold.pathCoeff m r = 0 := by
  match m, r with
  | _, 0 => omega
  | 0, r+1 | 1, r+1 => rfl
  | m+2, r+1 =>
    rw [Threshold.pathCoeff, pathCoeff_outside (m := m+1) (r := r+1) (by omega),
      pathCoeff_outside (m := m) (r := r) (by omega), mul_zero, add_zero]


private def addSingle {P S : Type*} : Shape P (Option S) ≃ Option (Shape P S) where
  toFun
    | .inl q => some (.inl q)
    | .inr none => none
    | .inr (some s) => some (.inr s)
  invFun
    | none => .inr none
    | some (.inl q) => .inl q
    | some (.inr s) => .inr (some s)
  left_inv x := by rcases x with q | (_ | s) <;> rfl
  right_inv x := by rcases x with _ | (q | s) <;> rfl

private def addEdge {P S : Type*} : Shape (Option P) S ≃ Fin 2 ⊕ Shape P S where
  toFun
    | .inl (none,j) => .inl j
    | .inl (some a,j) => .inr (.inl (a,j))
    | .inr s => .inr (.inr s)
  invFun
    | .inl j => .inl (none,j)
    | .inr (.inl (a,j)) => .inl (some a,j)
    | .inr (.inr s) => .inr s
  left_inv x := by rcases x with ⟨(_ | a), j⟩ | s <;> rfl
  right_inv x := by rcases x with j | (⟨a,j⟩ | s) <;> rfl

private def insertEdge (m : ℕ) (i : Fin (m+1)) : Fin 2 ⊕ Fin m ≃ Fin (m+2) :=
  ((finSumFinEquiv.trans (finCongr (Nat.add_comm 2 m))).trans (finSuccEquiv (m+1))).trans
    ((Equiv.optionCongr (Equiv.swap 0 i)).trans (finSuccEquiv (m+1)).symm)

private theorem insertEdge_zero (i : Fin (m+1)) :
    insertEdge m i (.inl 0) = 0 := by
  change (finSuccEquiv (m+1)).symm (Option.map (Equiv.swap 0 i) (finSuccEquiv (m+1) 0)) = _
  simp

private theorem insertEdge_one (i : Fin (m+1)) :
    insertEdge m i (.inl 1) = i.succ := by
  change (finSuccEquiv (m+1)).symm (Option.map (Equiv.swap 0 i)
    (finSuccEquiv (m+1) (0 : Fin (m+1)).succ)) = _
  rw [finSuccEquiv_succ]
  change (finSuccEquiv _).symm (some ((Equiv.swap 0 i) 0)) = _
  rw [Equiv.swap_apply_left, finSuccEquiv_symm_some]

private theorem insertEdge_tail (i : Fin (m+1)) (a : Fin m) :
    insertEdge m i (.inr a) = (Equiv.swap 0 i a.succ).succ := by
  have h : (finCongr (Nat.add_comm 2 m)) (finSumFinEquiv (Sum.inr a)) = a.succ.succ := by
    apply Fin.ext
    simp [finCongr]
  change (finSuccEquiv (m+1)).symm (Option.map (Equiv.swap 0 i)
    (finSuccEquiv (m+1) ((finCongr (Nat.add_comm 2 m)) (finSumFinEquiv (Sum.inr a))))) = _
  rw [h, finSuccEquiv_succ]
  exact finSuccEquiv_symm_some _

/-- Interchange the ambient permutation average with the average over
bijections on the undeleted labels. -/
private theorem average_insert {m l r j : ℕ} (hfit : 2*r ≤ l)
    (v : Fin m → ℝ) (p : Fin m → Fin m → ℝ)
    (c : Equiv.Perm (Fin m) → ℝ) (f : Fin l → Fin m)
    (h : ∀ e : Shape (Fin r) (Fin (l-2*r)) ≃ Fin l,
      average m (fun σ => c σ * weight v p (σ ∘ f ∘ e)) = moment m j v p) :
    average m (fun σ => c σ * moment l r (fun a => v (σ (f a))) (fun a b => p (σ (f a)) (σ (f b)))) =
    moment m j v p := by
  classical
  let T := Shape (Fin r) (Fin (l-2*r))
  have hT : Fintype.card T = l := by
    simp only [T, Shape, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  let e₀ : T ≃ Fin l := Fintype.equivOfCardEq (by simpa using hT)
  have hn : Fintype.card (T ≃ Fin l) = l.factorial := by rw [Fintype.card_equiv e₀, hT]
  have step (σ : Equiv.Perm (Fin m)) :
      c σ * moment l r (fun a => v (σ (f a))) (fun a b => p (σ (f a)) (σ (f b))) =
      (l.factorial : ℝ)⁻¹ * ∑ e : T ≃ Fin l, c σ * weight v p (σ ∘ f ∘ e) := by
    change c σ * ((l.factorial : ℝ)⁻¹ * ∑ e : T ≃ Fin l, weight v p (σ ∘ f ∘ e)) = _
    rw [← Finset.mul_sum, mul_left_comm]
  simp_rw [step]
  rw [average_smul, average_sum]
  have heq : (∑ i : T ≃ Fin l, average m fun σ => c σ * weight v p (σ ∘ f ∘ i)) =
      ∑ _i : T ≃ Fin l, moment m j v p := Finset.sum_congr rfl (fun i _ => h i)
  rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero l), one_mul]

set_option maxHeartbeats 1000000 in
theorem average_single {m r : ℕ} (v : Fin (m+1) → ℝ) (p : Fin (m+1) → Fin (m+1) → ℝ)
    (h : 2*r ≤ m) :
    average (m+1) (fun σ => v (σ 0) * moment m r (fun a => v (σ a.succ))
      (fun a b => p (σ a.succ) (σ b.succ))) = moment (m+1) r v p := by
  apply average_insert (m := m+1) (l := m) (r := r) (j := r) h v p (fun σ => v (σ 0)) Fin.succ
  intro e
  let g := addSingle.trans ((Equiv.optionCongr e).trans (finSuccEquiv m).symm)
  rw [← average_weight_eq_moment v p g (Fintype.card_fin r)]
  congr 1
  funext σ
  have gpair (a : Fin r) (j : Fin 2) : g (.inl (a,j)) = (e (.inl (a,j))).succ :=
    finSuccEquiv_symm_some _
  have gnone : g (.inr none) = 0 := finSuccEquiv_symm_none
  have gsome (s : Fin (m-2*r)) : g (.inr (some s)) = (e (.inr s)).succ :=
    finSuccEquiv_symm_some _
  simp only [weight, Fintype.prod_option, Function.comp_apply, gpair, gnone, gsome]
  ring

set_option maxHeartbeats 1000000 in
theorem average_pair {m r : ℕ} (v : Fin (m+2) → ℝ) (p : Fin (m+2) → Fin (m+2) → ℝ)
    (i : Fin (m+1)) (h : 2*r ≤ m) :
    average (m+2) (fun σ => p (σ 0) (σ i.succ) *
      moment m r (fun a => v (σ ((Equiv.swap 0 i a.succ).succ)))
        (fun a b => p (σ ((Equiv.swap 0 i a.succ).succ)) (σ ((Equiv.swap 0 i b.succ).succ)))) =
      moment (m+2) (r+1) v p := by
  apply average_insert (m := m+2) (l := m) (r := r) (j := r+1) h v p (fun σ => p (σ 0) (σ i.succ)) (fun a => (Equiv.swap 0 i a.succ).succ)
  intro e
  let g := addEdge.trans (((Equiv.refl (Fin 2)).sumCongr e).trans (insertEdge m i))
  rw [← average_weight_eq_moment v p g (by simp : Fintype.card (Option (Fin r)) = r+1)]
  congr 1
  funext σ
  have gzero : g (.inl (none,0)) = 0 := insertEdge_zero i
  have gone : g (.inl (none,1)) = i.succ := insertEdge_one i
  have gpair (a : Fin r) (j : Fin 2) : g (.inl (some a,j)) = (Equiv.swap 0 i (e (.inl (a,j))).succ).succ :=
    insertEdge_tail i _
  have gsing (s : Fin (m-2*r)) : g (.inr s) = (Equiv.swap 0 i (e (.inr s)).succ).succ :=
    insertEdge_tail i _
  simp only [weight, Fintype.prod_option, Function.comp_apply, gzero, gone, gpair, gsing, mul_assoc]

end
end BlockPermanents.Matchings
