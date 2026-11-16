import BlockPermanents.FaceSampling
import BlockPermanents.FaceTrade
import BlockPermanents.FaceExit

/-! # Uniform four-face means

The role set distinguishes the spectator matching from the ordered active labels.
All injections of this set have the same mean under full relabeling.
-/
namespace BlockPermanents.FaceMeans
open FaceSampling CycleMatching Matchings Closures FaceExit
noncomputable section

abbrev Roles (r q : ℕ) := (Fin r × Fin 2) ⊕ Fin q

def positions {m r q : ℕ} (h : 2*r+q ≤ m) : Roles r q ↪ Fin m :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by
    simpa [Roles, Nat.mul_comm] using h))

variable {m d : ℕ}
abbrev Input (m d : ℕ) := Fin m → Fin d → ℂ

def weight (x : Input m d) {r q : ℕ} (v : Roles r q → Fin m) : ℝ :=
  ∏ i, Complex.normSq (bracket (x (v (.inl (i,0)))) (x (v (.inl (i,1)))))

def active (x : Input m d) {r q : ℕ} (v : Roles r q → Fin m) : Input q d :=
  fun i => x (v (.inr i))

/-- Weighted mean of any observable on the ordered active labels. -/
def mean (x : Input m d) (r q : ℕ) (F : Input q d → ℝ) : ℝ :=
  sample m (fun v : Roles r q → Fin m => weight x v * F (active x v))

theorem mean_mono (x : Input m d) {r q : ℕ} (fit : 2*r+q ≤ m)
    {F G : Input q d → ℝ}
    (h : ∀ v : Roles r q → Fin m, F (active x v) ≤ G (active x v)) :
    mean x r q F ≤ mean x r q G := by
  simp only [mean, sample_eq (positions fit)]
  exact average_le fun σ => mul_le_mul_of_nonneg_left (h _)
    (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _)

/-- Delete active spectator positions without changing the uniform distribution
on everything retained, including the separate marked edges. -/
theorem mean_restrict (x : Input m d) {r p q : ℕ} (fit : 2*r+q ≤ m) (e : Fin p ↪ Fin q)
    (F : Input p d → ℝ) :
    mean x r q (fun y => F (y ∘ e)) = mean x r p F := by
  exact restrict (Function.Embedding.sumMap (Function.Embedding.refl _) e) (positions fit)
    (fun v => weight x v * F (active x v))

/-- Averaged slack of the fixed four-set with its spectator matching. -/
def fourSlack (x : Input m d) (r : ℕ) :=
  mean x r 4 (fun y => FaceTrade.slack (crossGram y y))

theorem weighted_gain (x : Input m d) (unit : ∀ i, Bend.energy (x i) = 1)
    {r : ℕ} (fit : 2*r+4 ≤ m) {u : ℝ} (hu : 0 < u) :
    4*(1-u)*Z (crossGram x x) (r+1) + 4*(1-1/u)*Z (crossGram x x) (r+2) ≤ fourSlack x r := by
  let e := positions fit
  let p := Function.Embedding.inl.trans e
  let j := Function.Embedding.inr.trans e
  have hf (i : Fin 4) : j i ∉ Set.range p := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr (e.injective hk)
  have h := FaceTrade.weighted_trade x unit p j hf hu
  unfold fourSlack mean
  rw [sample_eq e]
  simpa only [Fintype.card_fin] using h

/-- The three chosen active labels produce the packet survivor D. -/
def triple (y : Input 3 d) := Bend.energy (survivor (y 0) (y 1) (y 2))

/-- Keep a fourth active label at the clasp. -/
def quadruple (y : Input 4 d) :=
  MatchingFine.fine ![survivor (y 0) (y 1) (y 2),y 3]

/-- The same pair of exits with all remaining active spectators. -/
def fullExit {n : ℕ} (y : Input (n+3) d) :=
  exitEnergy (y 0) (y (0 : Fin (n+2)).succ) (y (0 : Fin (n+1)).succ.succ)
    (fun i : Fin n => y i.succ.succ.succ)

theorem triple_face (x : Input m d) (schur : ∀ p q, SchurNormalization.HomogeneousSchur d p q)
    (unit : ∀ i, Bend.energy (x i) = 1) {n r : ℕ} (fit : 2*r+(n+3) ≤ m) :
    mean x r 3 triple ≤ mean x r (n+3) fullExit := by
  let e := Fin.castLEEmb (by omega : 3 ≤ n+3)
  rw [← mean_restrict x fit e triple]
  apply mean_mono x fit
  intro v
  exact keep_three schur _ _ _ _ (fun i => unit _)

theorem quadruple_face (x : Input m d) (schur : ∀ p q, SchurNormalization.HomogeneousSchur d p q)
    (unit : ∀ i, Bend.energy (x i) = 1) {n r : ℕ} (fit : 2*r+(n+4) ≤ m) :
    mean x r 4 quadruple ≤ mean x r (n+4) fullExit := by
  let e := Fin.castLEEmb (by omega : 4 ≤ n+4)
  rw [← mean_restrict x fit e quadruple]
  apply mean_mono x fit
  intro v
  let y := active x v
  have h := keep_four schur (y 0) (y (0 : Fin (n+3)).succ) (y (0 : Fin (n+2)).succ.succ)
    (y (0 : Fin (n+1)).succ.succ.succ) (fun i : Fin n => y i.succ.succ.succ.succ) (fun i => unit _)
  have he : (Fin.cons (y (0 : Fin (n+1)).succ.succ.succ) (fun i : Fin n => y i.succ.succ.succ.succ) :
      Fin (n+1) → Fin d → ℂ) = fun i => y i.succ.succ.succ := by
    funext i
    exact Fin.cases (by rw [Fin.cons_zero]) (fun j => by rw [Fin.cons_succ]) i
  rw [he] at h
  exact h

end
end BlockPermanents.FaceMeans
