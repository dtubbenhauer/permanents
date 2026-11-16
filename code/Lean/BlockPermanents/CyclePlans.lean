import BlockPermanents.CycleSmall
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! # Cycle partitions and their reflected-cut polynomials -/
namespace BlockPermanents.CyclePlans
open CycleMatching CycleComposition CyclePolynomial CycleCuts CycleSmall
noncomputable section

theorem split_type {a b m : ℕ} (e : Fin a ⊕ Fin b ≃ Fin m) (p : S a) (q : S b) :
    (splitPerm e p q).cycleType = p.cycleType + q.cycleType := by
  classical
  let L : Fin a ↪ Fin m := Function.Embedding.inl.trans e.toEmbedding
  let R : Fin b ↪ Fin m := Function.Embedding.inr.trans e.toEmbedding
  have ln (i : Fin b) : R i ∉ Set.range L := by
    rintro ⟨j,h⟩
    exact Sum.inl_ne_inr (e.injective h)
  have rn (i : Fin a) : L i ∉ Set.range R := by
    rintro ⟨j,h⟩
    exact Sum.inr_ne_inl (e.injective h)
  have h : splitPerm e p q = p.viaEmbedding L * q.viaEmbedding R := by
    apply Equiv.ext
    intro i
    obtain ⟨(j | j),rfl⟩ := e.surjective i
    · change _ = p.viaEmbedding L (q.viaEmbedding R (L j))
      rw [Equiv.Perm.viaEmbedding_apply_of_not_mem _ _ _ (rn j), Equiv.Perm.viaEmbedding_apply]
      simp [splitPerm,L]
    · change _ = p.viaEmbedding L (q.viaEmbedding R (R j))
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply_of_not_mem _ _ _ (ln (q j))]
      simp [splitPerm,R]
  have dis : (p.viaEmbedding L).Disjoint (q.viaEmbedding R) := by
    apply Equiv.Perm.disjoint_iff_eq_or_eq.mpr
    intro i
    obtain ⟨(j | j),rfl⟩ := e.surjective i
    · exact Or.inr (Equiv.Perm.viaEmbedding_apply_of_not_mem q R _ (rn j))
    · exact Or.inl (Equiv.Perm.viaEmbedding_apply_of_not_mem p L _ (ln j))
  rw [h,dis.cycleType]
  simp [Equiv.Perm.viaEmbedding, Equiv.Perm.cycleType_extendDomain]

def Realizes (m : ℕ) (l : List ℕ) (p : Polynomial) : Prop :=
  ∃ τ : S m, τ.cycleType = (l : Multiset ℕ) ∧ Admits τ p

theorem merge {a b l t p q} (h₁ : Realizes a l p) (h₂ : Realizes b t q) :
    Realizes (a+b) (l++t) (combine p q) := by
  obtain ⟨x,hx,hp⟩ := h₁
  obtain ⟨y,hy,hq⟩ := h₂
  exact ⟨_, by simp [split_type,hx,hy],admits_combine finSumFinEquiv hp hq⟩

theorem fixed_realizes (m : ℕ) : Realizes m [] [(0,1)] := by
  refine ⟨1,by simp,by simp,fun g hg => ?_⟩
  have hc (σ : S m) : circuit g 1 σ = 1 := by simp [circuit,hg.diag]
  have hz : Z g 0 = 1 := by simp [Z, Matchings.moment_zero]
  simp [mean, re_complexAverage, hc, Matchings.average_const, evaluate, hz]

inductive Piece where
  | fixed (n : ℕ)
  | even (r : ℕ)
  | odd (r s : ℕ)
  deriving DecidableEq

def Piece.size : Piece → ℕ
  | .fixed n => n
  | .even r => 2*r+2
  | .odd r s => 2*r+3+s

def Piece.parts : Piece → List ℕ
  | .fixed _ => []
  | .even r => [2*r+2]
  | .odd r _ => [2*r+3]

def Piece.polynomial : Piece → Polynomial
  | .fixed _ => [(0,1)]
  | .even r => [(r+1,1)]
  | .odd r s => oddPolynomial (r+1) s (CycleCoefficients.halfParameter s)

private theorem half_pos (s : ℕ) : 0 < CycleCoefficients.halfParameter s := by
  unfold CycleCoefficients.halfParameter
  have h := Nat.sqrt_le_sqrt (show 16 ≤ 16*(s+1) by omega)
  change 4 ≤ _ at h
  have ht : 0 < (Nat.sqrt (16*(s+1))+1)/2 := by omega
  positivity

theorem Piece.realizes (x : Piece) (h : x.size ≤ 10) : Realizes x.size x.parts x.polynomial := by
  cases x with
  | fixed n => exact fixed_realizes n
  | even r =>
    exact ⟨_,by simpa [Piece.parts] using localPerm_type (2*r+2) 0 (by omega), even_small r h⟩
  | odd r s =>
    exact ⟨_,by simpa [Piece.parts] using localPerm_type (2*r+3) s (by omega),
      odd_small r s h _ (half_pos s)⟩

def planSize (p : List Piece) := (p.map Piece.size).sum
def planParts (p : List Piece) := p.flatMap Piece.parts
def planPolynomial : List Piece → Polynomial
  | [] => [(0,1)]
  | x :: p => combine x.polynomial (planPolynomial p)

theorem plan_realizes (p : List Piece) (hn : planSize p ≤ 10) :
    Realizes (planSize p) (planParts p) (planPolynomial p) := by
  induction p with
  | nil => exact fixed_realizes 0
  | cons x p ih =>
    change x.size + planSize p ≤ 10 at hn
    exact merge (x.realizes (by omega)) (ih (by omega))

/-- Assign fixed points to the odd cycles as evenly as possible. -/
def plan (l : List ℕ) : List Piece :=
  let odd := l.filter (fun d => decide (1 < d) && d%2 == 1)
  let even := l.filter (fun d => d%2 == 0)
  let n := l.count 1
  let a := odd.length
  even.map (fun d => Piece.even ((d-2)/2)) ++
  (odd.zipIdx.map (fun (d,i) => Piece.odd ((d-3)/2) (n/a + if i<n%a then 1 else 0))) ++
  (if a=0 then [Piece.fixed n] else [])

set_option maxRecDepth 100000 in
private theorem ten_plans : ∀ l ∈ CycleCoefficients.partitions 10,
    planSize (plan l) = 10 ∧ (planParts (plan l) : Multiset ℕ) = ↑(l.filter (· > 1)) := by
  decide +kernel

/-- Every partition of ten supplies a concrete permutation representative,
its actual cycle type, and its polynomial matching bound. -/
theorem ten_realizes {l : List ℕ} (hl : l ∈ CycleCoefficients.partitions 10) :
    Realizes 10 (l.filter (· > 1)) (planPolynomial (plan l)) := by
  obtain ⟨hn,hp⟩ := ten_plans l hl
  obtain ⟨τ,hτ,hb⟩ := plan_realizes (plan l) hn.le
  rw [hp] at hτ
  rw [← hn]
  exact ⟨τ,hτ,hb⟩

set_option maxRecDepth 100000 in
private theorem six_plans : ∀ l ∈ CycleCoefficients.partitions 6,
    planSize (plan l) = 6 ∧ (planParts (plan l) : Multiset ℕ) = ↑(l.filter (· > 1)) := by
  decide +kernel

theorem six_realizes {l : List ℕ} (hl : l ∈ CycleCoefficients.partitions 6) :
    Realizes 6 (l.filter (· > 1)) (planPolynomial (plan l)) := by
  obtain ⟨hn,hp⟩ := six_plans l hl
  obtain ⟨τ,hτ,hb⟩ := plan_realizes (plan l) (by omega)
  rw [hp] at hτ
  rw [← hn]
  exact ⟨τ,hτ,hb⟩

end
end BlockPermanents.CyclePlans
