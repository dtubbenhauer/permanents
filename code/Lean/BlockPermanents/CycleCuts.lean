import BlockPermanents.CyclePolynomial
import BlockPermanents.CycleCoefficients

/-! # Verifying the wiring of elementary cycle cuts

A wire is an ordered pair of labels, evaluated at one Gram entry. Equal
multisets therefore give identical closed products in every dimension. -/
namespace BlockPermanents.CycleCuts
open CycleMatching CycleComposition CyclePolynomial Matchings
noncomputable section

abbrev Wire (m : ℕ) := Fin m × Fin m
def evalW {m} (g : Gram m) (σ : S m) (w : Multiset (Wire m)) : ℂ :=
  (w.map (fun z => g (σ z.1) (σ z.2))).prod

def wiring {m} (τ : S m) : Multiset (Wire m) :=
  ((Finset.univ.filter (fun i => τ i ≠ i)).val).map (fun i => (τ i,i))

def arcs {m r : ℕ} (e : Fin r × Fin 2 ↪ Fin m) : Multiset (Wire m) :=
  Finset.univ.val.map (fun t => (e (t,0),e (t,1)))

private theorem eval_circuit {m : ℕ} (g : Gram m) (hg : UnitGram g) (τ σ : S m) :
    circuit g τ σ = evalW g σ (wiring τ) := by
  simp only [evalW, wiring, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Function.comp_apply, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : τ i = i <;> simp [h, hg.diag]

private theorem eval_arcs {m r : ℕ} (g : Gram m) (σ : S m) (e : Fin r × Fin 2 ↪ Fin m) :
    evalW g σ (arcs e) = amplitude g e σ := by
  simp only [evalW, arcs, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

private theorem eval_reverse {m : ℕ} (g : Gram m) (hg : UnitGram g) (σ : S m)
    (s : Multiset (Wire m)) : evalW g σ (s.map Prod.swap) = star (evalW g σ s) := by
  induction s using Multiset.induction_on with
  | empty => simp [evalW]
  | cons x s ih =>
    simpa [evalW, hg.herm, mul_comm] using congrArg (fun z => g (σ x.2) (σ x.1) * z) ih

theorem admits_even {m r} (τ : S m) (u v : Fin r × Fin 2 ↪ Fin m)
    (h : wiring τ = (arcs u).map Prod.swap + arcs v) : Admits τ [(r,1)] := by
  refine ⟨by simp,fun g hg => ?_⟩
  have hx (σ : S m) : circuit g τ σ = star (amplitude g u σ) * amplitude g v σ := by
    rw [eval_circuit g hg, h, show ∀ t s, evalW g σ (t+s) = evalW g σ t * evalW g σ s by
      simp [evalW], eval_reverse g hg, eval_arcs, eval_arcs]
  simpa only [mean, re_complexAverage, hx, evaluate, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_one, one_mul, add_zero, Fintype.card_fin] using even_cycle_cut g u v

/-- The two monomials L_s shifted by the number r of alternate upper edges. -/
def oddPolynomial (r s : ℕ) (u : ℚ) : Polynomial :=
  [(r,(u/(s+1)+1/u)/2),(r+1,s/(2*u))]

theorem admits_odd {m r} (τ : S m) (upper : Fin (r+1) × Fin 2 ↪ Fin m)
    (lower : Fin r × Fin 2 ↪ Fin m) (i j v : Fin m) (U : Finset (Fin m))
    (hij : i ≠ j) (hi : i ∉ Set.range lower) (hj : j ∉ Set.range lower)
    (hU : ∀ w ∈ U, i ≠ w ∧ j ≠ w ∧ w ∉ Set.range upper ∧ w ∉ Set.range lower) (hv : v ∈ U)
    (hw : wiring τ = (arcs upper).map Prod.swap + (arcs lower + {(i,v),(v,j)}))
    (s : ℕ) (hs : U.card = s+1) (u : ℚ) (hu : 0 < u) : Admits τ (oddPolynomial (r+1) s u) := by
  constructor
  · intro z hz
    simp only [oddPolynomial, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> dsimp <;> positivity
  intro g hg
  have hx (σ : S m) : circuit g τ σ =
      star (amplitude g upper σ) * (amplitude g lower σ * via g i j v σ) := by
    rw [eval_circuit g hg, hw]
    have hadd : ∀ t s, evalW g σ (t+s) = evalW g σ t * evalW g σ s := by simp [evalW]
    rw [hadd, hadd, eval_reverse g hg, eval_arcs, eval_arcs]
    simp [evalW, via]
  have hb := odd_cycle_cut g hg.unit upper lower (by simp) i j hij hi hj U
    (fun w hw => ⟨(hU w hw).1,(hU w hw).2.1,(hU w hw).2.2.2⟩)
    (hs ▸ Nat.succ_pos _) (u:ℝ) (by exact_mod_cast hu)
  rw [pathCut_at _ _ _ _ _ _ _ hv hU] at hb
  simpa [mean,re_complexAverage,hx,evaluate,oddPolynomial,hs] using hb

/-- Wiring for the two sets of matching edges in a consecutive cycle.
The orientation of the short edges runs back from each even vertex to the
previous odd vertex. -/
def upperWire (m : ℕ) [NeZero m] {r} (p : Fin r × Fin 2) : Fin m :=
  Fin.ofNat' m (2*p.1.val + p.2.val)

def lowerWire (m : ℕ) [NeZero m] {r} (p : Fin r × Fin 2) : Fin m :=
  if p.2=0 then Fin.ofNat' m (2*(p.1.val+1)) else Fin.ofNat' m (2*p.1.val+1)

/-- An elementary component with a consecutive nontrivial cycle and its
assigned unused labels. -/
def localPerm (d s : ℕ) : S (d+s) :=
  if h : 0 < d then Fin.cycleRange ⟨d-1,by omega⟩ else 1

theorem localPerm_type (d s : ℕ) (h : 2 ≤ d) :
    (localPerm d s).cycleType = {d} := by
  haveI : NeZero (d+s) := ⟨by omega⟩
  have hn : (⟨d-1,by omega⟩ : Fin (d+s)) ≠ 0 := by simp [Fin.ext_iff]; omega
  simp [localPerm, show 0 < d by omega, Fin.cycleType_cycleRange hn, Nat.sub_add_cancel (by omega : 1 ≤ d)]

end
end BlockPermanents.CycleCuts
