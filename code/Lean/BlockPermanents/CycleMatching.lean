import BlockPermanents.Matchings
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases

/-! # Averaged two-step paths and alternating cycle cuts

A family of disjoint edges is an embedding of its ordered endpoints into the
set of labels. Extending that embedding by unused labels identifies its mean
with the matching moment used in the fine estimate. -/
namespace BlockPermanents.CycleMatching
open Matchings
open scoped BigOperators
noncomputable section
abbrev S (m : ℕ) := Equiv.Perm (Fin m)
abbrev Gram (m : ℕ) := Fin m → Fin m → ℂ

def sqEdge {m} (g : Gram m) (i j : Fin m) := Complex.normSq (g i j)

def Z {m} (g : Gram m) (r : ℕ) := moment m r (fun _ => 1) (sqEdge g)

/-- Every fixed embedding of the endpoints of a matching realizes its canonical mean. -/
theorem mean_edges {m : ℕ} {P : Type*} [Fintype P] (g : Gram m) (e : P × Fin 2 ↪ Fin m) :
    average m (fun σ => ∏ a, sqEdge g (σ (e (a,0))) (σ (e (a,1)))) =
      Z g (Fintype.card P) := by
  classical
  let s := Set.range e
  let ext : Shape P ↥(sᶜ) ≃ Fin m :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl s)
  have h := average_weight_eq_moment (fun _ => 1) (sqEdge g) ext rfl
  simpa [weight, ext, s, Z] using h

/-- Add an edge on fresh vertices to an existing list of oriented edges. -/
def withEdge {P : Type*} {m} (e : P × Fin 2 ↪ Fin m) (x y : Fin m)
    (hxy : x ≠ y) (hx : x ∉ Set.range e) (hy : y ∉ Set.range e) :
    Option P × Fin 2 ↪ Fin m where
  toFun p := match p.1 with
    | none => if p.2 = 0 then x else y
    | some a => e (a,p.2)
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    cases a with
    | none =>
      cases b with
      | none => fin_cases i <;> fin_cases j <;> simp_all
      | some b =>
        change (if i = 0 then x else y) = e (b,j) at h
        split at h
        · exact False.elim (hx ⟨_,h.symm⟩)
        · exact False.elim (hy ⟨_,h.symm⟩)
    | some a =>
      cases b with
      | none =>
        change e (a,i) = (if j = 0 then x else y) at h
        split at h
        · exact False.elim (hx ⟨_,h⟩)
        · exact False.elim (hy ⟨_,h⟩)
      | some b =>
        obtain h' := e.injective (show e (a,i) = e (b,j) from h)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h'
        rfl

def prefixWeight {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (σ : S m) : ℝ :=
  ∏ a, sqEdge g (σ (e (a,0))) (σ (e (a,1)))

theorem prefix_nonneg {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (σ : S m) : 0 ≤ prefixWeight g e σ :=
  Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _

theorem extend_weight {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (x y : Fin m) (hxy hx hy) (σ : S m) :
    prefixWeight g (withEdge e x y hxy hx hy) σ =
      sqEdge g (σ x) (σ y) * prefixWeight g e σ := by
  rw [prefixWeight, Fintype.prod_option]
  rfl

theorem mean_extension {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (x y : Fin m) (hxy : x ≠ y) (hx : x ∉ Set.range e) (hy : y ∉ Set.range e) :
    average m (fun σ => sqEdge g (σ x) (σ y) * prefixWeight g e σ) =
      Z g (Fintype.card P + 1) := by
  simp_rw [← extend_weight g e x y hxy hx hy]
  simpa only [Fintype.card_option] using mean_edges g (withEdge e x y hxy hx hy)

private theorem two_re_le (a b : ℂ) : 2 * (star a * b).re ≤ Complex.normSq a + Complex.normSq b := by
  have h := Complex.normSq_nonneg (a-b)
  simp only [Complex.normSq_sub, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at *
  linarith

/-- The path carrying intermediate color v between distinct endpoints i,j. -/
def via {m : ℕ} (g : Gram m) (i j v : Fin m) (σ : S m) : ℂ := g (σ i) (σ v) * g (σ v) (σ j)

private theorem four_cycle (a b c d : ℂ) :
    2 * (star (a*b) * (c*d)).re ≤ Complex.normSq (a * star d) + Complex.normSq (c * star b) := by
  have h := two_re_le (a * star d) (c * star b)
  convert h using 3
  simp [star_mul', mul_comm, mul_left_comm, mul_assoc]

theorem mem_withEdge {m : ℕ} {P : Type*} (e : P × Fin 2 ↪ Fin m)
    {x y : Fin m} {hxy hx hy} {z : Fin m} :
    z ∈ Set.range (withEdge e x y hxy hx hy) ↔ z = x ∨ z = y ∨ z ∈ Set.range e := by
  constructor
  · rintro ⟨⟨_ | a, j⟩,rfl⟩
    · change (if j=0 then x else y) = x ∨ _
      split <;> simp_all [withEdge]
    · exact Or.inr (Or.inr ⟨_,rfl⟩)
  · rintro (rfl | rfl | ⟨⟨a,j⟩,rfl⟩)
    · exact ⟨(none,0),rfl⟩
    · exact ⟨(none,1),rfl⟩
    · exact ⟨(some a,j),rfl⟩

theorem mean_two_edges {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) {i j v w : Fin m}
    (hij : i ≠ j) (hvw : v ≠ w) (hiv : i ≠ v) (hiw : i ≠ w) (hjv : j ≠ v) (hjw : j ≠ w)
    (hi : i ∉ Set.range e) (hj : j ∉ Set.range e) (hv : v ∉ Set.range e) (hw : w ∉ Set.range e) :
    average m (fun σ => prefixWeight g e σ * (sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j))) =
      Z g (Fintype.card P+2) := by
  let f := withEdge e i v hiv hi hv
  have hw' : w ∉ Set.range f := by
    change ¬ w ∈ Set.range (withEdge e i v hiv hi hv)
    rw [mem_withEdge]
    tauto
  have hj' : j ∉ Set.range f := by
    change ¬ j ∈ Set.range (withEdge e i v hiv hi hv)
    rw [mem_withEdge]
    tauto
  have h := mean_extension g f w j hjw.symm hw' hj'
  simpa only [f, extend_weight, Fintype.card_option, mul_comm, mul_assoc, mul_left_comm] using h

private theorem normSq_sum {I : Type*} (s : Finset I) (x : I → ℂ) :
    Complex.normSq (∑ i ∈ s, x i) = ∑ i ∈ s, ∑ j ∈ s, (star (x i) * x j).re := by
  have he := congrArg Complex.re (@Complex.normSq_eq_conj_mul_self (∑ i ∈ s, x i))
  rw [Finset.sum_comm]
  simpa only [Complex.ofReal_re, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum] using he

/-- The two-step-path bound, with any fixed disjoint spectator matching.
There are |U| diagonal terms, and |U|(|U|−1) ordered distinct middles.
On the latter, completing a square produces the two opposite-edge matchings.
Averaging the free endpoints gives Lemma 7E.1; the spectator version is
the path estimate used for all odd circuits in Appendix A. -/
theorem path_bound {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (hg : ∀ i j, sqEdge g i j ≤ 1) (e : P × Fin 2 ↪ Fin m)
    (i j : Fin m) (hij : i ≠ j) (hi : i ∉ Set.range e) (hj : j ∉ Set.range e)
    (U : Finset (Fin m)) (hU : ∀ v ∈ U, i ≠ v ∧ j ≠ v ∧ v ∉ Set.range e) :
    average m (fun σ => prefixWeight g e σ * Complex.normSq (∑ v ∈ U, via g i j v σ)) ≤
      (U.card : ℝ)*Z g (Fintype.card P+1) + (U.card : ℝ)*(U.card-1)*Z g (Fintype.card P+2) := by
  classical
  let term (v w : Fin m) (σ : S m) := prefixWeight g e σ * (star (via g i j v σ) * via g i j w σ).re
  have diag (v) (hv : v ∈ U) : average m (term v v) ≤ Z g (Fintype.card P+1) := by
    obtain ⟨hiv,_,hv'⟩ := hU v hv
    rw [← mean_extension g e i v hiv hi hv']
    apply average_le
    intro σ
    have h := hg (σ v) (σ j)
    change Complex.normSq _ ≤ 1 at h
    have h' := mul_le_mul_of_nonneg_left h (Complex.normSq_nonneg (g (σ i) (σ v)))
    rw [mul_one] at h'
    unfold term
    rw [show ∀ z : ℂ, (star z * z).re = Complex.normSq z by
      intro z; exact congrArg Complex.re (@Complex.normSq_eq_conj_mul_self z).symm]
    rw [via, Complex.normSq_mul, mul_comm (sqEdge g _ _)]
    exact mul_le_mul_of_nonneg_left h' (prefix_nonneg ..)
  have cross (v w) (hv : v ∈ U) (hw : w ∈ U) (hvw : v ≠ w) :
      average m (term v w) ≤ Z g (Fintype.card P+2) := by
    obtain ⟨hiv,hjv,hv'⟩ := hU v hv
    obtain ⟨hiw,hjw,hw'⟩ := hU w hw
    let R (v w : Fin m) (σ : S m) := prefixWeight g e σ * (sqEdge g (σ i) (σ v) * sqEdge g (σ w) (σ j))
    have cr (σ : S m) : 2 * term v w σ ≤ R v w σ + R w v σ := by
      have h := four_cycle (g (σ i) (σ v)) (g (σ v) (σ j)) (g (σ i) (σ w)) (g (σ w) (σ j))
      simp only [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj] at h
      simpa only [R, term, via, sqEdge, mul_add, mul_left_comm, Complex.star_def] using
        mul_le_mul_of_nonneg_left h (prefix_nonneg g e σ)
    have h := average_le cr
    rw [average_smul, average_add] at h
    have h1 : average m (R v w) = _ := mean_two_edges g e hij hvw hiv hiw hjv hjw hi hj hv' hw'
    have h2 : average m (R w v) = _ := mean_two_edges g e hij hvw.symm hiw hiv hjw hjv hi hj hw' hv'
    rw [h1,h2] at h
    linarith
  have hp (σ : S m) : prefixWeight g e σ * Complex.normSq (∑ v ∈ U, via g i j v σ) =
      ∑ v ∈ U, ∑ w ∈ U, term v w σ := by
    simp [normSq_sum, term, Finset.mul_sum]
  rw [show average m (fun σ => prefixWeight g e σ * Complex.normSq (∑ v ∈ U, via g i j v σ)) =
      ∑ v ∈ U, ∑ w ∈ U, average m (term v w) by simp_rw [hp, average_sum]]
  have row (v) (hv : v ∈ U) : ∑ w ∈ U, average m (term v w) ≤
      Z g (Fintype.card P+1) + (U.card-1 : ℝ)*Z g (Fintype.card P+2) := by
    rw [← Finset.sum_erase_add U _ hv, add_comm]
    apply add_le_add (diag v hv)
    apply le_trans (Finset.sum_le_sum (fun w hw => cross v w hv (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm))
    rw [Finset.sum_const, Finset.card_erase_of_mem hv, nsmul_eq_mul, Nat.cast_sub (Finset.card_pos.mpr ⟨v,hv⟩)]
    simp
  refine (Finset.sum_le_sum row).trans_eq ?_
  simp [nsmul_eq_mul, mul_add, mul_assoc]

/-- Product on an oriented matching, before closing it with its reflection. -/
def amplitude {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (σ : S m) : ℂ :=
  ∏ a, g (σ (e (a,0))) (σ (e (a,1)))

theorem normSq_amplitude {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (e : P × Fin 2 ↪ Fin m) (σ : S m) :
    Complex.normSq (amplitude g e σ) = prefixWeight g e σ := by
  simp [amplitude, prefixWeight, sqEdge]

theorem average_relabel {m : ℕ} (f : S m → ℝ) (τ : S m) :
    average m (fun σ => f (σ*τ)) = average m f := by
  unfold average
  rw [show (∑ σ, f (σ*τ)) = ∑ σ, f σ from Equiv.sum_comp (Equiv.mulRight τ) f]

theorem abs_average_le {m : ℕ} (f : S m → ℝ) :
    |average m f| ≤ average m (fun σ => |f σ|) := by
  unfold average
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m.factorial : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

private theorem weighted_cut (u : ℝ) (hu : 0 < u) (a b : ℂ) :
    (2*u)*|(star a * b).re| ≤ u^2 * Complex.normSq a + Complex.normSq b := by
  have h := Complex.abs_re_le_norm (star a * b)
  rw [norm_mul, norm_star] at h
  rw [← Complex.sq_norm, ← Complex.sq_norm]
  nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 2*u by positivity),
    sq_nonneg (u*‖a‖-‖b‖)]

/-- A cycle cut at alternating edges. The r long upper edges form A.
The other orientation has r−1 short lower edges and the path from i through
a free middle vertex to j. Averaging over all middles collapses to the mean
of the oriented circuit when the short and upper edges avoid them. -/
def pathCut {m : ℕ} {P Q : Type*} [Fintype P] [Fintype Q] (g : Gram m)
    (upper : Q × Fin 2 ↪ Fin m) (lower : P × Fin 2 ↪ Fin m) (i j : Fin m)
    (U : Finset (Fin m)) : ℝ :=
  average m (fun σ => (star (amplitude g upper σ) *
    (amplitude g lower σ * ∑ v ∈ U, via g i j v σ)).re) / U.card

/-- Normalized odd-cycle estimate of Appendix A with either orientation sign.
The two coefficients are exactly the constant and linear coefficients of
L_{|U|−1}. Both halves are explicit products of Gram entries. -/
theorem odd_cycle_cut {m : ℕ} {P Q : Type*} [Fintype P] [Fintype Q] (g : Gram m)
    (hg : ∀ i j, sqEdge g i j ≤ 1) (upper : Q × Fin 2 ↪ Fin m)
    (lower : P × Fin 2 ↪ Fin m) (hsize : Fintype.card Q = Fintype.card P+1)
    (i j : Fin m) (hij : i ≠ j) (hi : i ∉ Set.range lower) (hj : j ∉ Set.range lower)
    (U : Finset (Fin m)) (hU : ∀ v ∈ U, i ≠ v ∧ j ≠ v ∧ v ∉ Set.range lower)
    (hn : 0 < U.card) (u : ℝ) (hu : 0 < u) :
    |pathCut g upper lower i j U| ≤
      (u/(U.card : ℝ) + 1/u)/2 * Z g (Fintype.card Q) +
      ((U.card : ℝ)-1)/(2*u) * Z g (Fintype.card Q + 1) := by
  let A := amplitude g upper
  let B := fun σ => amplitude g lower σ * ∑ v ∈ U, via g i j v σ
  let f := fun σ => (star (A σ) * B σ).re
  have h := average_le (fun σ => weighted_cut u hu (A σ) (B σ))
  rw [average_smul, average_add, average_smul] at h
  have hA : average m (fun σ => Complex.normSq (A σ)) = Z g (Fintype.card Q) := by
    simp only [A, normSq_amplitude]
    exact mean_edges g upper
  have hB := path_bound g hg lower i j hij hi hj U hU
  have b (σ) : Complex.normSq (B σ) =
      prefixWeight g lower σ * Complex.normSq (∑ v ∈ U, via g i j v σ) := by
    simp only [B, Complex.normSq_mul, normSq_amplitude]
  simp_rw [hA,b] at h
  have h' := le_trans (mul_le_mul_of_nonneg_left (abs_average_le f)
    (by positivity : 0 ≤ 2*u)) (h.trans (add_le_add_left hB _))
  change |average m f / (U.card : ℝ)| ≤ _
  have hn' : 0 < (U.card : ℝ) := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hn']
  have halg (x y n : ℝ) (hnp : n ≠ 0) :
      (u/n+1/u)/2 * x + (n-1)/(2*u)*y =
        ((u^2*x + (n*x+n*(n-1)*y))/(2*u))/n := by
    field_simp [hu.ne',hnp]
    ring
  rw [halg _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn', le_div_iff₀ (by positivity)]
  simpa only [mul_comm (|average m f|), hsize, Nat.add_assoc] using h'

private theorem amplitude_swap {m} {T : Type*} [Fintype T] (g : Gram m)
    (e : T × Fin 2 ↪ Fin m) (v w : Fin m)
    (hv : v ∉ Set.range e) (hw : w ∉ Set.range e) (σ : S m) :
    amplitude g e (σ * Equiv.swap v w) = amplitude g e σ := by
  have h (p) : Equiv.swap v w (e p) = e p :=
    Equiv.swap_apply_of_ne_of_ne (fun he => hv ⟨p,he⟩) (fun he => hw ⟨p,he⟩)
  simp only [amplitude, Equiv.Perm.mul_apply, h]

/-- A single specified middle vertex has the same mean as the sum over all
available middles divided by their number. The equality follows by exchanging
two free labels without changing either short matching. -/
theorem pathCut_at {m : ℕ} {P Q : Type*} [Fintype P] [Fintype Q] (g : Gram m)
    (upper : Q × Fin 2 ↪ Fin m) (lower : P × Fin 2 ↪ Fin m) (i j : Fin m)
    (U : Finset (Fin m)) (v : Fin m) (hv : v ∈ U)
    (hU : ∀ w ∈ U, i ≠ w ∧ j ≠ w ∧ w ∉ Set.range upper ∧ w ∉ Set.range lower) :
    pathCut g upper lower i j U = average m (fun σ => (star (amplitude g upper σ) *
      (amplitude g lower σ * via g i j v σ)).re) := by
  let f := fun w σ => (star (amplitude g upper σ) * (amplitude g lower σ * via g i j w σ)).re
  have hf (w) (hw : w ∈ U) : average m (f w) = average m (f v) := by
    let π := Equiv.swap v w
    have fixed (x) (hxv : x ≠ v) (hxw : x ≠ w) : π x = x :=
      Equiv.swap_apply_of_ne_of_ne hxv hxw
    obtain ⟨hiv,hjv,huv,hlv⟩ := hU v hv
    obtain ⟨hiw,hjw,huw,hlw⟩ := hU w hw
    have hs (σ) : f v (σ*π) = f w σ := by
      simp only [f, π, amplitude_swap g upper v w huv huw, amplitude_swap g lower v w hlv hlw, via, Equiv.Perm.mul_apply,
        fixed i hiv hiw, fixed j hjv hjw, show π v = w from Equiv.swap_apply_left ..]
    simpa only [hs] using average_relabel (f v) π
  have he (σ : S m) : (star (amplitude g upper σ) *
        (amplitude g lower σ * ∑ w ∈ U, via g i j w σ)).re = ∑ w ∈ U, f w σ := by
    simp [f, Finset.mul_sum, Complex.re_sum]
  unfold pathCut
  simp_rw [he]
  rw [average_sum, Finset.sum_congr rfl hf, Finset.sum_const,nsmul_eq_mul]
  have hU' : (U.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨v,hv⟩).ne'
  change (U.card : ℝ) * average m (f v) / U.card = average m (f v)
  field_simp

/-- Closing either of two alternating matchings against the other gives the
even-cycle bound of Appendix A, with both signs. -/
theorem even_cycle_cut {m : ℕ} {P : Type*} [Fintype P] (g : Gram m)
    (upper lower : P × Fin 2 ↪ Fin m) :
    |average m (fun σ => (star (amplitude g upper σ) * amplitude g lower σ).re)| ≤
      Z g (Fintype.card P) := by
  let f := fun σ => (star (amplitude g upper σ) * amplitude g lower σ).re
  have h := average_le (fun σ => weighted_cut 1 zero_lt_one
    (amplitude g upper σ) (amplitude g lower σ))
  simp only [mul_one, one_pow, one_mul, average_smul, average_add, normSq_amplitude] at h
  have hmean (e : P × Fin 2 ↪ Fin m) : average m (prefixWeight g e) = Z g (Fintype.card P) :=
    mean_edges g e
  rw [hmean,hmean] at h
  change |average m f| ≤ _
  have hl := abs_average_le f
  change 2 * average m (fun σ => |f σ|) ≤ _ at h
  linarith

end
end BlockPermanents.CycleMatching
