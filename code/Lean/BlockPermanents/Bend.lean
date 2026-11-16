import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

/-!
# The exchange and its bent square

We use matrices in orthonormal coordinates. A fork has incoming label `I`,
a through label `A`, and an exchanged label `R`. The two sides may have
different through and input spaces. The same basis of `R` is used on both
sides. In the symmetric-cable interpretation the forks are the isometric
inclusions of the paper. The local equality holds for arbitrary fork matrices.
-/

namespace BlockPermanents.Bend
open scoped BigOperators ComplexConjugate

variable {I J A B R : Type*}

/-- Turning the two ends belonging to the second tensor factor. -/
def partialTranspose (M : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun x y => M (x.1, y.2) (y.1, x.2)

/-- Coordinates of the two forks placed side by side. The first pair of
output indices is kept, and the second pair is available for exchange. -/
def splitPair (f : Matrix (A × R) I ℂ) (g : Matrix (B × R) J ℂ) :
    Matrix ((A × B) × (R × R)) (I × J) ℂ :=
  fun z x => f (z.1.1, z.2.1) x.1 * g (z.1.2, z.2.2) x.2

/-- Split, interchange the two `R`-outputs, and merge by the adjoint. -/
def exchange [Fintype A] [Fintype B] [Fintype R]
    (f : Matrix (A × R) I ℂ) (g : Matrix (B × R) J ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  (splitPair f g).conjTranspose *
    (show Matrix ((A × B) × (R × R)) (I × J) ℂ from
      fun z x => splitPair f g (z.1, z.2.swap) x)

/-- Split on each side, conjugate the second fork, and evaluate the shared
`R` and dual-`R` indices. No loop dimension or averaging factor occurs. -/
def cap [Fintype R] (f : Matrix (A × R) I ℂ) (g : Matrix (B × R) J ℂ) :
    Matrix (A × B) (I × J) ℂ :=
  fun q x => ∑ r, f (q.1, r) x.1 * star (g (q.2, r) x.2)

/-- Equation (loc:cut). The bent exchange is the *operator* given by
reflecting the cap and composing. -/
theorem bend_exchange [Fintype A] [Fintype B] [Fintype R]
    (f : Matrix (A × R) I ℂ) (g : Matrix (B × R) J ℂ) :
    partialTranspose (exchange f g) = (cap f g).conjTranspose * cap f g := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [partialTranspose, exchange, splitPair, cap, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, star_sum, star_mul',
    star_star, Finset.sum_mul, Finset.mul_sum, Prod.swap_prod_mk]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The quadratic form of an operator in orthonormal coordinates. -/
def quadratic [Fintype I] (M : Matrix I I ℂ) (v : I → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * M i j * v j

/-- A product across the chosen bend. -/
def product (v : I → ℂ) (w : J → ℂ) : I × J → ℂ :=
  fun x => v x.1 * w x.2

/-- Equation (loc:bendeval). This equality requires a product across the
bend but places no constraint on the tensor represented by the first factor. -/
theorem evaluate_bend [Fintype I] [Fintype J]
    (M : Matrix (I × J) (I × J) ℂ) (v : I → ℂ) (w : J → ℂ) :
    quadratic M (product v w) =
      quadratic (partialTranspose M) (product v (fun j => star (w j))) := by
  simp only [quadratic, product, Fintype.sum_prod_type, partialTranspose, star_mul', star_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  refine Eq.trans ?_ Finset.sum_comm
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The closure of a reflected cut, with completely unrestricted boundary. -/
theorem quadratic_reflected [Fintype I] [Fintype A] (C : Matrix A I ℂ) (v : I → ℂ) :
    quadratic (C.conjTranspose * C) v =
      ∑ a, (Complex.normSq (C.mulVec v a) : ℂ) := by
  simp only [quadratic, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, Complex.normSq_eq_conj_mul_self, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a, ∑ j, star (v i) * (star (C a i) * C a j) * v j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, star (v i) * (star (C a i) * C a j) * v j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      change star (v i) * (star (C a i) * C a j) * v j =
        star (C a i) * star (v i) * (C a j * v j)
      ring

/-- An ordinary tensor basis word on `n` strands of dimension `d`. -/
abbrev Word (d n : ℕ) := Fin n → Fin d

/-- Entries of the actual orthogonal symmetric clasp. We sum the permutation
matrices of *all* labeled slots (so repeated letters retain their multiplicities). -/
noncomputable def symClasp (d n : ℕ) : Matrix (Word d n) (Word d n) ℂ :=
  fun x y => (n.factorial : ℂ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), if x = y ∘ σ then (1 : ℂ) else 0

/-- A square fork in ambient word bases: project onto the symmetric cable,
then simply regard the output as two groups of strands. -/
noncomputable def wordFork (d n r : ℕ) (h : r ≤ n) :
    Matrix (Word d (n-r) × Word d r) (Word d n) ℂ :=
  fun z y => symClasp d n (fun t => Fin.append z.1 z.2
    (Fin.cast (Nat.sub_add_cancel h).symm t)) y

/-- The total clasp in grouped coordinates. It absorbs both input clasps. -/
noncomputable def totalClasp (d p q : ℕ) :
    Matrix (Word d p × Word d q) (Word d p × Word d q) ℂ :=
  fun x y => symClasp d (p+q) (Fin.append x.1 x.2) (Fin.append y.1 y.2)

/-- The allowed numbers of exchanged strands include both extreme cuts. -/
abbrev CutIndex (p q : ℕ) := Fin (min p q + 1)

private theorem left_bound {p q : ℕ} (r : CutIndex p q) : r.val ≤ p :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_left _ _)

private theorem right_bound {p q : ℕ} (r : CutIndex p q) : r.val ≤ q :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_right _ _)

/-- The coefficient converting the two homogeneous splits to square forks. -/
def weight (p q r : ℕ) : ℕ := p.choose r * q.choose r

/-- Equation (loc:exchange), the classical specialization of the cited
unbent Schur relation. This proposition specifies the one external input
to `bent_schur`; all matrices and normalizations in it are concrete. -/
def UnbentSchur (d p q : ℕ) : Prop :=
  ∀ x y, ((p+q).choose p : ℂ) * totalClasp d p q x y =
    ∑ r : CutIndex p q, (weight p q r : ℂ) *
      exchange (wordFork d p r (left_bound r)) (wordFork d q r (right_bound r)) x y

/-- The thin evaluations give the contraction of the two symmetric
`r`-cables. Using ambient orthonormal words automatically includes the zero-
and full-through cases. -/
noncomputable def wordCap (d p q : ℕ) (r : CutIndex p q) :=
  cap (wordFork d p r (left_bound r)) (wordFork d q r (right_bound r))

/-- Equation (loc:shuffle) on word coordinates. The only mathematical input
is the precise *unbent* relation above. Each reflected square is derived. -/
theorem bent_schur (d p q : ℕ) (schur : UnbentSchur d p q) (x y) :
    ((p+q).choose p : ℂ) * partialTranspose (totalClasp d p q) x y =
      ∑ r : CutIndex p q, (weight p q r : ℂ) *
        ((wordCap d p q r).conjTranspose * wordCap d p q r) x y := by
  rw [partialTranspose, schur]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  exact congrFun (congrFun (bend_exchange
    (wordFork d p r (left_bound r)) (wordFork d q r (right_bound r))) x) y

/-- The scalar obtained by evaluating the cut and gluing its reflection. -/
noncomputable def energy {T : Type*} [Fintype T] (u : T → ℂ) : ℝ :=
  ∑ t, Complex.normSq (u t)

/-- The quadratic form commutes with finite linear combinations of operators. -/
private theorem quadratic_combination {S : Type*} [Fintype S] [Fintype I]
    (M : Matrix I I ℂ) (C : S → Matrix I I ℂ) (c : ℂ) (w : S → ℂ)
    (h : ∀ i j, c * M i j = ∑ s, w s * C s i j) (v : I → ℂ) :
    c * quadratic M v = ∑ s, w s * quadratic (C s) v := by
  simp only [quadratic, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ j, ∑ s, w s * (star (v i) * C s i j * v j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = star (v i) * (c * M i j) * v j := by ring
        _ = _ := by
          rw [h, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intros
          ring
    _ = ∑ i, ∑ s, ∑ j, w s * (star (v i) * C s i j * v j) := by
      apply Finset.sum_congr rfl
      intros
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Closing the total clasp on a product gives the weighted energies of the
contractions. This form is convenient for removing the extreme cuts. -/
theorem closed_bent_schur (d p q : ℕ) (schur : UnbentSchur d p q)
    (F : Word d p → ℂ) (H : Word d q → ℂ) :
    ((p+q).choose p : ℂ) * quadratic (totalClasp d p q) (product F H) =
      ∑ r : CutIndex p q, (weight p q r : ℂ) *
        (energy ((wordCap d p q r).mulVec (product F (fun j => star (H j)))) : ℂ) := by
  rw [evaluate_bend]
  rw [quadratic_combination _ _ _ _ (bent_schur d p q schur)]
  apply Finset.sum_congr rfl
  intro r _
  rw [quadratic_reflected]
  congr 1
  exact (map_sum Complex.ofRealHom _ _).symm

/-- Multiplying the two input tensors by the two split maps, and then
contracting their common output. -/
theorem cap_product [Fintype R] [Fintype I] [Fintype J]
    (f : Matrix (A × R) I ℂ) (g : Matrix (B × R) J ℂ)
    (F : I → ℂ) (H : J → ℂ) (a : A) (b : B) :
    (cap f g).mulVec (product F (fun j => star (H j))) (a,b) =
      ∑ r, f.mulVec F (a,r) * star (g.mulVec H (b,r)) := by
  simp only [Matrix.mulVec, dotProduct, cap, product, Fintype.sum_prod_type,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ r, ∑ j, f (a,r) i * star (g (b,r) j) * (F i * star (H j)) := by
      apply Finset.sum_congr rfl
      intros
      exact Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, f (a,r) i * star (g (b,r) j) * (F i * star (H j)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A vector carried by a symmetric cable, defined as a fixed point of the
concrete orthogonal clasp. -/
def Symmetric {d k : ℕ} (F : Word d k → ℂ) : Prop := (symClasp d k).mulVec F = F

/-- Regrouping a symmetric input just reads off its coefficient. -/
theorem split_symmetric {d k r : ℕ} (h : r ≤ k)
    {F : Word d k → ℂ} (hs : Symmetric F) (a : Word d (k-r)) (b : Word d r) :
    (wordFork d k r h).mulVec F (a,b) =
      F (fun t => Fin.append a b (Fin.cast (Nat.sub_add_cancel h).symm t)) :=
  congrFun hs _

/-- The two distinguished cut indices in equal thickness. -/
def zeroCut (k : ℕ) : CutIndex k k := ⟨0, Nat.zero_lt_succ _⟩
def fullCut (k : ℕ) : CutIndex k k := ⟨k, by simp⟩

/-- On symmetric inputs the zero cap is the identity on the bent product. -/
theorem zero_cap {d k : ℕ} {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H)
    (a b : Word d k) :
    (wordCap d k k (zeroCut k)).mulVec (product F (fun j => star (H j))) (a,b) =
      F a * star (H b) := by
  rw [wordCap, cap_product]
  simp only [zeroCut, split_symmetric _ hF, split_symmetric _ hH]
  simp [Fin.append_right_nil _ _ rfl, Function.comp_def]

/-- On symmetric inputs the full cap evaluates their Hermitian pairing. -/
theorem full_cap {d k : ℕ} {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H)
    (a b : Word d (k-k)) :
    (wordCap d k k (fullCut k)).mulVec (product F (fun j => star (H j))) (a,b) =
      ∑ t, F t * star (H t) := by
  rw [wordCap, cap_product]
  simp only [fullCut, split_symmetric _ hF, split_symmetric _ hH]
  simp [Fin.append_left_nil _ _ (Nat.sub_self k), Function.comp_def]

/-- Reflected zero and full caps give the two whole-packet routings. -/
theorem zero_cap_energy {d k : ℕ} {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H) :
    energy ((wordCap d k k (zeroCut k)).mulVec (product F (fun j => star (H j)))) =
      energy F * energy H := by
  unfold energy
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [zero_cap hF hH, Complex.normSq_mul]
  exact congrArg _ (Complex.normSq_conj (H b))

theorem full_cap_energy {d k : ℕ} {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H) :
    energy ((wordCap d k k (fullCut k)).mulVec (product F (fun j => star (H j)))) =
      Complex.normSq (∑ t, F t * star (H t)) := by
  unfold energy
  rw [Fintype.sum_prod_type]
  simp only [full_cap hF hH]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, fullCut, Nat.sub_self, pow_zero, one_smul]

/-- The indices strictly between zero and full exchange. -/
def properCuts (k : ℕ) : Finset (CutIndex k k) :=
  (Finset.univ.erase (zeroCut k)).erase (fullCut k)

private theorem split_cuts {T : Type*} [AddCommMonoid T] {k : ℕ}
    (hk : 0 < k) (g : CutIndex k k → T) :
    ∑ r, g r = g (zeroCut k) + g (fullCut k) + ∑ r ∈ properCuts k, g r := by
  have hne : fullCut k ≠ zeroCut k := fun he => hk.ne' (congrArg Fin.val he)
  have hfull := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ (fullCut k)⟩
  rw [← Finset.sum_erase_add _ g (Finset.mem_univ (zeroCut k))]
  rw [← Finset.sum_erase_add _ g hfull]
  unfold properCuts
  ac_rfl

/-- A proper contraction contributes its binomial multiplicity times its
squared norm. -/
noncomputable def cutTerm {d k : ℕ} (F H : Word d k → ℂ) (r : CutIndex k k) : ℝ :=
  (weight k k r : ℝ) * energy ((wordCap d k k r).mulVec (product F (fun j => star (H j))))

/-- Equation (eq:two-gap), for arbitrary symmetric packet vectors of every
positive thickness. The two subtracted terms correspond to the identity
and the whole interchange. -/
theorem two_block_gap {d k : ℕ} (hk : 0 < k) (schur : UnbentSchur d k k)
    {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H) :
    ((k+k).choose k : ℂ) * quadratic (totalClasp d k k) (product F H) -
      ((energy F * energy H + Complex.normSq (∑ t, F t * star (H t)) : ℝ) : ℂ) =
      ((∑ r ∈ properCuts k, cutTerm F H r : ℝ) : ℂ) := by
  rw [closed_bent_schur d k k schur, split_cuts hk]
  rw [zero_cap_energy hF hH, full_cap_energy hF hH]
  have hz : weight k k (zeroCut k) = 1 := by simp [weight, zeroCut]
  have hf : weight k k (fullCut k) = 1 := by simp [weight, fullCut]
  simp only [hz, hf, Nat.cast_one, one_mul, Complex.ofReal_add, Complex.ofReal_mul,
    add_sub_cancel_left]
  rw [show ((∑ r ∈ properCuts k, cutTerm F H r : ℝ) : ℂ) =
    ∑ r ∈ properCuts k, (cutTerm F H r : ℂ) from map_sum Complex.ofRealHom _ _]
  apply Finset.sum_congr rfl
  intro r _
  simp [cutTerm, Complex.ofReal_mul]

/-- Positivity follows term by term after the two extreme cuts have been
removed. -/
theorem cutTerm_nonneg {d k : ℕ} (F H : Word d k → ℂ) (r : CutIndex k k) :
    0 ≤ cutTerm F H r :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

theorem two_block_nonneg {d k : ℕ} (hk : 0 < k) (schur : UnbentSchur d k k)
    {F H : Word d k → ℂ} (hF : Symmetric F) (hH : Symmetric H) :
    0 ≤ (((k+k).choose k : ℂ) * quadratic (totalClasp d k k) (product F H) -
      ((energy F * energy H + Complex.normSq (∑ t, F t * star (H t)) : ℝ) : ℂ)).re := by
  rw [two_block_gap hk schur hF hH, Complex.ofReal_re]
  exact Finset.sum_nonneg fun r _ => cutTerm_nonneg F H r

end BlockPermanents.Bend
