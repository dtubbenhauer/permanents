import BlockPermanents.ThreeSupport

/-! # Completing an unequal pair of cables

The first cable can have arbitrary thickness at least the thickness of the
marked packet. The extra ordinary wires are retained as spectator slots.
This applies to the (2k,k)-contraction of Section 8A.
-/

namespace BlockPermanents.ThreeSupport
open Bend Closures PairBound
open scoped BigOperators Matrix
noncomputable section

/-- Concatenate words across an explicit equality of lengths. -/
def joinAt {d a b n : ℕ} (h : a+b=n) : Word d a × Word d b ≃ Word d n where
  toFun u := Fin.append u.1 u.2 ∘ Fin.cast h.symm
  invFun w := (fun i => w (Fin.cast h (Fin.castAdd b i)), fun j => w (Fin.cast h (Fin.natAdd a j)))
  left_inv u := by simp [Function.comp_def, -Fin.natAdd_eq_addNat]
  right_inv w := by
    subst n
    exact Fin.append_castAdd_natAdd

private theorem joinAt_assoc {d a b c ab bc n : ℕ} (hab : a+b=ab) (hbc : b+c=bc)
    (hl : ab+c=n) (hr : a+bc=n) (x : Word d a) (y : Word d b) (z : Word d c) :
    joinAt hl (joinAt hab (x,y), z) = joinAt hr (x,joinAt hbc (y,z)) := by
  subst ab
  subst bc
  subst n
  simpa [joinAt, Function.comp_def] using Fin.append_assoc x y z

private theorem thinLe {p k : ℕ} (r : CutIndex p k) : r.val ≤ k :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_right ..)

private theorem thickLe {p k : ℕ} (r : CutIndex p k) : r.val ≤ p :=
  (Nat.le_of_lt_succ r.isLt).trans (min_le_left ..)

/-- The full cut in which the shorter, marked packet disappears. -/
def longFull {p k : ℕ} (h : k ≤ p) : CutIndex p k := ⟨k, by simp [min_eq_right h]⟩

/-- Grouping the free wires first, the survivors of the paired wires second. -/
def freeSlots (d : ℕ) {p k : ℕ} (h : k ≤ p) (r : CutIndex p k) :
    Word d (p-k) × Word d (k-r) ≃ Word d (p-r) :=
  joinAt (by have := thinLe r; omega)

/-- The lower half of the rectangular cap in the ordinary word basis. -/
def longCut {d p k : ℕ} (P : Word d p → ℂ) (H : Word d k → ℂ) (r : CutIndex p k) :=
  (wordCap d p k r).mulVec (product P (fun i => star (H i)))

theorem longCut_entry {d p k : ℕ} {P : Word d p → ℂ} {H : Word d k → ℂ}
    (hP : Symmetric P) (hH : Symmetric H) (r : CutIndex p k) (a : Word d (p-r)) (b : Word d (k-r)) :
    longCut P H r (a,b) =
      ∑ w, P (joinAt (Nat.sub_add_cancel (thickLe r)) (a,w)) *
        star (H (joinAt (Nat.sub_add_cancel (thinLe r)) (b,w))) := by
  rw [longCut, wordCap, cap_product]
  apply Finset.sum_congr rfl
  intro t _
  rw [split_symmetric _ hP, split_symmetric _ hH]
  rfl

/-- The full cut takes the Hermitian pairing along the last k input slots
and leaves the first p−k coordinates as an actual output word. -/
theorem longFull_entry {d p k : ℕ} {P : Word d p → ℂ} {H : Word d k → ℂ}
    (hP : Symmetric P) (hH : Symmetric H) (h : k ≤ p) (t : Word d (p-k)) (b : Word d (k-k)) :
    longCut P H (longFull h) (t,b) =
      ∑ w, P (joinAt (Nat.sub_add_cancel h) (t,w)) * star (H w) := by
  rw [longCut_entry hP hH]
  apply Finset.sum_congr rfl
  intro w _
  change _ * star (H (joinAt _ (b,w))) = _
  congr 2
  apply congrArg H
  funext i
  simp [joinAt, Fin.append_left_nil _ _ (Nat.sub_self k), Function.comp_def]

/-- With a fixed free word, the remaining positive and dual words have equal
length and form the rows and columns of a square matrix. -/
def longSlice {d p k : ℕ} (h : k ≤ p) (P : Word d p → ℂ) (H : Word d k → ℂ)
    (r : CutIndex p k) (t : Word d (p-k)) : Matrix (Word d (k-r)) (Word d (k-r)) ℂ :=
  fun a b => longCut P H r (freeSlots d h r (t,a), b)

theorem longSlice_trace {d p k : ℕ} {P : Word d p → ℂ} {H : Word d k → ℂ}
    (hP : Symmetric P) (hH : Symmetric H) (h : k ≤ p) (r : CutIndex p k) (t : Word d (p-k)) :
    (longSlice h P H r t).trace =
      ∑ w, P (joinAt (Nat.sub_add_cancel h) (t,w)) * star (H w) := by
  let e := joinAt (d := d) (Nat.sub_add_cancel (thinLe r))
  unfold Matrix.trace
  simp only [Matrix.diag, longSlice, longCut_entry hP hH]
  rw [← e.sum_comp (fun w => P (joinAt (Nat.sub_add_cancel h) (t,w)) * star (H w)),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro w _
  rw [freeSlots, joinAt_assoc _ (Nat.sub_add_cancel (thinLe r)) _ (Nat.sub_add_cancel h)]

theorem longSlice_columns {d p k : ℕ} {P : Word d p → ℂ}
    (hP : Symmetric P) (x : Fin k → Fin d → ℂ) (h : k ≤ p) (r : CutIndex p k)
    (t : Word d (p-k)) (b : Word d (k-r)) :
    (fun a => (longSlice h P (packet x) r t)ᴴ a b) ∈ PacketSupport.splitSupport x r (thinLe r) := by
  have he := PacketSupport.split_contraction_mem x r (thinLe r)
    (fun w => star (P (joinAt (Nat.sub_add_cancel (thickLe r)) (freeSlots d h r (t,b),w))))
  simpa only [Matrix.conjTranspose_apply, longSlice, longCut_entry hP (Bridges.packet_symmetric _ _ _),
    star_sum, star_mul', star_star, mul_comm (packet x _)] using he

/-- Completing all remaining pairs costs at most the dimension of the
subset support. The bound is uniform in the positive cable thickness. -/
theorem long_cap_energy {d p k : ℕ} {P : Word d p → ℂ} (hP : Symmetric P)
    (x : Fin k → Fin d → ℂ) (h : k ≤ p) (r : CutIndex p k) :
    energy (longCut P (packet x) (longFull h)) ≤ (k.choose r : ℝ) * energy (longCut P (packet x) r) := by
  let e := freeSlots d h r
  let H := packet x
  have hH : Symmetric H := Bridges.packet_symmetric _ _ x
  have full : energy (longCut P H (longFull h)) =
      ∑ t, Complex.normSq (longSlice h P H r t).trace := by
    unfold energy
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    change (∑ b : Word d (k-k), Complex.normSq (longCut P H (longFull h) (t,b))) = _
    simp_rw [longFull_entry hP hH h, longSlice_trace hP hH]
    simp only [Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, longFull, Nat.sub_self,
      pow_zero, one_smul]
  have cutEnergy : energy (longCut P H r) =
      ∑ t, ∑ a, ∑ b, Complex.normSq (longSlice h P H r t a b) := by
    unfold energy
    rw [Fintype.sum_prod_type, ← e.sum_comp, Fintype.sum_prod_type]
    rfl
  change energy (longCut P H _) ≤ _ * energy (longCut P H _)
  rw [full, cutEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hu := trace_of_adjoint_columns _ _ (longSlice_columns hP x h r t)
  refine hu.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact_mod_cast PacketSupport.splitSupport_dimension x r (thinLe r)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

def fiveFull (k : ℕ) : CutIndex (k+k) k := longFull (by omega)

/-- The (2k,k) case needed for the cap against the two-packet product. -/
theorem five_cap_energy {d k : ℕ} {P : Word d (k+k) → ℂ} (hP : Symmetric P)
    (x : Fin k → Fin d → ℂ) (r : CutIndex (k+k) k) :
    energy ((wordCap d (k+k) k (fiveFull k)).mulVec (product P (fun i => star (packet x i)))) ≤
      (k.choose r : ℝ) * energy ((wordCap d (k+k) k r).mulVec (product P (fun i => star (packet x i)))) :=
  long_cap_energy hP x (by omega) r

end
end BlockPermanents.ThreeSupport
