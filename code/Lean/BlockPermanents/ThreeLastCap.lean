import BlockPermanents.ThreeSupport
import BlockPermanents.Support
import BlockPermanents.ThreeTransfer

/-! Section 3D, resolving the last thin cap on the full mixed boundary.
An adapted orthonormal basis identifies the marked support with a set of
colours. No factorization of the boundary tensor is needed. -/
namespace BlockPermanents.ThreeLastCap
open Bend ThreeSupport PairBound Matrix
open scoped BigOperators Matrix
noncomputable section

variable {T I : Type*} [Fintype T] [DecidableEq T]
abbrev Pair (d : ℕ) := Word d 1 × Word d 1

def diagonal (d : ℕ) : Fin d ↪ Pair d where
  toFun c := (fun _ => c,fun _ => c)
  inj' := fun _ _ h => congrFun (congrArg Prod.fst h) 0

/-- Evaluation on the supported thin pair, with the spectator carried through. -/
def cap {d : ℕ} (S : Finset (Fin d)) : Matrix T (T × Pair d) ℂ :=
  fun t v => if t=v.1 ∧ v.2 ∈ S.map (diagonal d) then 1 else 0

private theorem cap_apply {d : ℕ} (S : Finset (Fin d)) (U : Matrix (T × Pair d) I ℂ) (t : T) (i : I) :
    (cap (T:=T) S * U : Matrix T I ℂ) t i = ∑ c ∈ S, U (t,diagonal d c) i := by
  rw [Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_eq_single t]
  · simp only [cap, true_and,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    rw [show Finset.univ.filter (fun z => z ∈ S.map (diagonal d)) = S.map (diagonal d)
      from Finset.ext (by simp)]
    exact Finset.sum_map _ _ _
  · intro t' _ h
    simp [cap,Ne.symm h]
  · simp

theorem cap_bubble {d : ℕ} (S : Finset (Fin d)) :
    cap (T:=T) S * (cap S)ᴴ = (S.card : ℂ) • (1 : Matrix T T ℂ) := by
  ext a b
  rw [cap_apply]
  by_cases hab : a=b
  · subst b
    simp [cap,Matrix.conjTranspose_apply]
  · simp [cap,Matrix.conjTranspose_apply,hab,Ne.symm hab]

/-- The full trace closes the remaining thin pair with coefficient one. -/
def fullTrace {d : ℕ} (U : Matrix (T × Pair d) I ℂ) : Matrix T I ℂ :=
  fun t i => ∑ c : Fin d, U (t,diagonal d c) i

theorem cap_eq_trace {d : ℕ} (S : Finset (Fin d)) (U : Matrix (T × Pair d) I ℂ)
    (hs : ∀ t c i, c ∉ S → U (t,diagonal d c) i=0) :
    cap S * U = fullTrace U := by
  ext t i
  rw [cap_apply]
  exact Finset.sum_subset (Finset.subset_univ S) (fun c _ hc => hs t c i hc)

def perpendicular {d : ℕ} (S : Finset (Fin d)) (U : Matrix (T × Pair d) I ℂ) :=
  ((1 : Matrix (T × Pair d) (T × Pair d) ℂ) - (S.card : ℂ)⁻¹ • ((cap (T:=T) S)ᴴ * cap S))*U

/-- Equality of operators on any (possibly entangled) mixed input.
Vanishing of the excluded diagonal entries is all that is required for the
final cap to agree with the unrestricted trace. -/
theorem resolve {d : ℕ} (S : Finset (Fin d)) (h : 0 < S.card)
    (U : Matrix (T × Pair d) I ℂ)
    (hs : ∀ t c i, c ∉ S → U (t,diagonal d c) i=0) :
    Support.reflected U = Support.reflected (perpendicular S U) +
      (S.card : ℂ)⁻¹ • Support.reflected (fullTrace U) := by
  have hh := Support.resolve_last_cap (cap S) U S.card h (cap_bubble S)
  simpa only [cap_eq_trace S U hs] using hh

/-- The last proper cut on k=n+1 strands, including all n shared word slots. -/
def lastCut (n : ℕ) : CutIndex (n+1) (n+1) := ⟨n,by simp;omega⟩

private def oneWord (d n : ℕ) : Fin d ≃ Word d ((n+1)-n) :=
  (Equiv.funUnique (Fin 1) (Fin d)).symm.trans
    ((finCongr (by omega : 1 = (n+1)-n)).arrowCongr (Equiv.refl _))

private def wholeWord (d n : ℕ) : Fin d × Word d n ≃ Word d (n+1) :=
  ((oneWord d n).prodCongr (Equiv.refl _)).trans (splitWords d (n+1) (lastCut n))

/-- A k−1 cap with an arbitrary upright merge. The two output word
coordinates each have one strand. -/
def proper {d n : ℕ} (M : Matrix (T × Word d (n+1)) I ℂ) :
    Matrix (T × Pair d) (I × Word d (n+1)) ℂ := fun a x =>
  ∑ y, M (a.1,y) x.1 * wordCap d (n+1) (n+1) (lastCut n)
    (fun _ => a.2.1 0,fun _ => a.2.2 0) (y,x.2)

/-- The full k-cap of the same diagram, read directly on the full word
indices. The spectator is the only output. -/
def full {d k : ℕ} (M : Matrix (T × Word d k) I ℂ) :
    Matrix T (I × Word d k) ℂ := fun t x =>
  ∑ y, M (t,y) x.1 * ∑ w, symClasp d k w y * star (symClasp d k w x.2)

omit [Fintype T] [DecidableEq T] in
/-- Closing the last pair regroups the k word slots bijectively. -/
theorem trace_partial {d n : ℕ} (M : Matrix (T × Word d (n+1)) I ℂ) :
    fullTrace (proper M) = full M := by
  ext t x
  unfold fullTrace proper full
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Prod.fst,Prod.snd]
  rw [← Finset.mul_sum]
  congr 1
  let f (w : Word d (n+1)) := symClasp d (n+1) w y * star (symClasp d (n+1) w x.2)
  have he := (wholeWord d n).sum_comp f
  rwa [Fintype.sum_prod_type] at he

private theorem unsupported {d k : ℕ} {S : Finset (Fin d)} {x y : Word d k}
    (h : ∃ i, x i ∉ S) (hy : ∀ i, y i ∈ S) : symClasp d k x y = 0 := by
  obtain ⟨i,hi⟩ := h
  have he (p : Equiv.Perm (Fin k)) : x ≠ y ∘ p := fun hh => hi (hh ▸ hy (p i))
  simp [symClasp,he]

/-- Restrict the marked input to all words in a support (and hence all
their arbitrary linear combinations). -/
def restrictMarked {d k : ℕ} (S : Finset (Fin d)) (U : Matrix T (I × Word d k) ℂ) :
    Matrix T (I × {z : Word d k // ∀ j, z j ∈ S}) ℂ := fun t z => U t (z.1,z.2.val)

private theorem starts {d n : ℕ} (c : Fin d) (w : Word d n) :
    wholeWord d n (c,w) 0=c := by
  change Fin.append (fun _ : Fin ((n+1)-n) => c) w _ = c
  let i : Fin ((n+1)-n) := ⟨0,by omega⟩
  rw [show Fin.cast (Nat.sub_add_cancel (cut_le (lastCut n))).symm (0:Fin (n+1)) =
    Fin.castAdd n i from Fin.ext rfl,Fin.append_left]

omit [Fintype T] [DecidableEq T] in
private theorem partial_outside {d n : ℕ} (S : Finset (Fin d))
    (M : Matrix (T × Word d (n+1)) I ℂ) (t : T) (a b : Fin d) (i : I)
    (z : {w : Word d (n+1) // ∀ j, w j∈S}) (hb : b∉S) :
    restrictMarked S (proper M) (t,((fun _ => a),(fun _ => b))) (i,z)=0 := by
  apply Finset.sum_eq_zero
  intro y _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro w _
  change _ * star (symClasp d (n+1) (wholeWord d n (b,w)) z.1) = 0
  rw [unsupported ⟨0,by rw [starts]; exact hb⟩ z.2,star_zero,mul_zero]

/-- Exact resolution of the concrete k−1 routed contraction as an operator
on the entire supported mixed boundary. The upright map may entangle its inputs. -/
theorem concrete_resolution {d n : ℕ} (S : Finset (Fin d)) (h : 0<S.card)
    (M : Matrix (T × Word d (n+1)) I ℂ) :
    Support.reflected (restrictMarked S (proper M)) =
      Support.reflected (perpendicular S (restrictMarked S (proper M))) +
        (S.card:ℂ)⁻¹ • Support.reflected (restrictMarked S (full M)) := by
  have hh := resolve S h (restrictMarked S (proper M)) (fun t c i hc =>
    partial_outside S M t c c i.1 i.2 hc)
  have full' : fullTrace (restrictMarked S (proper M)) = restrictMarked S (full M) := by
    rw [← trace_partial]
    rfl
  rw [full'] at hh
  exact hh

omit [Fintype T] [DecidableEq T] in
/-- Identification with the full actual word cap, whose two survivors are
empty words. -/
theorem full_wordCap {d k : ℕ} (M : Matrix (T × Word d k) I ℂ) (t : T)
    (i : I) (z : Word d k) (u v : Word d (k-k)) :
    full M t (i,z) = ∑ y, M (t,y) i * wordCap d k k (fullCut k) (u,v) (y,z) := by
  simp only [full,wordCap,cap, Bend.cap,wordFork,fullCut,
    Fin.append_left_nil _ _ (Nat.sub_self k),Function.comp_def]
  rfl

/-- The ordinary two-packet projector f=(id+swap)/2. -/
def pairMerge (d k : ℕ) : Matrix (Word d k × Word d k) (Word d k × Word d k) ℂ :=
  fun y a => ((if y=a then 1 else 0)+(if y=a.swap then 1 else 0))/2

/-- Section 3D.1 with the precise U averaging the two ordinary placements. -/
theorem pair_resolution {d n : ℕ} (S : Finset (Fin d)) (hs : 0<S.card) :
    Support.reflected (restrictMarked S (proper (pairMerge d (n+1)))) =
      Support.reflected (perpendicular S (restrictMarked S (proper (pairMerge d (n+1))))) +
      (S.card:ℂ)⁻¹ • Support.reflected (restrictMarked S (full (pairMerge d (n+1)))) :=
  concrete_resolution S hs _

private theorem glue_energy {A B : Type*} [Fintype A] [Fintype B] (Y : Matrix B A ℂ) (v : A → ℂ) :
    quadratic (Support.reflected Y) v = (energy (Y.mulVec v) : ℂ) := by
  rw [Support.reflected,quadratic_reflected]
  exact (map_sum Complex.ofRealHom _ _).symm

private theorem quadratic_add_smul {A : Type*} [Fintype A] (X Y : Matrix A A ℂ) (c : ℂ) (v : A→ℂ) :
    quadratic (X+c • Y) v = quadratic X v+c*quadratic Y v := by
  simp only [quadratic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The norm equality on every vector in the supported tensor product,
without any simple-tensor restriction. -/
theorem energy_resolution {d n : ℕ} [Fintype I] (S : Finset (Fin d)) (h : 0<S.card)
    (M : Matrix (T × Word d (n+1)) I ℂ)
    (v : (I × {w : Word d (n+1) // ∀ j,w j∈S}) → ℂ) :
    energy ((restrictMarked S (proper M)).mulVec v) =
      energy ((perpendicular S (restrictMarked S (proper M))).mulVec v) +
      energy ((restrictMarked S (full M)).mulVec v) / S.card := by
  have he := congrArg (fun A => quadratic A v) (concrete_resolution S h M)
  dsimp only at he
  rw [quadratic_add_smul,glue_energy,glue_energy,glue_energy] at he
  have hh := congrArg Complex.re he
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,
    ← Complex.ofReal_add,Complex.ofReal_re,div_eq_mul_inv,mul_comm] using hh

end
end BlockPermanents.ThreeLastCap
