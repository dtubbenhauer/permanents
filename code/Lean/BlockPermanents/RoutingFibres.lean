import BlockPermanents.Routings
import BlockPermanents.Transfer
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Sum

/-! # Thin permutations with a prescribed routing table -/

namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

abbrev Fibre {X J : Type*} (g : X → J) (j : J) := { x : X // g x=j }
abbrev Coordinate (X : Type*) {J : Type*} (T : J → Type*) := X ≃ Σ j, T j

def sigmaValue {J : Type*} {T : J → Type*} (j : J) :
    {a : (Σ i,T i) // a.1=j} ≃ T j where
  toFun a := a.property ▸ a.val.2
  invFun t := ⟨⟨j,t⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,t⟩,rfl⟩;rfl
  right_inv _ := rfl

abbrev Profile {X J : Type*} {T : J → Type*} (e : Coordinate X T) (x : X) := (e x).1

/-- A labeling inside each fiber of the first coordinate is exactly the
remaining information needed to specify a bijection of all the thin slots. -/
def labelEquiv {X J : Type*} {T : J → Type*} (g : X → J) :
    (∀ j, Fibre g j ≃ T j) ≃ {e : Coordinate X T // Profile e = g} where
  toFun l := ⟨(sigmaFiberEquiv g).symm.trans (sigmaCongrRight l),rfl⟩
  invFun e j := (e.val.subtypeEquiv (fun x => by
    change (g x = j) ↔ (Profile e.val x = j);rw [e.property])).trans (sigmaValue j)
  left_inv l := by funext j;apply Equiv.ext;intro x;rcases x with ⟨x,rfl⟩;rfl
  right_inv e := by
    apply Subtype.ext;apply Equiv.ext;intro x
    rcases e with ⟨e,h⟩
    subst g
    exact Sigma.eta _

variable {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]

/-- Multiplicities of the individual letters in a labeling. -/
def profileSize (g : X → J) (j : J) := Fintype.card (Fibre g j)

abbrev Assignment (X : Type*) {J : Type*} [Fintype X] [DecidableEq J] (v : J → ℕ) :=
  {g : X → J // profileSize g = v}

def project {T : J → Type*} [∀ j,Fintype (T j)] (e : Coordinate X T) :
    Assignment X (fun j => Fintype.card (T j)) :=
  ⟨Profile e, funext fun j => Fintype.card_congr ((labelEquiv (Profile e)).symm ⟨e,rfl⟩ j)⟩

private def projectFibre {T : J → Type*} [∀ j,Fintype (T j)]
    (g : Assignment X (fun j => Fintype.card (T j))) :
    Fibre (project (X := X) (T := T)) g ≃ (∀ j,Fibre g.val j ≃ T j) :=
  (Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)).trans (labelEquiv g.val).symm

/-- The size of the permutations inside a fixed letter assignment. -/
theorem project_fibre_card {T : J → Type*} [∀ j,Fintype (T j)] [∀ j,DecidableEq (T j)] [DecidableEq X]
    (g : Assignment X (fun j => Fintype.card (T j))) :
    Fintype.card (Fibre (project (X := X) (T := T)) g) = ∏ j, (Fintype.card (T j)).factorial := by
  classical
  rw [Fintype.card_congr (projectFibre g), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro j _
  let e : Fibre g.val j ≃ T j := Fintype.equivOfCardEq (congrFun g.property j)
  simpa [← congrFun g.property j,profileSize] using Fintype.card_equiv e

/-- The number of words with given occupations, in a division-free form. -/
theorem assignment_count (v : J → ℕ) [DecidableEq X] (h : ∑ j,v j = Fintype.card X) :
    Fintype.card (Assignment X v) * (∏ j, (v j).factorial) = (Fintype.card X).factorial := by
  classical
  let T := fun j => Fin (v j)
  have hv : (fun j => Fintype.card (T j)) = v := funext fun j => Fintype.card_fin _
  have he : X ≃ Σ j,T j := Fintype.equivOfCardEq (by simp [T,h])
  have hc := Fintype.card_congr (sigmaFiberEquiv (project (X := X) (T := T)))
  rw [Fintype.card_sigma] at hc
  simp_rw [project_fibre_card] at hc
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_equiv he] at hc
  simpa only [hv,T,Fintype.card_fin] using hc

abbrev Slot (m k : ℕ) := Fin m × Fin k
abbrev Wire (m k : ℕ) := Perm (Slot m k)

private theorem size_sum (g : X → J) : (∑ j, profileSize g j) = Fintype.card X := by
  simpa only [Fintype.card_sigma,profileSize] using Fintype.card_congr (sigmaFiberEquiv g)

private def grouped {m k : ℕ} (g : Slot m k → Fin m) (j : Fin m) :
    (Σ i : Fin m, Fibre (fun t => g (i,t)) j) ≃ Fibre g j where
  toFun t := ⟨(t.1,t.2.val),t.2.property⟩
  invFun t := ⟨t.val.1, t.val.2,t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem grouped_size {m k : ℕ} (g : Slot m k → Fin m) (j : Fin m) :
    (∑ i, profileSize (fun t => g (i,t)) j) = profileSize g j := by
  simpa only [Fintype.card_sigma,profileSize] using Fintype.card_congr (grouped g j)

private def asCoord {m k : ℕ} (p : Wire m k) : Coordinate (Slot m k) (fun _ : Fin m => Fin k) :=
  p.trans (sigmaEquivProd _ _).symm

/-- The actual strand-permutation routing matrix. -/
def table {m k : ℕ} (p : Wire m k) : Routing m k where
  entries i := profileSize fun t => (p (i,t)).1
  rowSum i := (size_sum (fun t => (p (i,t)).1)).trans (Fintype.card_fin _)
  colSum j := by
    rw [grouped_size (fun x => (p x).1)]
    exact (congrFun (project (asCoord p)).property j).trans (Fintype.card_fin _)

@[ext] theorem table_ext {m k : ℕ} {M N : Routing m k} (h : ∀ i j, M.entries i j = N.entries i j) :
    M=N := by
  rcases M with ⟨M,_,_⟩;rcases N with ⟨N,_,_⟩
  congr;funext i j;exact h i j

private def bounded {m k : ℕ} (M : Routing m k) (i j : Fin m) : Fin (k+1) :=
  ⟨M.entries i j, Nat.lt_succ_of_le (by
    exact (Finset.single_le_sum (f := M.entries i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq (M.rowSum i))⟩

instance {m k : ℕ} : Finite (Routing m k) :=
  Finite.of_injective bounded (fun _ _ he => table_ext fun i j =>
    congrArg Fin.val (congrFun (congrFun he i) j))
noncomputable instance {m k : ℕ} : Fintype (Routing m k) := Fintype.ofFinite _
noncomputable instance {m k : ℕ} : DecidableEq (Routing m k) := Classical.decEq _

abbrev RowAssignments {m k : ℕ} (M : Routing m k) :=
  ∀ i, Assignment (Fin k) (M.entries i)

private def toRows {m k : ℕ} (M : Routing m k) (p : Fibre table M) : RowAssignments M :=
  fun i => ⟨fun t => (p.val (i,t)).1,congrArg (fun N : Routing m k => N.entries i) p.property⟩

private def wordOf {m k : ℕ} {M : Routing m k} (g : RowAssignments M) (u : Slot m k) : Fin m :=
  (g u.1).val u.2

private theorem colSize {m k : ℕ} {M : Routing m k} (g : RowAssignments M) (j : Fin m) :
    profileSize (wordOf g) j = k := by
  rw [← grouped_size]
  have h (i : Fin m) : profileSize (fun t => wordOf g (i,t)) j = M.entries i j :=
    congrFun (g i).property j
  simpa only [h] using M.colSum j

private def byRows {m k : ℕ} (M : Routing m k) (g : RowAssignments M) :
    Fibre (toRows M) g ≃ {p : Coordinate (Slot m k) (fun _ : Fin m => Fin k) //
      Profile p = wordOf g} where
  toFun p := ⟨asCoord p.val.val,by
    funext u
    exact congrFun (congrArg Subtype.val (congrFun p.property u.1)) u.2⟩
  invFun e := by
    let p := e.val.trans (sigmaEquivProd _ _)
    have he (i : Fin m) : (fun t => (p (i,t)).1) = (g i).val :=
      funext fun t => congrFun e.property (i,t)
    have hp : table p = M := table_ext fun i j => by
      change profileSize (fun t => (p (i,t)).1) j = _
      rw [he i];exact congrFun (g i).property j
    exact ⟨⟨p,hp⟩,funext fun i => Subtype.ext (he i)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem rows_fibre_card {m k : ℕ} (M : Routing m k) (g : RowAssignments M) :
    Fintype.card (Fibre (toRows M) g) = k.factorial^m := by
  classical
  rw [Fintype.card_congr (byRows M g),Fintype.card_congr (labelEquiv (wordOf g)).symm,Fintype.card_pi]
  have h (j : Fin m) : Fintype.card (Fibre (wordOf g) j ≃ Fin k) = k.factorial := by
    let e : Fibre (wordOf g) j ≃ Fin k :=
      Fintype.equivOfCardEq ((colSize g j).trans (Fintype.card_fin k).symm)
    exact (Fintype.card_equiv e).trans (congrArg Nat.factorial (colSize g j))
  simp [h]

/-- Cardinality of a double coset of within-packet strand permutations,
before any thin permutation has been normalized. -/
theorem fibre_multiplicity {m k : ℕ} (M : Routing m k) :
    Fintype.card (Fibre table M) * (∏ i, ∏ j, (M.entries i j).factorial) =
      k.factorial^(2*m) := by
  classical
  have h := Fintype.card_congr (sigmaFiberEquiv (toRows M))
  rw [Fintype.card_sigma] at h
  change (∑ g : RowAssignments M, Fintype.card (Fibre (toRows M) g)) = _ at h
  simp only [rows_fibre_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have a (i : Fin m) : Fintype.card (Assignment (Fin k) (M.entries i)) *
      (∏ j, (M.entries i j).factorial) = k.factorial := by
    simpa only [Fintype.card_fin] using assignment_count (X := Fin k) (M.entries i)
      ((M.rowSum i).trans (Fintype.card_fin k).symm)
  have ha : Fintype.card (RowAssignments M) * (∏ i, ∏ j, (M.entries i j).factorial) =
      k.factorial^m := by
    rw [Fintype.card_pi,← Finset.prod_mul_distrib]
    simp [a]
  simp only [Nat.cast_id] at h
  rw [← h,mul_right_comm,ha,two_mul,pow_add]

theorem fibre_card {m k : ℕ} (M : Routing m k) :
    Fintype.card (Fibre table M) = k.factorial^(2*m) / (∏ i, ∏ j, (M.entries i j).factorial) := by
  rw [← fibre_multiplicity M,Nat.mul_div_cancel _ (by positivity)]

/-- Every nonnegative integer table with the stated margins really occurs. -/
theorem realizable {m k : ℕ} (M : Routing m k) : ∃ p : Wire m k, table p = M := by
  have hc := fibre_multiplicity M
  have h : Fintype.card (Fibre table M) ≠ 0 := by
    intro hz;rw [hz,zero_mul] at hc;exact (Nat.ne_of_gt (pow_pos (Nat.factorial_pos _) _)) hc.symm
  obtain ⟨p,hp⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
  exact ⟨p,hp⟩

end
end BlockPermanents.RoutingFibres
