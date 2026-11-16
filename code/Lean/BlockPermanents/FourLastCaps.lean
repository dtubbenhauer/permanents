import BlockPermanents.Routings
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.Group.Multiset

/-! # Closing two last-cap routes on symmetric word coefficients

An occupation is the multiset of letters of a word. A reflected cap chooses
one of the slots in its port and inserts a supported dual letter. After a
second cap the two possible traces are evaluated directly at these slots.
-/
namespace BlockPermanents.FourLastCaps
open scoped BigOperators
open Equiv Routings
noncomputable section

variable {I D : Type*} [Fintype I] [DecidableEq I] [DecidableEq D]

/-- The multiset of letters in an ordered word, including repetitions. -/
def occupation {T : Type*} [Fintype T] (w : T → D) : Multiset D := ∑ i, {w i}

def insertAt (a : Option I) (w : I → D) (c : D) (i : Option I) : D :=
  (Equiv.swap none a i).elim c w

def deleteAt (a : Option I) (w : Option I → D) (i : I) : D := w (Equiv.swap none a (some i))

omit [DecidableEq D] in
private theorem occupation_delete (a : Option I) (x : Option I → D) :
    {x a} + occupation (deleteAt a x) = occupation x := by
  unfold occupation deleteAt
  have h := Equiv.sum_comp (Equiv.swap none a) (fun i => ({x i} : Multiset D))
  rwa [Fintype.sum_option, swap_apply_left] at h

omit [DecidableEq D] in
private theorem delete_equal (a b : Option I) (x : Option I → D) (h : x a = x b) :
    occupation (deleteAt a x) = occupation (deleteAt b x) := by
  apply add_left_cancel (a := ({x a} : Multiset D))
  rw [occupation_delete, h, occupation_delete]

/-- Insert a supported color at port `b` in a reflected symmetric test
vector. `f` specifies the values in the occupation-word coordinates. -/
def cupAt (b : Option I) (f : Multiset D → ℂ) (w : Option I → D) (c : D) :=
  if w b = c then f (occupation (deleteAt b w)) else 0

/-- The adjoining cap reads the raw word with the marked color inserted.
The two slots here can belong to the same port or to different ports. -/
def glueAt (S : Finset D) (a b : Option I) (f : Multiset D → ℂ) (w : I → D) :=
  ∑ c ∈ S, cupAt b f (insertAt a w c) c

omit [Fintype I] [DecidableEq D] in
private lemma insert_own (a : Option I) (w : I → D) (c : D) : insertAt a w c a = c := by
  simp [insertAt]
omit [Fintype I] [DecidableEq D] in
private lemma delete_insert (a : Option I) (w : I → D) (c : D) :
    deleteAt a (insertAt a w c) = w := by funext i; simp [deleteAt,insertAt]

/-- A return to the same slot closes one supported loop. -/
theorem same_slot (S : Finset D) (a : Option I) (f : Multiset D → ℂ) (w : I → D) :
    glueAt S a a f w = (S.card : ℂ) * f (occupation w) := by
  simp [glueAt,cupAt,insert_own,delete_insert]

/-- The index of the strand from one distinct slot to another among the
surviving slots. -/
private def survivor (a b : Option I) (h : a ≠ b) : I :=
  ((Equiv.swap none a) b).get (by
    rw [Option.isSome_iff_ne_none]
    intro he; exact h ((Equiv.swap none a).injective ((swap_apply_right none a).trans he.symm)))

omit [Fintype I] in
private lemma survivor_spec (a b : Option I) (h : a ≠ b) :
    some (survivor a b h) = (Equiv.swap none a) b := Option.some_get _

/-- Distinct slots force equality of the two letters at the turns and test
exactly one surviving strand against the marked support. -/
theorem different_slots (S : Finset D) {a b : Option I} (h : a ≠ b)
    (f : Multiset D → ℂ) (w : I → D) :
    glueAt S a b f w = if w (survivor a b h) ∈ S then f (occupation w) else 0 := by
  have hi (c : D) : insertAt a w c b = w (survivor a b h) := by
    unfold insertAt; rw [← survivor_spec a b h]; rfl
  have he (c : D) (hc : w (survivor a b h) = c) :
      occupation (deleteAt b (insertAt a w c)) = occupation w := by
    rw [delete_equal b a (insertAt a w c) (by rw [hi,insert_own,hc]), delete_insert]
  unfold glueAt cupAt
  simp_rw [hi]
  calc
    _ = ∑ c ∈ S, if w (survivor a b h) = c then f (occupation w) else 0 := by
      apply Finset.sum_congr rfl
      intro c _; split_ifs with eq
      · rw [he _ eq]
      · rfl
    _ = _ := by simp

/-- The actual port cap on arbitrary ordered input coefficients. The output
is projected onto symmetric four-strand words. The positive input positions
are `none,some 0,some 1,some 2,some 3`. -/
def portCap (S : Finset D) (P : Finset (Option (Fin 4)))
    (z : (Option (Fin 4) → D) → D → ℂ) (w : Fin 4 → D) :=
  ((P.card : ℂ) * 24)⁻¹ * ∑ σ : Equiv.Perm (Fin 4), ∑ a ∈ P,
    ∑ c ∈ S, z (insertAt a (w ∘ σ) c) c

/-- On an occupation test function, a port's reflected cap averages over
the available positive slots, pairing the supported color with each. -/
def portCup (P : Finset (Option (Fin 4))) (f : Multiset D → ℂ)
    (w : Option (Fin 4) → D) (c : D) := (P.card : ℂ)⁻¹ * ∑ b ∈ P, cupAt b f w c

omit [DecidableEq D] in
private theorem occupation_permute {T : Type*} [Fintype T] (w : T → D) (σ : Perm T) :
    occupation (w ∘ σ) = occupation w := Equiv.sum_comp σ (fun i => ({w i} : Multiset D))

/-- Number of the four surviving ordinary slots on which a supported color
is present. -/
def density (S : Finset D) (w : Fin 4 → D) : ℝ :=
  ((Finset.univ.filter fun i => w i ∈ S).card : ℝ) / 4

private theorem countSlot (S : Finset D) (w : Fin 4 → D) (i : Fin 4) :
    (∑ σ : Perm (Fin 4), if w (σ i) ∈ S then (1:ℂ) else 0) = 24 * (density S w : ℂ) := by
  have hi := (Group.mulRight_bijective (swap 0 i)).sum_comp
    (fun σ : Perm (Fin 4) => if w (σ 0) ∈ S then (1:ℂ) else 0)
  simp only [Perm.mul_apply, swap_apply_left] at hi
  rw [hi, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product,
    Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Finset.sum_filter]; norm_num [density, Nat.factorial]; ring

private theorem slotSum (S : Finset D) (a b : Option (Fin 4)) (f : Multiset D → ℂ) (w : Fin 4 → D) :
    (∑ σ : Perm (Fin 4), glueAt S a b f (w ∘ σ)) =
      24 * (if a=b then (S.card:ℂ) else (density S w : ℂ)) * f (occupation w) := by
  classical
  split_ifs with h
  · subst b; simp [same_slot, occupation_permute, Fintype.card_perm, Nat.factorial]
    ring
  · simp_rw [different_slots S h, occupation_permute]
    have hi (σ : Perm (Fin 4)) : (if (w ∘ σ) (survivor a b h) ∈ S then f (occupation w) else 0) =
       (if w (σ (survivor a b h)) ∈ S then (1:ℂ) else 0) * f (occupation w) := by split_ifs <;> simp_all
    simp_rw [hi]
    rw [← Finset.sum_mul, countSlot]


private lemma count_ports {T : Type*} [DecidableEq T] (P Q : Finset T) (s ρ : ℂ) :
    (∑ a ∈ P, ∑ b ∈ Q, if a=b then s else ρ) =
      (P.card : ℂ)*Q.card*ρ + ((P ∩ Q).card : ℂ)*(s-ρ) := by
  have h (a b : T) : (if a=b then s else ρ) = ρ + (if a=b then s-ρ else 0) := by split_ifs <;> ring
  simp_rw [h,Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq]
  rw [← Finset.sum_filter, show P.filter (fun a => a ∈ Q) = P ∩ Q by ext; simp]
  simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The cap and reflected cap on actual words. A common slot closes a loop;
all other pairs carry a supported color along one of the four ordinary
survivors. The formula also permits overlapping, unequal ports. -/
theorem port_gluing (S : Finset D) (P Q : Finset (Option (Fin 4))) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (f : Multiset D → ℂ) (w : Fin 4 → D) :
    portCap S P (portCup Q f) w =
      ((density S w : ℂ) + ((P∩Q).card : ℂ)/((P.card : ℂ)*Q.card)*((S.card : ℂ)-(density S w : ℂ))) * f (occupation w) := by
  have hp : (P.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hP
  have hq : (Q.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hQ
  unfold portCap portCup
  simp_rw [← Finset.mul_sum]
  rw [show (∑ σ : Perm (Fin 4), ∑ a ∈ P, ∑ c ∈ S, ∑ b ∈ Q,
      cupAt b f (insertAt a (w ∘ σ) c) c) =
      ∑ a ∈ P, ∑ b ∈ Q, ∑ σ : Perm (Fin 4), glueAt S a b f (w ∘ σ) by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
    simp_rw [Finset.sum_comm (s:=S) (t:=Q)]; rw [Finset.sum_comm]; rfl]
  simp_rw [slotSum, ← Finset.sum_mul, ← Finset.mul_sum, count_ports]
  field_simp; ring


/-- On disjoint ports, gluing the actual word maps gives the entry
of the last-cap Gram matrix, pointwise on every symmetric output. -/
theorem port_gluing_gram {J : Type*} [DecidableEq J] (S : Finset D) (P : J → Finset (Option (Fin 4)))
    (d : J → ℕ) (hP : ∀ i, (P i).card = d i+1) (hD : ∀ i j, i≠j → Disjoint (P i) (P j))
    (i j : J) (f : Multiset D → ℂ) (w : Fin 4 → D) :
    portCap S (P i) (portCup (P j) f) w = Routings.capGram d S.card (density S w) i j * f (occupation w) := by
  have hn (i : J) : (P i).Nonempty := Finset.card_pos.mp (by rw [hP]; omega)
  rw [port_gluing S _ _ (hn i) (hn j)]
  unfold Routings.capGram
  by_cases hij : i=j
  · subst j
    simp only [Finset.inter_self, hP, Nat.cast_add_one, if_true]
    push_cast
    have h : (d i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d i)
    field_simp
  · simp [Finset.disjoint_iff_inter_eq_empty.mp (hD _ _ hij), hij]

/-- Computing the sector density on a multiset makes its permutation
invariance and the possible values after relabeling explicit. -/
def bagDensity (S : Finset D) (B : Multiset D) : ℝ := ((B.filter (· ∈ S)).card : ℝ)/4

lemma bagDensity_word (S : Finset D) (w : Fin 4 → D) : bagDensity S (occupation w) = density S w := by
  have hc := map_sum (Multiset.countPAddMonoidHom (fun i => i ∈ S)) (fun i => ({w i} : Multiset D)) Finset.univ
  change (Multiset.countP (fun i => i ∈ S) (occupation w)) = _ at hc
  have hn : ((occupation w).filter (fun i => i ∈ S)).card = (Finset.univ.filter fun i => w i ∈ S).card := by
    rw [← Multiset.countP_eq_card_filter, hc, Finset.card_filter]
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : w i ∈ S <;> simp [Multiset.countPAddMonoidHom,← Multiset.cons_zero,Multiset.countP_cons,hi]
  unfold bagDensity density; rw [hn]

lemma density_nonneg (S : Finset D) (w : Fin 4 → D) : 0 ≤ density S w := by
  unfold density; positivity
lemma density_le_one (S : Finset D) (w : Fin 4 → D) : density S w ≤ 1 := by
  unfold density
  have hc : (Finset.univ.filter fun i => w i ∈ S).card ≤ 4 :=
    by simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_filter_le Finset.univ (fun i => w i ∈ S)
  rw [div_le_one (by norm_num)]; exact_mod_cast hc

/-- Coordinates for the marked input use ordinary ordered words and one
supported dual color. -/
def rawPair [Fintype D] (S : Finset D) (u v : (Option (Fin 4) → D) → D → ℂ) : ℂ :=
  ∑ t, ∑ c ∈ S, star (u t c) * v t c

/-- Pair a symmetric output test against any ordered complex four-tensor. -/
def outPair [Fintype D] (f : Multiset D → ℂ) (v : (Fin 4 → D) → ℂ) : ℂ :=
  ∑ w, star (f (occupation w)) * v w

def splitWord (a : Option (Fin 4)) : (Option (Fin 4) → D) ≃ D × (Fin 4 → D) where
  toFun x := (x a, deleteAt a x)
  invFun z := insertAt a z.2 z.1
  left_inv x := by
    funext t
    change ((swap none a) t).elim (x a) (deleteAt a x) = x t
    cases h : Equiv.swap none a t with
    | none =>
      have he : t=a := (Equiv.swap none a).injective (h.trans (swap_apply_right _ _).symm)
      subst t; rfl
    | some j =>
      change x ((Equiv.swap none a) (some j)) = x t
      rw [← h, swap_apply_self]
  right_inv z := by simp [insert_own, delete_insert]

private theorem adjoint_one [Fintype D] (S : Finset D) (a : Option (Fin 4))
    (f : Multiset D → ℂ) (z : (Option (Fin 4) → D) → D → ℂ) :
    rawPair S (cupAt a f) z =
      ∑ w, ∑ c ∈ S, star (f (occupation w)) * z (insertAt a w c) c := by
  unfold rawPair
  rw [← Equiv.sum_comp (splitWord a).symm, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  change (∑ x : D, star (cupAt a f (insertAt a w x) c) * z (insertAt a w x) c) = _
  simp only [cupAt,insert_own,delete_insert,apply_ite star,star_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

omit [DecidableEq D] in
private theorem rotate_sum [Fintype D] (f : Multiset D → ℂ) (g : (Fin 4 → D) → ℂ)
    (σ : Perm (Fin 4)) : (∑ w, star (f (occupation w)) * g (w ∘ σ)) = outPair f g := by
  have h := Equiv.sum_comp (σ.symm.arrowCongr (Equiv.refl D))
    (fun w => star (f (occupation w)) * g w)
  convert h using 1
  apply Finset.sum_congr rfl; intro w _
  change _ = star (f (occupation (w ∘ σ))) * g (w ∘ σ)
  rw [occupation_permute]

omit [DecidableEq D] in
theorem raw_sum_left [Fintype D] {T : Type*} (P : Finset T) (S : Finset D)
    (u : T → (Option (Fin 4) → D) → D → ℂ) (z : (Option (Fin 4) → D) → D → ℂ) :
    rawPair S (fun w c => ∑ a ∈ P, u a w c) z = ∑ a ∈ P, rawPair S (u a) z := by
  unfold rawPair
  simp only [star_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := P)]
  apply Finset.sum_congr rfl; intro t _; exact Finset.sum_comm

omit [DecidableEq D] in
lemma raw_scale [Fintype D] (a : ℂ) (S : Finset D) (u z : (Option (Fin 4) → D) → D → ℂ) :
    rawPair S (fun w c => a * u w c) z = star a * rawPair S u z := by
  simp only [rawPair, star_mul', Finset.mul_sum, mul_assoc]

omit [DecidableEq D] in
lemma out_sum [Fintype D] {T : Type*} (P : Finset T) (f : Multiset D → ℂ)
    (v : T → (Fin 4 → D) → ℂ) :
    outPair f (fun w => ∑ a ∈ P, v a w) = ∑ a ∈ P, outPair f (v a) := by
  simp only [outPair, Finset.mul_sum]; exact Finset.sum_comm

omit [DecidableEq D] in
lemma out_scale [Fintype D] (f : Multiset D → ℂ) (a : ℂ) (u : (Fin 4 → D) → ℂ) :
    outPair f (fun w => a * u w) = a * outPair f u := by
  unfold outPair; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- The reflected port map is the adjoint of the cap on every symmetric
output test, including complex coefficients and support restriction. -/
theorem port_adjoint [Fintype D] (S : Finset D) (P : Finset (Option (Fin 4)))
    (f : Multiset D → ℂ) (z : (Option (Fin 4) → D) → D → ℂ) :
    rawPair S (portCup P f) z = outPair f (portCap S P z) := by
  unfold portCup portCap
  rw [raw_scale, raw_sum_left, out_scale, out_sum]
  simp_rw [adjoint_one]
  let core := fun w : Fin 4 → D => ∑ a ∈ P, ∑ c ∈ S, z (insertAt a w c) c
  have hσ (σ : Perm (Fin 4)) : outPair f (fun w => core (w ∘ σ)) = outPair f core :=
    rotate_sum f core σ
  change _ = ((P.card : ℂ)*24)⁻¹ * ∑ σ : Perm (Fin 4), outPair f (fun w => core (w ∘ σ))
  simp only [hσ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,Fintype.card_fin, nsmul_eq_mul,
    star_inv₀, star_natCast]
  norm_num [Nat.factorial, mul_inv_rev, ← mul_assoc]
  unfold core
  rw [out_sum]
  simp only [outPair,Finset.mul_sum]
  rw [show (1/24 : ℂ)*(P.card : ℂ)⁻¹*24 = (P.card : ℂ)⁻¹ by ring]
  rfl

end
end BlockPermanents.FourLastCaps
