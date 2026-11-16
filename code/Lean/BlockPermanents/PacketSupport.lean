import BlockPermanents.Closures
import BlockPermanents.Bend
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Powerset

/-! The support of a decomposable packet after splitting off a set of slots
(Section 7A). The two blocks of slots are A and B. Freezing the A-coordinates
leaves a B-word tensor in the span of at most (|A|+|B| choose |B|) vectors. -/

namespace BlockPermanents.PacketSupport
open scoped BigOperators
open Closures
noncomputable section

variable {A B D : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Subsets which can supply the surviving B-slots. -/
abbrev Subsets (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :=
  ↥((Finset.univ : Finset (A ⊕ B)).powersetCard (Fintype.card B))

private def enumerate (s : Subsets A B) : B ≃ ↥(s.val) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, (Finset.mem_powersetCard.mp s.property).2])

/-- Unnormalized symmetric product of the factors in the selected subset.
Its value is independent of the choice of ordering. -/
def partialPacket (x : A ⊕ B → D → ℂ) (s : Subsets A B) : (B → D) → ℂ :=
  orderSum (fun b => x ((enumerate s b).val))

def supportSpace (x : A ⊕ B → D → ℂ) : Submodule ℂ ((B → D) → ℂ) :=
  Submodule.span ℂ (Set.range (partialPacket x))

theorem support_dimension (x : A ⊕ B → D → ℂ) :
    Module.finrank ℂ (supportSpace x) ≤
      (Fintype.card A + Fintype.card B).choose (Fintype.card B) := by
  have h := finrank_range_le_card (R := ℂ) (partialPacket x)
  simpa [Subsets, supportSpace, Finset.card_powersetCard] using h

private theorem orderSum_perm (y : B → D → ℂ) (p : Equiv.Perm B) :
    orderSum (y ∘ p) = orderSum y := by
  funext w
  exact (Group.mulLeft_bijective p).sum_comp (fun σ => pureWord (y ∘ σ) w)

private def rightEmbedding (σ : Equiv.Perm (A ⊕ B)) : B ↪ A ⊕ B :=
  ⟨fun b => σ (Sum.inr b), σ.injective.comp Sum.inr_injective⟩

private theorem surviving_member (x : A ⊕ B → D → ℂ) (σ : Equiv.Perm (A ⊕ B)) :
    orderSum (fun b => x (σ (Sum.inr b))) ∈ supportSpace x := by
  classical
  let e := rightEmbedding σ
  let s : Subsets A B := ⟨Finset.univ.map e, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩⟩
  let f : B ≃ ↥s.val := Equiv.ofBijective (fun b => ⟨e b, Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro b c h
      exact e.injective (congrArg Subtype.val h)
    · rintro ⟨i, hi⟩
      obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hi
      exact ⟨b, Subtype.ext hb⟩)
  let p := f.trans (enumerate s).symm
  have h : (fun b => x (σ (Sum.inr b))) = (fun b => x (enumerate s b).val) ∘ p := by
    funext b
    simp [p, f, e, rightEmbedding]
  rw [h, orderSum_perm]
  exact Submodule.subset_span ⟨s, rfl⟩

/-- Coefficient contributed by the fixed coordinates of a permutation term. -/
def frozenWeight (x : A ⊕ B → D → ℂ) (a : A → D) (σ : Equiv.Perm (A ⊕ B)) : ℂ :=
  ∏ i, x (σ (Sum.inl i)) (a i)

/-- Average over orders in the surviving slots before summing over all
permutations. The factorial clears this extra average. -/
theorem slice_expansion (x : A ⊕ B → D → ℂ) (a : A → D) (b : B → D) :
    ((Fintype.card B).factorial : ℂ) * packet x (Sum.elim a b) =
    packetScale (A ⊕ B) * ∑ σ : Equiv.Perm (A ⊕ B),
      frozenWeight x a σ * orderSum (fun j => x (σ (Sum.inr j))) b := by
  classical
  let term (σ : Equiv.Perm (A ⊕ B)) := pureWord (x ∘ σ) (Sum.elim a b)
  have oneOrder (τ : Equiv.Perm B) :
      ∑ σ : Equiv.Perm (A ⊕ B), frozenWeight x a σ *
          pureWord ((fun j => x (σ (Sum.inr j))) ∘ τ) b = ∑ σ, term σ := by
    let p := Equiv.sumCongr (Equiv.refl A) τ
    have h := (Group.mulRight_bijective p).sum_comp term
    convert h using 1
    apply Finset.sum_congr rfl
    intro σ _
    simp [term, pureWord, Fintype.prod_sum_type, frozenWeight, p]
  have grouped : (∑ σ : Equiv.Perm (A ⊕ B),
      frozenWeight x a σ * orderSum (fun j => x (σ (Sum.inr j))) b) =
      (Fintype.card B).factorial * ∑ σ, term σ := by
    simp only [orderSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [oneOrder]
    simp [Fintype.card_perm, Finset.mul_sum]
  rw [grouped]
  simp [packet, orderSum, term, mul_left_comm]

/-- Every slice of the normalized matrix packet belongs to the same
subset-indexed span, independently of the values of the frozen slots. -/
theorem slice_mem (x : A ⊕ B → D → ℂ) (a : A → D) :
    (fun b => packet x (Sum.elim a b)) ∈ supportSpace x := by
  classical
  let z : (B → D) → ℂ := ∑ σ : Equiv.Perm (A ⊕ B),
    frozenWeight x a σ • orderSum (fun j => x (σ (Sum.inr j)))
  have hz : z ∈ supportSpace x := Submodule.sum_mem _ fun σ _ =>
    Submodule.smul_mem _ _ (surviving_member x σ)
  have hne : ((Fintype.card B).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h : (fun b => packet x (Sum.elim a b)) =
      (packetScale (A ⊕ B) / (Fintype.card B).factorial) • z := by
    funext b
    simp only [z, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have he := slice_expansion x a b
    field_simp [hne]
    linear_combination he
  rw [h]
  exact Submodule.smul_mem _ _ hz


/-- Relabeling both factor and word slots preserves the normalized packet. -/
theorem packet_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (x : I → D → ℂ) (w : I → D) :
    packet (x ∘ e) (w ∘ e) = packet x w := by
  have h : orderSum (x ∘ e) (w ∘ e) = orderSum x w := by
    apply Fintype.sum_equiv e.permCongr
    intro σ
    apply Fintype.prod_equiv e
    intro j
    simp [Function.comp_def]
  simp only [packet, h, packetScale, Fintype.card_congr e]

private def splitSlots (k r : ℕ) (h : r ≤ k) : Fin r ⊕ Fin (k-r) ≃ Fin k :=
  ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr (Nat.sub_add_cancel h))

/-- The support in the contiguous word convention of Bend.wordFork:
the first k−r slots survive; the final r are contracted. -/
def splitSupport {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : ℕ) (h : r ≤ k) :
    Submodule ℂ (Bend.Word d (k-r) → ℂ) :=
  supportSpace (x ∘ splitSlots k r h)

theorem splitSupport_dimension {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : ℕ) (h : r ≤ k) :
    Module.finrank ℂ (splitSupport x r h) ≤ k.choose r := by
  have hs := support_dimension (x ∘ splitSlots k r h)
  simp only [Fintype.card_fin, Nat.add_sub_of_le h, Nat.choose_symm h] at hs
  exact hs

/-- Every surviving column after arbitrary contraction against the final r
strands lies in the same subspace. The fork uses exactly this appended word. -/
theorem split_contraction_mem {d k : ℕ} (x : Fin k → Fin d → ℂ) (r : ℕ) (h : r ≤ k)
    (c : Bend.Word d r → ℂ) :
    (fun y => ∑ t, c t * packet x (fun i => Fin.append y t (Fin.cast (Nat.sub_add_cancel h).symm i)))
      ∈ splitSupport x r h := by
  let v (t : Bend.Word d r) := fun y : Bend.Word d (k-r) =>
    packet x (fun i => Fin.append y t (Fin.cast (Nat.sub_add_cancel h).symm i))
  have hv (t : Bend.Word d r) : v t ∈ splitSupport x r h := by
    have hv' := slice_mem (x ∘ splitSlots k r h) t
    convert hv' using 1
    funext y
    unfold v
    rw [← packet_reindex (splitSlots k r h)]
    congr 1
    funext i
    cases i with
    | inl i => simp [Function.comp_def, splitSlots, finCongr, Fin.append_right]
    | inr i => simp [Function.comp_def, splitSlots, finCongr, Fin.append_left]
  have hsum : (∑ t, c t • v t) ∈ splitSupport x r h :=
    Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (hv t))
  convert hsum using 1
  funext y
  simp [v, Finset.sum_apply]

end
end BlockPermanents.PacketSupport
