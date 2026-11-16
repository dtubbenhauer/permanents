import BlockPermanents.FourCompression
import BlockPermanents.Coarse

/-! # Positive semidefinite matrix of the supported compression -/
namespace BlockPermanents.FourCompression
open FourTarget FourAdjoints FourUpright TransferBlocks FourSupportedTensor
open Closures Bend SchurNormalization Matrix
open scoped BigOperators Matrix ComplexOrder
noncomputable section
set_option maxHeartbeats 950000

private theorem reflected_id {I : Type*} [Fintype I] : Reflected (1 : End I) 1 := fun _ _ => rfl

private theorem sandwich {I : Type*} [Fintype I] {A B : End I}
    (ha : Reflected A A) (hb : Reflected B B) : Reflected (A*B*A) (A*B*A) := by
  simpa only [mul_assoc] using (ha.mul hb).mul ha

private theorem jordan {I : Type*} [Fintype I] {A B : End I}
    (ha : Reflected A A) (hb : Reflected B B) : Reflected (A*B+B*A) (A*B+B*A) := by
  have h := (ha.mul hb).add (hb.mul ha)
  rwa [add_comm (B*A) (A*B)] at h

private theorem reflected_four {I : Type*} [Fintype I] (a : ℚ) (u v w t P X Y : End I)
    (hu : Reflected u u) (hv : Reflected v v) (hw : Reflected w w) (ht : Reflected t t)
    (hP : Reflected P P) (hx : Reflected X X) (hy : Reflected Y Y)
    (hF : Reflected (triple u v) (triple u v)) :
    Reflected (fourOperator a u v w t P X Y) (fourOperator a u v w t P X Y) := by
  let B := corrected a u v P X
  let C := (2:ℚ) • B-X
  have hA : Reflected (pair u) (pair u) := (reflected_id.add hu).scale (1/2)
  have hV : Reflected (pair v) (pair v) := (reflected_id.add hv).scale (1/2)
  have hmove : Reflected (movedDifference u v P) (movedDifference u v P) := by
    have half := sandwich hA (sandwich (sandwich hu hv) hP)
    have tail := ((hP.mul hV).mul hA).add ((hA.mul hV).mul hP)
    have e := (half.scale 2).sub tail
    unfold movedDifference
    convert e using 1 <;> simp only [mul_assoc] <;> abel
  have hB : Reflected B B := hx.add (hmove.scale a)
  have hC : Reflected C C := (hB.scale 2).sub hx
  exact (((hy.sub hx).add ((sandwich hF (sandwich hw hB)).scale 3)).sub (sandwich hF (jordan hC ht)))

/-- Self-adjointness of the marked transfer before bending, for arbitrary packet order. -/
theorem marked_self (d k : ℕ) : Reflected (Q d k) (Q d k) := by
  have hL : Reflected (fineClasp d k) (fineClasp d k) :=
    average_self (D:=Fin d) (MonoidHom.id (Wire k))
  have hW : Reflected (packetClaspOp d k) (packetClaspOp d k) := average_self (D:=Fin d) (wires k)
  unfold Q
  apply reflected_four
  · exact swap_self d k 0 1
  · exact swap_self d k 1 2
  · exact swap_self d k 2 3
  · exact swap_self d k 0 3
  · exact local_self d k 2
  · exact ((local_self d k 3).scale (((3*k).factorial : ℚ)/k.factorial^3)).sub ((ordinary_self d k).scale 6)
  · exact (hL.scale (((4*k).factorial : ℚ)/k.factorial^4)).sub (hW.scale 24)
  · exact ordinary_self d k

attribute [local irreducible] Q markedMatrix layout

private theorem pair_pull {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (v : B → ℂ) (y : A → ℂ) : bracket v (pull e.symm y) = bracket (pull e v) y := by
  calc
    _ = ∑ a, star (v (e a)) * y (e.symm (e a)) :=
      (e.sum_comp (fun b => star (v b) * y (e.symm b))).symm
    _ = _ := by simp [bracket,pull]

theorem marked_hermitian (d : ℕ) : (markedMatrix d).IsHermitian := by
  classical
  let e := layout d
  have h (x y : Boundary d) : bracket x ((markedMatrix d).mulVec y) =
      bracket ((markedMatrix d).mulVec x) y := by
    rw [marked_action,marked_action,pair_pull,marked_self d 2]
    exact (e.symm.sum_comp (fun a => star (Q d 2 (pull e x) a) * y (e a))).symm.trans
      (by simp [bracket,pull,e])
  ext i j
  have one (a : Index d) (v : Boundary d) : bracket (Pi.single a 1) v = v a := by
    simp [bracket,Pi.single_apply,ite_mul]
  have two (a : Index d) (v : Boundary d) : bracket v (Pi.single a 1) = star (v a) := by
    simp [bracket,Pi.single_apply,mul_ite]
  have read := h (Pi.single i 1) (Pi.single j 1)
  rw [one,two] at read
  simpa only [mulVec_single_one,conjTranspose_apply] using read.symm

theorem bent_hermitian (d : ℕ) : (partialTranspose (markedMatrix d)).IsHermitian := by
  ext ⟨a,b⟩ ⟨c,e⟩
  change star (markedMatrix d (c,b) (a,e)) = markedMatrix d (a,e) (c,b)
  exact congrFun (congrFun (marked_hermitian d) (a,e)) (c,b)

/-- In ambient dimension zero or one the fine and packet actions are trivial. -/
private theorem small_marked (d : ℕ) [Subsingleton (Fin d)] : Q d 2 = (2496:ℚ) • 1 := by
  have act_one (g : Wire 2) : act d 2 g = 1 := by
    apply LinearMap.ext; intro z; funext w
    change z (w ∘ g) = z w
    exact congrArg z (Subsingleton.elim _ _)
  have pkt (g : FourPerm) : packets d 2 g = 1 := act_one _
  have base {G : Type} [Group G] [Fintype G] (A : Op d 2) :
      (Fintype.card G : ℚ)⁻¹ • (∑ _ : G, A) = A := by
    rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℚ,
      inv_smul_smul₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  have avg {G : Type} [Group G] [Fintype G] (ρ : G →* Op d 2) (h : ∀ g, ρ g=1) :
      Transfer.clasp ρ = 1 := by
    unfold Transfer.clasp
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    exact base (G:=G) 1
  have hf : fineClasp d 2 = 1 := avg _ act_one
  have hp : packetClaspOp d 2 = 1 := avg _ pkt
  have ha := four_average_actual d 2
  have fixed (A : Op d 2) : Transfer.bracket (packets d 2) A = A := by
    change (Fintype.card FourPerm : ℚ)⁻¹ • (∑ g : FourPerm, packets d 2 g * A * packets d 2 g⁻¹) = A
    simp only [pkt,one_mul,mul_one]; exact base (G:=FourPerm) _
  rw [fixed,X₄,hf,hp] at ha
  convert ha using 1
  norm_num [Nat.factorial]
  module

/-- A supported subspace of smaller dimension may be extended to a plane.
The argument also covers ambient dimensions zero and one. -/
theorem nonnegative_of_card_le {d : ℕ} (S : Finset (Fin d)) (hc : S.card ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2)
    {z : Boundary d} (hz : z ∈ Submodule.span ℂ (simple S)) :
    0 ≤ (quadratic (partialTranspose (markedMatrix d)) z).re := by
  by_cases hd : 2 ≤ d
  · obtain ⟨T,hST,hT⟩ := Finset.exists_superset_card_eq hc (by simpa using hd)
    apply nonnegative T hT h₂ h₄ h₆
    apply Submodule.span_mono (s:=simple S) (t:=simple T) _ hz
    rintro _ ⟨x,y,hx,hy,hs,rfl⟩
    exact ⟨x,y,hx,hy,fun b hb => hs b (fun h => hb (hST h)),rfl⟩
  · letI : Subsingleton (Fin d) := ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
    have pt : partialTranspose (markedMatrix d) = markedMatrix d := by
      ext ⟨a,b⟩ ⟨c,e⟩; change markedMatrix d (a,e) (c,b) = markedMatrix d (a,b) (c,e); rw [Subsingleton.elim b e]
    rw [pt,marked_quadratic,small_marked]
    let v := pull (layout d) z
    change 0 ≤ (rightPair v ((2496:ℚ) • v)).re
    rw [map_smul]
    change 0 ≤ ((2496:ℚ) • bracket v v).re
    rw [Coarse.bracket_self]
    simp [Rat.smul_def,Bend.energy]
    exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- Every choice of generators in the supported subspace gives a positive
semidefinite complex compression matrix. An orthonormal basis gives the usual compression. -/
theorem compression_psd {d : ℕ} (S : Finset (Fin d)) (hc : S.card ≤ 2)
    (h₂ : HomogeneousSchur d 2 2) (h₄ : HomogeneousSchur d 4 2) (h₆ : HomogeneousSchur d 6 2)
    {T : Type*} [Fintype T] (B : Matrix (Index d) T ℂ)
    (hs : ∀ x, B.mulVec x ∈ Submodule.span ℂ (simple S)) :
    (Bᴴ * partialTranspose (markedMatrix d) * B).PosSemidef := by
  let M := partialTranspose (markedMatrix d)
  have hM : M.IsHermitian := bent_hermitian d
  refine ⟨isHermitian_conjTranspose_mul_mul B hM,fun x => ?_⟩
  have q := nonnegative_of_card_le S hc h₂ h₄ h₆ (hs x)
  rw [Bridges.quadratic_bracket] at q
  let y := B.mulVec x
  have real : star (bracket y (M.mulVec y)) = bracket y (M.mulVec y) := by
    change star (dotProduct (star y) (M.mulVec y)) = dotProduct (star y) (M.mulVec y)
    calc
      _ = dotProduct (star (M.mulVec y)) y := (star_dotProduct (M.mulVec y) y).symm
      _ = _ := by rw [star_mulVec,← dotProduct_mulVec,hM.eq]
  have im := congrArg Complex.im real
  simp only [Complex.star_def,Complex.conj_im] at im
  have pos : 0 ≤ dotProduct (star y) (M.mulVec y) := by
    apply Complex.nonneg_iff.mpr
    exact ⟨q,by change 0 = (bracket y (M.mulVec y)).im; linarith⟩
  simpa only [y,M,star_mulVec,dotProduct_mulVec,vecMul_vecMul] using pos

end
end BlockPermanents.FourCompression
