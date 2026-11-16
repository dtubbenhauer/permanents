import BlockPermanents.PortAverages
import BlockPermanents.SupportCoordinates

/-! # Two marked strands of the three-cable (Example 4B.3) -/
namespace BlockPermanents.TwoMarkedExample
open Closures RoutedTrace Bend
open scoped Matrix
noncomputable section

/-- The ordinary tensor with f in position t and e in the other two. -/
def placement {d : ℕ} (e f : Fin d → ℂ) (t : Fin 3) (w : Word d 3) : ℂ :=
  ∏ i, if i=t then f (w i) else e (w i)

/-- The symmetric product e ⊙ e ⊙ f obtained by the ordinary averaging clasp. -/
def z {d : ℕ} (e f : Fin d → ℂ) := clasp (placement e f 2)

open private eval_perm from BlockPermanents.PortAverages in
theorem three_placements {d : ℕ} (e f : Fin d → ℂ) (w : Word d 3) :
    z e f w = (placement e f 0 w + placement e f 1 w + placement e f 2 w)/3 := by
  have move (p : Equiv.Perm (Fin 3)) :
      placement e f 2 (w ∘ p.symm) = placement e f (p.symm 2) w := by
    unfold placement
    rw [← Equiv.prod_comp p (fun i => if i = 2 then f ((w ∘ p.symm) i) else e ((w ∘ p.symm) i))]
    simp only [Function.comp_apply,Equiv.symm_apply_apply,p.apply_eq_iff_eq_symm_apply]
  let F := fun i => placement e f i w
  have hi := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 3))) (fun p : Equiv.Perm (Fin 3) => F (p 2))
  have ha := eval_perm 2 2 F
  change (∑ p : Equiv.Perm (Fin 3), F (p 2)) / (Fintype.card (Equiv.Perm (Fin 3)) : ℂ) = _ at ha
  simp only [z,clasp,sumSlots,move,Fintype.card_fin]
  change (6:ℂ)⁻¹ * (∑ p : Equiv.Perm (Fin 3), F (p⁻¹ 2)) = _
  change (∑ p : Equiv.Perm (Fin 3), F (p⁻¹ 2)) = ∑ p : Equiv.Perm (Fin 3), F (p 2) at hi
  rw [hi]
  norm_num [Fintype.card_perm, Nat.factorial,mean,Fin.sum_univ_three,F] at ha
  rw [Fin.sum_univ_three] at ha
  linear_combination ha

/-- Apply the same support projection at slots zero and one. -/
def marked {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (v : Word d 3 → ℂ) (w : Word d 3) : ℂ :=
  ∑ i, ∑ j, P (w 0) i * P (w 1) j * v ![i,j,w 2]

private theorem projection_on_placement {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (e f : Fin d → ℂ) (t : Fin 3) (w : Word d 3) :
    marked P (placement e f t) w =
      (P.mulVec (if 0=t then f else e)) (w 0) *
      (P.mulVec (if 1=t then f else e)) (w 1) *
      (if 2=t then f (w 2) else e (w 2)) := by
  fin_cases t <;>
    simp [marked,placement,Fin.prod_univ_three,Matrix.mulVec,dotProduct,
      Finset.sum_mul, Finset.mul_sum] <;>
    rw [Finset.sum_comm] <;>
    apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- Exactly the placement with f on the unmarked slot survives projection. -/
theorem sole_survivor {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (e f : Fin d → ℂ)
    (he : P.mulVec e = e) (hf : P.mulVec f = 0) (w : Word d 3) :
    marked P (placement e f 0) w = 0 ∧ marked P (placement e f 1) w = 0 ∧
    marked P (placement e f 2) w = placement e f 2 w := by
  simp [projection_on_placement,he,hf, placement,Fin.prod_univ_three]

theorem projected_word {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (e f : Fin d → ℂ)
    (he : P.mulVec e = e) (hf : P.mulVec f = 0) (w : Word d 3) :
    marked P (z e f) w = placement e f 2 w / 3 := by
  have h := sole_survivor P e f he hf w
  calc
    _ = (marked P (placement e f 0) w + marked P (placement e f 1) w +
        marked P (placement e f 2) w)/3 := by
      simp only [marked,three_placements,mul_div_assoc',mul_add,
        ← Finset.sum_div,Finset.sum_add_distrib]
    _ = _ := by rw [h.1,h.2.1,h.2.2]; ring

/-- Restoring the outer three-clasp gives z/3. Only the action of the
support projector on these two input vectors is needed. -/
theorem clasped_projection {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (e f : Fin d → ℂ)
    (he : P.mulVec e = e) (hf : P.mulVec f = 0) (w : Word d 3) :
    clasp (marked P (z e f)) w = z e f w / 3 := by
  rw [show marked P (z e f) = fun v => placement e f 2 v/3 from funext (projected_word P e f he hf)]
  simp only [clasp,sumSlots,z,← Finset.sum_div]
  ring

/-- In an adapted basis the two matrix projections are exactly the
two marked paths of the routed intersection form. -/
theorem adapted_wire {d : ℕ} (S : Finset (Fin d)) (v : Word d 3 → ℂ) (w : Word d 3) :
    marked (Matrix.diagonal (fun j => if j ∈ S then (1:ℂ) else 0)) v w =
      wire S 1 ({0,1} : Finset (Fin 3)) v w := by
  have hpair : (∀ i ∈ ({0,1}:Finset (Fin 3)), w i ∈ S) ↔ w 0 ∈ S ∧ w 1 ∈ S := by simp
  have hw : ![w 0,w 1,w 2] = w := by funext i; fin_cases i <;> rfl
  simp only [marked,Matrix.diagonal_apply,wire,hpair]
  by_cases h0 : w 0 ∈ S <;> by_cases h1 : w 1 ∈ S <;>
    simp [h0,h1,ite_mul,mul_ite,hw]

abbrev Space (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The matrix of the actual orthogonal support projector in the ambient basis. -/
def projector {d : ℕ} (S : Submodule ℂ (Space d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.toEuclideanLin.symm (S.subtype.comp S.orthogonalProjection.toLinearMap)

private theorem projector_apply {d : ℕ} (S : Submodule ℂ (Space d)) (x : Space d) :
    (projector S).mulVec (fun i => x i) = fun i => (S.orthogonalProjection x : Space d) i := by
  change WithLp.equiv 2 _ (Matrix.toEuclideanLin (projector S) x) = _
  rw [projector,LinearEquiv.apply_symm_apply]
  rfl

/-- The statement with any geometric subspace S and the two vectors on
its orthogonal sides, without choosing an adapted basis. -/
theorem subspace_example {d : ℕ} (S : Submodule ℂ (Space d)) (e f : Space d)
    (he : e ∈ S) (hf : f ∈ Sᗮ) (w : Word d 3) :
    clasp (marked (projector S) (z (fun i => e i) (fun i => f i))) w =
      z (fun i => e i) (fun i => f i) w / 3 := by
  apply clasped_projection
  · rw [projector_apply]
    have h := S.orthogonalProjection_mem_subspace_eq_self (⟨e,he⟩ : S)
    exact congrArg (fun v : S => (fun i => (v.val : Space d) i)) h
  · rw [projector_apply, (S.orthogonalProjection_eq_zero_iff).mpr hf]
    rfl

end
end BlockPermanents.TwoMarkedExample
