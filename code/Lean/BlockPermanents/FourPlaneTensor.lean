import BlockPermanents.FourRotatedCompression

/-! Tensor generators for the compression on a rotated coordinate plane. -/
namespace BlockPermanents.FourCovariance
open FourCapOrbit FourRoutes FourSupportedTensor FourFullValues Closures Bend TensorCoordinates
open scoped BigOperators Matrix
noncomputable section

/-- Applying the same coordinate map in all slots preserves every in-packet symmetry. -/
theorem ordinaryChange_inner {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℂ)
    {F : Triple d 2 → ℂ} (hF : Inner F) : Inner ((ordinaryChange A).mulVec F) := by
  classical
  intro p x
  let s : Equiv.Perm (Triple d 2) :=
    Equiv.piCongrRight (fun i => (p i).symm.arrowCongr (Equiv.refl (Fin d)))
  change (∑ w : Triple d 2, (∏ i, ∏ j, A (x i (p i j)) (w i j)) * F w) =
    ∑ w : Triple d 2, (∏ i, ∏ j, A (x i j) (w i j)) * F w
  rw [← Equiv.sum_comp s (fun w => (∏ i, ∏ j, A (x i (p i j)) (w i j)) * F w)]
  apply Finset.sum_congr rfl
  intro w _
  change (∏ i, ∏ j, A (x i (p i j)) (w i (p i j))) * F (fun i => w i ∘ p i) = _
  rw [hF]
  apply congrArg (fun z => z * F w)
  exact Finset.prod_congr rfl (fun i _ => Equiv.prod_comp (p i) (fun j => A (x i j) (w i j)))

/-- Every symmetric ordinary triple has a symmetric preimage under a unitary rotation. -/
theorem ordinaryChange_preimage {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : Aᴴ * A = 1) {F : Triple d 2 → ℂ} (hF : Inner F) :
    ∃ G, Inner G ∧ (ordinaryChange A).mulVec G = F := by
  refine ⟨(ordinaryChange Aᴴ).mulVec F, ordinaryChange_inner Aᴴ hF, ?_⟩
  rw [Matrix.mulVec_mulVec]
  change (power (Fin 3) (power (Fin 2) A) * power (Fin 3) (power (Fin 2) Aᴴ)).mulVec F = F
  rw [← power_mul, ← power_mul, Matrix.mul_eq_one_comm.mp hA, power_one, power_one,
    Matrix.one_mulVec]

/-- Tensor powers take a pure word to the pure word on the transformed letters. -/
theorem power_pureWord {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (A : Matrix β α ℂ) (x : ι → α → ℂ) :
    (power ι A).mulVec (pureWord x) = pureWord (fun i => A.mulVec (x i)) := by
  classical
  funext v
  simp only [Matrix.mulVec, dotProduct, power, pureWord, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => A (v i) a * x i a)).symm

private theorem packet_expansion {ι D : Type*} [Fintype ι] [DecidableEq ι] (y : ι → D → ℂ) :
    packet y = packetScale ι • ∑ p : Equiv.Perm ι, pureWord (y ∘ p) := by
  funext w
  simp [packet, orderSum, Finset.sum_apply]

/-- The normalized permanent packet transforms by changing each of its letter vectors. -/
theorem power_packet {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (A : Matrix β α ℂ) (x : ι → α → ℂ) :
    (power ι A).mulVec (packet x) = packet (fun i => A.mulVec (x i)) := by
  classical
  rw [packet_expansion x, packet_expansion (fun i => A.mulVec (x i)),
    ← Matrix.mulVecLin_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact power_pureWord A (x ∘ p)

/-- A marked packet on two rotated coordinate vectors can be paired with any
inner-symmetric ordinary input, including a sum of ordinary packet triples. -/
theorem rotatedSupport_packet {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : Aᴴ * A = 1)
    (S : Finset (Fin d)) {F : Triple d 2 → ℂ} (hF : Inner F)
    (x : Fin 2 → Fin d → ℂ)
    (hx : ∀ i, ∃ c : Fin d → ℂ, (∀ j, j ∉ S → c j = 0) ∧ A.mulVec c = x i) :
    product F (fun w => star (packet x w)) ∈ rotatedSupport A S := by
  classical
  choose c hc hx' using hx
  obtain ⟨G, hG, hGF⟩ := ordinaryChange_preimage A hA hF
  rw [rotatedSupport_eq]
  apply Submodule.subset_span
  refine ⟨G, packet c, hG, Bridges.packet_symmetric _ _ _, packet_supported S c hc, ?_⟩
  rw [hGF, power_packet, show (fun i => A.mulVec (c i)) = x from funext hx']

end
end BlockPermanents.FourCovariance
