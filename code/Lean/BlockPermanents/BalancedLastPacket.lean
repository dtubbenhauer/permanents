import BlockPermanents.BalancedLastIntrinsic
import BlockPermanents.BalancedLastEnvelope
import BlockPermanents.BalancedLastAverage

/-! Evaluating the two-plane compression on four arbitrary matrix packets
and combining their three marked inequalities on the upright boundary. -/
namespace BlockPermanents.BalancedLast
open Bend Closures BalancedDivision BalancedAssembly BalancedPacket
noncomputable section

private theorem symmetric_scale {d k : ℕ} {F : Word d k → ℂ}
    (hF : Symmetric F) (c : ℂ) : Symmetric (c • F) := by
  unfold Bend.Symmetric at *
  rw [Matrix.mulVec_smul, hF]

private theorem product_onPlanes {d k : ℕ}
    (S T : Submodule ℂ (FourPlaneBasis.Ambient d))
    (F G H J : Word d k → ℂ) (hF : Symmetric F) (hG : Symmetric G)
    (hH : H ∈ ThreePlane.symmetricPower k S) (hJ : J ∈ ThreePlane.symmetricPower k T) :
    OnPlanes S T (product (product F G) (fun p => star (product H J p))) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro b c e
    convert symmetric_scale hF (G b * star (H c * J e)) using 1
    funext a; simp only [product, Pi.smul_apply, smul_eq_mul]; ring
  · intro a c e
    convert symmetric_scale hG (F a * star (H c * J e)) using 1
    funext b; simp only [product, Pi.smul_apply, smul_eq_mul]; ring
  · intro a b e
    convert (ThreePlane.symmetricPower k S).smul_mem (star (F a * G b) * J e) hH using 1
    funext c; simp only [product, Pi.smul_apply, smul_eq_mul,star_mul',star_star]; ring
  · intro a b c
    convert (ThreePlane.symmetricPower k T).smul_mem (star (F a * G b) * H c) hJ using 1
    funext e; simp only [product, Pi.smul_apply, smul_eq_mul,star_mul',star_star]; ring

/-- A plane containing the atoms is chosen independently at each of the
two turned feet. This includes zero and nonunit packets. -/
theorem packet_expectation {d k : ℕ} (hk : 4 ≤ k) (hkd : k ≤ d)
    (u v s t : Fin k → Fin d → ℂ) :
    0 ≤ (quadratic (marked d k) (packetProduct (packet u) (packet v) (packet s) (packet t))).re := by
  obtain ⟨S, hS, _, hs⟩ := packet_plane hkd s
  obtain ⟨T, hT, _, ht⟩ := packet_plane hkd t
  change 0 ≤ (quadratic (marked d k)
    (product (product (packet u) (packet v)) (product (packet s) (packet t)))).re
  rw [evaluate_bend]
  exact subspace_marked_nonnegative hk S T hS hT _
    (product_onPlanes _ _ _ _ _ _ (Bridges.packet_symmetric _ _ u) (Bridges.packet_symmetric _ _ v) hs ht)

private def cyclic {D : Type*} : Boundary D ≃ Boundary D where
  toFun := rotate
  invFun x := rotate (rotate x)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem product_rotate {D : Type*} (F G H J : D → ℂ) (y : Boundary D) :
    packetProduct F H J G (rotate y) = packetProduct F G H J y := by
  unfold packetProduct rotate; ring

private theorem pair_rotate {d k : ℕ} (F G H J : Word d k → ℂ)
    (W : B d k → ℂ) :
    bracket (packetProduct F H J G) W =
      bracket (packetProduct F G H J) (W ∘ rotate) := by
  unfold bracket
  rw [← cyclic.sum_comp (fun y => (starRingEnd ℂ) (packetProduct F H J G y) * W y)]
  exact Finset.sum_congr rfl (fun y _ => by change (starRingEnd ℂ) (packetProduct F H J G (rotate y)) * _ = _; rw [product_rotate]; rfl)

/-- Polarization against the upright product gives the three marked
expectations whose average is the genuine four-packet defect. -/
theorem three_expectations {d k : ℕ} (F G H J : Word d k → ℂ)
    (hF : Symmetric F) (hG : Symmetric G) (hH : Symmetric H) (hJ : Symmetric J) :
    quadratic (marked d k) (packetProduct F G H J) +
      quadratic (marked d k) (packetProduct F H J G) +
      quadratic (marked d k) (packetProduct F J G H) =
      3 * quadratic (defect d k) (packetProduct F G H J) := by
  simp only [Bridges.quadratic_bracket]
  rw [pair_rotate F H J G, pair_rotate F G H J ((marked d k).mulVec (packetProduct F H J G)),
    pair_rotate F G H J (((marked d k).mulVec (packetProduct F J G H)) ∘ rotate)]
  simp only [bracket, Function.comp_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_add, ← mul_add, three_division_average F G H J hF hG hH hJ y]
  ring

/-- The main nonnegative upright defect follows directly from the actual
three marked bends, allowing a different pair of supporting planes each time. -/
theorem defect_nonnegative {d k : ℕ} (hk : 4 ≤ k) (hkd : k ≤ d)
    (x : Fin 4 → Fin k → Fin d → ℂ) :
    0 ≤ (quadratic (defect d k)
      (packetProduct (packet (x 0)) (packet (x 1)) (packet (x 2)) (packet (x 3)))).re := by
  have h := congrArg Complex.re (three_expectations _ _ _ _ (Bridges.packet_symmetric d k (x 0))
    (Bridges.packet_symmetric d k (x 1)) (Bridges.packet_symmetric d k (x 2)) (Bridges.packet_symmetric d k (x 3)))
  norm_num [Complex.add_re, Complex.mul_re] at h
  linarith only [h, packet_expectation hk hkd (x 0) (x 1) (x 2) (x 3),
    packet_expectation hk hkd (x 0) (x 2) (x 3) (x 1), packet_expectation hk hkd (x 0) (x 3) (x 1) (x 2)]

end
end BlockPermanents.BalancedLast
