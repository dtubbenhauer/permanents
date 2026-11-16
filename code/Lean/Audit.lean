import BlockPermanents
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Inspect the transitive kernel dependencies of every public project theorem.
A failing dependency makes the verification command fail. -/
open Lean Elab Command in
elab "#audit_block_permanents" : command => do
  let env ← getEnv
  let mut roots := #[]
  for (name, ci) in env.constants.toList do
    if (`BlockPermanents).isPrefixOf name then
      if ci.isTheorem then roots := roots.push name
  if roots.isEmpty then throwError "No BlockPermanents theorems were found."
  let traversal := roots.forM CollectAxioms.collect
  let (_, state) := ((traversal.run env).run {})
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom reachable from a project theorem: {ax}"
  logInfo m!"Audited {roots.size} theorem declarations in BlockPermanents. Kernel axioms: {state.axioms}."

-- These examples also guard the mathematical interfaces. In particular,
-- adding a hypothesis on the desired positivity result would fail here.
example {k : ℕ} (hk : 0 < k)
    (h : BlockPermanents.SchurNormalization.HomogeneousSchur (k+k) k k) :
    BlockPermanents.MarcusAt 2 k := BlockPermanents.marcus_two hk h

example {k : ℕ} (hk : 3 ≤ k)
    (h₁ : BlockPermanents.SchurNormalization.HomogeneousSchur (3*k) k k)
    (h₂ : BlockPermanents.SchurNormalization.HomogeneousSchur (3*k) (2*k) k) :
    BlockPermanents.MarcusAt 3 k := BlockPermanents.marcus_three hk h₁ h₂

example : BlockPermanents.MarcusAt 3 2 := BlockPermanents.marcus_three_quadratic

example {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ p q, BlockPermanents.SchurNormalization.HomogeneousSchur (5*k) p q) :
    BlockPermanents.MarcusAt 5 k := BlockPermanents.FiveMain.marcus_five hk h

example {m k : ℕ} (hc : m*(m-1)*(2*m-1) ≤ 6*(m/2)*(2^k-1))
    (h : ∀ p q, BlockPermanents.SchurNormalization.HomogeneousSchur (m*k) p q) :
    BlockPermanents.MarcusAt m k := BlockPermanents.MatchingThreshold.marcus_threshold hc h

example (h : ∀ d p q, BlockPermanents.SchurNormalization.HomogeneousSchur d p q) :
    BlockPermanents.ManuscriptTheorem := BlockPermanents.manuscript_theorem h

#audit_block_permanents

#print axioms BlockPermanents.marcus_three
#print axioms BlockPermanents.marcus_two
#print axioms BlockPermanents.two_quadratic
#print axioms BlockPermanents.Transfer.packet_transfer
#print axioms BlockPermanents.TransferBlocks.four_average
#print axioms BlockPermanents.PairSquares.full_caps_squares
#print axioms BlockPermanents.Threshold.pathCoeff_le_fine
#print axioms BlockPermanents.Negative.negative_marked_closure

#print axioms BlockPermanents.marcus_three_quadratic
#print axioms BlockPermanents.FiveMain.marcus_five
#print axioms BlockPermanents.MatchingThreshold.marcus_threshold
#print axioms BlockPermanents.matrix_range

#print axioms BlockPermanents.manuscript_theorem
#print axioms BlockPermanents.FourMatrix.marcus_four_quadratic
#print axioms BlockPermanents.RefinedThreshold.marcus
#print axioms BlockPermanents.TenEndpoint.marcus_ten

#print axioms BlockPermanents.FourNative.full_cap_row
#print axioms BlockPermanents.FourNative.quadratic_weights

#print axioms BlockPermanents.FourNative.transfer_first_proper
#print axioms BlockPermanents.FourNative.first_proper_term
#print axioms BlockPermanents.FourNative.drawn_half_eq

#print axioms BlockPermanents.FourNative.transfer_second_proper
#print axioms BlockPermanents.FourNative.second_proper_term
#print axioms BlockPermanents.FourNative.quadratic_second_family

#print axioms BlockPermanents.FourNative.four_packet_bend
#print axioms BlockPermanents.FourNative.four_packet_bend_quadratic
#print axioms BlockPermanents.FourNative.third_proper_term

#print axioms BlockPermanents.FourNative.terminalV_fixed

#print axioms BlockPermanents.FourCovariance.representation_natural
#print axioms BlockPermanents.FourCovariance.transfer_natural

#print axioms BlockPermanents.FourCovariance.bentChange_apply
#print axioms BlockPermanents.FourCovariance.bent_covariance

#print axioms BlockPermanents.FourCovariance.rotatedSupport_eq
#print axioms BlockPermanents.FourCovariance.rotated_nonnegative
#print axioms BlockPermanents.FourCovariance.rotated_compression_psd

#print axioms BlockPermanents.FourPlaneBasis.exists_plane_coordinates
#print axioms BlockPermanents.FourCovariance.power_packet
#print axioms BlockPermanents.FourCovariance.supported_mem_packet_span
#print axioms BlockPermanents.FourPlaneCompression.planeSupport_eq_rotatedSupport
#print axioms BlockPermanents.FourPlaneCompression.nonnegative
#print axioms BlockPermanents.FourPlaneCompression.compression_psd
#print axioms BlockPermanents.FourPlaneCompression.marcus_four_quadratic

#print axioms BlockPermanents.SchurWireCriterion.homogeneous_of_unbent
#print axioms BlockPermanents.SchurWireCriterion.unbent_of_operator
#print axioms BlockPermanents.SchurWireCriterion.of_operator
#print axioms BlockPermanents.SchurWireCriterion.operator_iff

#print axioms BlockPermanents.SchurSubsetCount.card_subsets

#print axioms BlockPermanents.SchurClass.factorization_iff
#print axioms BlockPermanents.SchurFibreCount.card_leftImage_fibre
#print axioms BlockPermanents.SchurFibreCount.card_cross_fibre

#print axioms BlockPermanents.SchurAverage.finite_average
#print axioms BlockPermanents.SchurAverage.representation_identity
#print axioms BlockPermanents.SchurAverage.wire_identity

-- Guard the precise interfaces: these proofs take no Schur or positivity input.
example (d p q : ℕ) : BlockPermanents.SchurNormalization.HomogeneousSchur d p q :=
  BlockPermanents.SchurNormalization.homogeneousSchur d p q

example : BlockPermanents.ManuscriptTheorem := BlockPermanents.VerifiedPaper.manuscript
example : BlockPermanents.MarcusAt 4 2 := BlockPermanents.VerifiedPaper.four_quadratic

#print axioms BlockPermanents.SchurNormalization.homogeneousSchur
#print axioms BlockPermanents.VerifiedPaper.manuscript
#print axioms BlockPermanents.VerifiedPaper.logarithmic
#print axioms BlockPermanents.VerifiedPaper.plane_compression
#print axioms BlockPermanents.VerifiedPaper.four_quadratic

#print axioms BlockPermanents.PairResidual.slice_mem
#print axioms BlockPermanents.PairResidual.rank_pos
#print axioms BlockPermanents.PairResidual.rank_le

#print axioms BlockPermanents.PairResidual.close_cut
#print axioms BlockPermanents.PairResidual.cut_bubble
#print axioms BlockPermanents.PairResidual.cut_resolution
#print axioms BlockPermanents.PairResidual.surplus_nonneg
#print axioms BlockPermanents.PairResidual.J_fixes_iff
#print axioms BlockPermanents.PairResidual.residual_closes_to_zero

#print axioms BlockPermanents.PairResidual.summand_nonneg
#print axioms BlockPermanents.PairResidual.full_caps_residual_squares
#print axioms BlockPermanents.PairResidual.summand_eq_zero_iff
#print axioms BlockPermanents.PairResidual.full_caps_eq_iff

#print axioms BlockPermanents.PairResidual.residualMatrix_apply
#print axioms BlockPermanents.PairResidual.residualMatrix_energy
#print axioms BlockPermanents.PairResidualExample.middle_matrix
#print axioms BlockPermanents.PairResidualExample.middle_trace
#print axioms BlockPermanents.PairResidualExample.middle_energy
#print axioms BlockPermanents.PairResidualExample.cut_values
#print axioms BlockPermanents.PairResidualExample.equality_four

#print axioms BlockPermanents.PairResidual.full_caps_residual_operator
#print axioms BlockPermanents.PairOrthonormalExample.middle_matrix
#print axioms BlockPermanents.PairOrthonormalExample.middle_trace
#print axioms BlockPermanents.PairOrthonormalExample.middle_energy
#print axioms BlockPermanents.PairOrthonormalExample.cut_values
#print axioms BlockPermanents.PairOrthonormalExample.equality_four

#print axioms BlockPermanents.ThreePlane.cap_frame_change
#print axioms BlockPermanents.ThreePlane.cap_bubble
#print axioms BlockPermanents.ThreePlane.cap_eq_trace
#print axioms BlockPermanents.ThreePlane.resolve

#print axioms BlockPermanents.ThreePlane.clasp_power
#print axioms BlockPermanents.ThreePlane.power_symmetric
#print axioms BlockPermanents.ThreePlane.power_slice
#print axioms BlockPermanents.ThreePlane.basis_isometry
#print axioms BlockPermanents.ThreePlane.basis_range
#print axioms BlockPermanents.ThreePlane.symmetricPower_range

#print axioms BlockPermanents.ThreePlane.routed_resolution
#print axioms BlockPermanents.ThreePlane.frame_projector_eq
#print axioms BlockPermanents.ThreePlane.perpendicular_eq_of_range

#print axioms BlockPermanents.ThreePlane.corrected_pullback
#print axioms BlockPermanents.ThreePlane.original_pullback
#print axioms BlockPermanents.ThreePlane.bare_compression
#print axioms BlockPermanents.ThreePlane.tensor_range
#print axioms BlockPermanents.ThreePlane.bent_tensor_range
#print axioms BlockPermanents.ThreePlane.symmetricBoundary_range
#print axioms BlockPermanents.ThreePlane.perpendicular_closes_to_zero
#print axioms BlockPermanents.ThreePlane.perpendicular_fixes_iff
#print axioms BlockPermanents.ThreePlane.Example.cup_e11
#print axioms BlockPermanents.ThreePlane.Example.perpendicular_e11
#print axioms BlockPermanents.ThreePlane.Example.e11_energies

-- The matrix consequence uses only the positive thickness and project theorems.
example {k : ℕ} (hk : 1 ≤ k) : BlockPermanents.MarcusAt 3 k :=
  BlockPermanents.ThreePlane.marcus_three hk

#print axioms BlockPermanents.ThreePlane.subspace_decomposition
#print axioms BlockPermanents.ThreePlane.subspace_compression_psd
#print axioms BlockPermanents.ThreePlane.family_lifts_iff
#print axioms BlockPermanents.ThreePlane.family_pullback
#print axioms BlockPermanents.ThreePlane.intrinsic_compression_psd
#print axioms BlockPermanents.ThreePlane.full_cap_weight_lower
#print axioms BlockPermanents.ThreePlane.proper_weights_pos
#print axioms BlockPermanents.ThreePlane.full_cap_weight_pos
#print axioms BlockPermanents.ThreePlane.packet_expectation
#print axioms BlockPermanents.ThreePlane.marcus_three

#print axioms BlockPermanents.BalancedLast.expand_independent
#print axioms BlockPermanents.BalancedLast.dimension
#print axioms BlockPermanents.BalancedLast.bubble

#print axioms BlockPermanents.BalancedLastTrace.survivor_mem
#print axioms BlockPermanents.BalancedLastTrace.close
#print axioms BlockPermanents.BalancedLastTrace.rank_resolution
#print axioms BlockPermanents.BalancedLastTrace.resolution
#print axioms BlockPermanents.BalancedLastTrace.residual_closes

#print axioms BlockPermanents.BalancedLastJoint.joint_entry
#print axioms BlockPermanents.BalancedLastJoint.terminal_energy
#print axioms BlockPermanents.BalancedLastJoint.joint_split
#print axioms BlockPermanents.BalancedLastJoint.first_split
#print axioms BlockPermanents.BalancedLastJoint.second_split
#print axioms BlockPermanents.BalancedLastJoint.firstSquares_nonneg
#print axioms BlockPermanents.BalancedLastJoint.secondSquares_nonneg

#print axioms BlockPermanents.BalancedLastRectangle.rectangle_exact
#print axioms BlockPermanents.BalancedLastRectangle.remainder_nonneg

-- Both original-matrix statements discharge every mathematical input internally.
example : BlockPermanents.MarcusAt 4 3 := BlockPermanents.BalancedCubicMarcus.marcus
example {k : ℕ} (hk : 4 ≤ k) : BlockPermanents.MarcusAt 4 k :=
  BlockPermanents.BalancedLast.marcus_thick hk

#print axioms BlockPermanents.BalancedLast.space_symmetricPower
#print axioms BlockPermanents.BalancedLast.dual_space_iff
#print axioms BlockPermanents.BalancedLast.supported_iff
#print axioms BlockPermanents.BalancedLast.exists_packet_frame
#print axioms BlockPermanents.BalancedLast.borderRemainder_nonneg
#print axioms BlockPermanents.BalancedLast.pairing_decomposition
#print axioms BlockPermanents.BalancedLast.subspace_last_cap_weight
#print axioms BlockPermanents.BalancedLastDifferences.completed_routes
#print axioms BlockPermanents.BalancedLast.subspace_marked_decomposition
#print axioms BlockPermanents.BalancedLast.subspace_compression_psd
#print axioms BlockPermanents.BalancedLastExample.cubic_shortfall
#print axioms BlockPermanents.BalancedCubicFine.fine_remainder
#print axioms BlockPermanents.BalancedCubicTau.tau_squares
#print axioms BlockPermanents.BalancedCubicTau.tau_swap
#print axioms BlockPermanents.BalancedCubicTau.tau_packet_spans
#print axioms BlockPermanents.BalancedCubicTau.correction_nonneg
#print axioms BlockPermanents.BalancedCubicExterior.crossing_exterior
#print axioms BlockPermanents.BalancedCubicExterior.signedSquares_exterior
#print axioms BlockPermanents.BalancedCubic.reverse_edge
#print axioms BlockPermanents.BalancedCubic.cubic_certificate
#print axioms BlockPermanents.BalancedCubic.cubic_certificate_all_dimensions
#print axioms BlockPermanents.BalancedCubicMarcus.marcus
#print axioms BlockPermanents.BalancedDivision.three_division_average
#print axioms BlockPermanents.BalancedDivision.defect_gram
#print axioms BlockPermanents.BalancedLast.defect_nonnegative
#print axioms BlockPermanents.BalancedLast.marcus_thick
#print axioms BlockPermanents.BalancedLast.marcus_four

#print axioms BlockPermanents.TwoStepSquares.local_matrix
#print axioms BlockPermanents.TwoStepSquares.unit_wedge
#print axioms BlockPermanents.TwoStepSquares.local_squares
#print axioms BlockPermanents.TwoStepSquares.local_squares_symmetric
#print axioms BlockPermanents.TwoStepSquares.remainder_nonneg

#print axioms BlockPermanents.TwoStepSquares.two_step_path_squares
#print axioms BlockPermanents.TwoStepSquares.unordered_path_squares
#print axioms BlockPermanents.TwoStepSquares.global_squares_nonnegative
#print axioms BlockPermanents.TwoStepSquares.path_energy_reverse

#print axioms BlockPermanents.TwoStepSpectator.count_extensions
#print axioms BlockPermanents.TwoStepSpectator.path_squares
#print axioms BlockPermanents.TwoStepSpectator.remainder_nonneg

#print axioms BlockPermanents.ReflectedCycles.odd_cut_squares
#print axioms BlockPermanents.ReflectedCycles.even_cut_squares
#print axioms BlockPermanents.ReflectedCycles.odd_circuit_squares
#print axioms BlockPermanents.ReflectedCycles.even_circuit_squares
#print axioms BlockPermanents.ReflectedCycles.odd_consecutive_squares
#print axioms BlockPermanents.ReflectedCycles.even_consecutive_squares
#print axioms BlockPermanents.ReflectedCycles.oddRemainder_nonneg
#print axioms BlockPermanents.RawCycleSquares.class_average
#print axioms BlockPermanents.RawCycleSquares.single_count
#print axioms BlockPermanents.RawCycleSquares.matching_class_sum
#print axioms BlockPermanents.RawCycleSquares.matching_class_outside
#print axioms BlockPermanents.RawCycleSquares.odd_cycle_real
#print axioms BlockPermanents.RawCycleSquares.oddClassRemainder_nonneg
#print axioms BlockPermanents.RawCycleSquares.odd_cycle_squares

example {k : ℕ} (hk : 3 ≤ k) : BlockPermanents.MarcusAt 5 k := BlockPermanents.FiveFullCertificate.marcus_five hk
#print axioms BlockPermanents.FiveResidualGram.remainder_gram
#print axioms BlockPermanents.FiveResidualGram.rows_gram
#print axioms BlockPermanents.FiveMixedSquares.test_gram
#print axioms BlockPermanents.FiveMixedSquares.mixed_gram
#print axioms BlockPermanents.FiveMixedSquares.physical_trace
#print axioms BlockPermanents.FiveMixedSquares.physical_trace_lower
#print axioms BlockPermanents.FiveMixedAverageSquares.plain_squares
#print axioms BlockPermanents.FiveMixedAverageSquares.weighted_squares
#print axioms BlockPermanents.FiveMixedAverageSquares.exits_nonneg
#print axioms BlockPermanents.FiveFreeCoefficient.closed_form
#print axioms BlockPermanents.FiveFreeCoefficient.strictMono_coefficient
#print axioms BlockPermanents.FiveFreeCoefficient.cubic
#print axioms BlockPermanents.FiveFreeCoefficient.uniform_eq_iff
#print axioms BlockPermanents.FiveFreeResidual.long_resolution
#print axioms BlockPermanents.FiveFreeResidual.full_test_squares
#print axioms BlockPermanents.FiveFreeResidual.testing_exact
#print axioms BlockPermanents.FiveFreeResidual.testing_free_cable_squares
#print axioms BlockPermanents.FiveFreeResidual.tripleRemainder_nonneg
#print axioms BlockPermanents.FiveOuterSquares.outer_squares
#print axioms BlockPermanents.FiveOuterSquares.assignmentRemainder_nonneg
#print axioms BlockPermanents.FiveScalarSquares.scalar_resolution
#print axioms BlockPermanents.FiveScalarSquares.long_cycle_squares
#print axioms BlockPermanents.FiveScalarSquares.coarse_difference
#print axioms BlockPermanents.FiveScalarSquares.packet_tests
#print axioms BlockPermanents.FiveScalarSquares.testSquares_nonneg
#print axioms BlockPermanents.FiveTriangleExample.triangle_trace
#print axioms BlockPermanents.FiveTriangleExample.thin_gram
#print axioms BlockPermanents.FiveTriangleExample.thin_minors
#print axioms BlockPermanents.FiveTriangleExample.thin_determinants
#print axioms BlockPermanents.FiveTriangleExample.packet_units
#print axioms BlockPermanents.FiveTriangleExample.triangle_sign
#print axioms BlockPermanents.FiveFullCertificate.unit_identity
#print axioms BlockPermanents.FiveFullCertificate.unit_five
#print axioms BlockPermanents.FiveFullCertificate.marcus_five
#print axioms BlockPermanents.FiveCubicExample.survivor_gram
#print axioms BlockPermanents.FiveCubicExample.one_cap
#print axioms BlockPermanents.FiveCubicExample.cut_energy
#print axioms BlockPermanents.FiveCubicExample.pair_cuts
#print axioms BlockPermanents.FiveCubicExample.disjoint_pairs
#print axioms BlockPermanents.FiveCubicExample.coarse_five
#print axioms BlockPermanents.FiveCubicExample.one_two_split

#print axioms BlockPermanents.FaceStraightSquares.spectator_squares
#print axioms BlockPermanents.FaceStraightSquares.keep_squares
#print axioms BlockPermanents.FaceStraightSquares.keep_three_squares
#print axioms BlockPermanents.FaceStraightSquares.keep_four_squares
#print axioms BlockPermanents.FaceStraightSquares.keepRemainder_nonneg
#print axioms BlockPermanents.FaceStraightSquares.spectatorRemainder_nonneg

#print axioms BlockPermanents.FaceMeanSquares.triple_identity
#print axioms BlockPermanents.FaceMeanSquares.quad_identity
#print axioms BlockPermanents.FaceMeanSquares.tripleRemainder_nonneg
#print axioms BlockPermanents.FaceMeanSquares.quadRemainder_nonneg

#print axioms BlockPermanents.RawTripleFaces.face_card
#print axioms BlockPermanents.RawTripleFaces.subset_sum
#print axioms BlockPermanents.RawTripleFaces.exitTotal_marked
#print axioms BlockPermanents.RawTripleFaces.triple_faces
#print axioms BlockPermanents.RawTripleFaces.quadruple_faces
#print axioms BlockPermanents.RawTripleFaces.three_face_bound
#print axioms BlockPermanents.RawTripleFaces.four_face_bound
#print axioms BlockPermanents.FacePropagationSquares.propagate_squares
#print axioms BlockPermanents.FacePropagationSquares.propagation_nonneg

#print axioms BlockPermanents.RawFaceMeans.mem_configs
#print axioms BlockPermanents.RawFaceMeans.fiber_card
#print axioms BlockPermanents.RawFaceMeans.card_configs
#print axioms BlockPermanents.RawFaceMeans.sum_eq
#print axioms BlockPermanents.RawFaceWeights.slack_perm
#print axioms BlockPermanents.RawFaceWeights.edgeWeight_image
#print axioms BlockPermanents.RawFaceWeights.faceSlack_image
#print axioms BlockPermanents.RawFaceWeights.value_forget
#print axioms BlockPermanents.RawFaceWeights.sum_eq
#print axioms BlockPermanents.RawFaceCertificate.raw_identity
#print axioms BlockPermanents.RawFaceCertificate.raw_bound
#print axioms BlockPermanents.RawFaceCertificate.four_exact
#print axioms BlockPermanents.FourTradeSquares.one_division
#print axioms BlockPermanents.FourTradeSquares.remainder_nonneg
#print axioms BlockPermanents.FourTradeSquares.gram_identity
#print axioms BlockPermanents.FaceTradeSquares.four_identity
#print axioms BlockPermanents.FaceTradeSquares.remainder_nonneg
#print axioms BlockPermanents.FaceCoarseCertificate.coarse_identity
#print axioms BlockPermanents.FaceCoarseCertificate.remainder_nonneg
#print axioms BlockPermanents.FaceCounts.coeff_zero
#print axioms BlockPermanents.FaceCounts.coeff_succ

example : BlockPermanents.ManuscriptTheorem := BlockPermanents.PaperCertificate.manuscript

-- Resolve the Lean entry points in the manuscript index against this build.
run_cmd do
  let env ← Lean.getEnv
  let names : List Lean.Name := [
    `BlockPermanents.BalancedAssembly.opening,
    `BlockPermanents.BalancedCubic.cubic_certificate_all_dimensions,
    `BlockPermanents.BalancedCubicMarcus.marcus,
    `BlockPermanents.BalancedEvaluation.opening,
    `BlockPermanents.BalancedLast.marcus_thick,
    `BlockPermanents.BalancedLast.subspace_compression_psd,
    `BlockPermanents.BalancedLast.subspace_last_cap_weight,
    `BlockPermanents.BalancedLast.subspace_marked_decomposition,
    `BlockPermanents.BalancedLastExample.cubic_shortfall,
    `BlockPermanents.BalancedSigned.signed_gluing,
    `BlockPermanents.Bend.bent_schur,
    `BlockPermanents.Bend.evaluate_bend,
    `BlockPermanents.Bend.two_block_gap,
    `BlockPermanents.Closures.defect_closure,
    `BlockPermanents.Closures.fine_closure,
    `BlockPermanents.Closures.packet_closure,
    `BlockPermanents.ComplexCapExample.matching_term,
    `BlockPermanents.ComplexCapExample.permanent_gap,
    `BlockPermanents.ComplexCapExample.single_cap,
    `BlockPermanents.CountingExamples.five_marks,
    `BlockPermanents.CountingExamples.four_matchings,
    `BlockPermanents.CountingExamples.four_path_coefficients,
    `BlockPermanents.CountingExamples.whole_edges,
    `BlockPermanents.CycleCoefficients.ten_coefficients,
    `BlockPermanents.Digon.clasp_recursion,
    `BlockPermanents.Digon.merge_split,
    `BlockPermanents.Digon.split_merge,
    `BlockPermanents.DisjointCycleCertificate.certificate,
    `BlockPermanents.DisjointCycleCertificate.marcus,
    `BlockPermanents.FaceCounts.coeff_succ,
    `BlockPermanents.FiveCubicExample.coarse_five,
    `BlockPermanents.FiveCubicExample.cut_energy,
    `BlockPermanents.FiveCubicExample.disjoint_pairs,
    `BlockPermanents.FiveFreeCoefficient.uniform_eq_iff,
    `BlockPermanents.FiveFreeResidual.testing_free_cable_squares,
    `BlockPermanents.FiveFullCertificate.marcus_five,
    `BlockPermanents.FiveFullCertificate.unit_identity,
    `BlockPermanents.FiveMixedAverageSquares.plain_squares,
    `BlockPermanents.FiveMixedAverageSquares.weighted_squares,
    `BlockPermanents.FiveMixedSquares.physical_trace,
    `BlockPermanents.FiveProjection.remainder_posSemidef,
    `BlockPermanents.FiveScalarSquares.long_cycle_squares,
    `BlockPermanents.FiveTriangleExample.triangle_sign,
    `BlockPermanents.ForcedQuadratics.forced_weight,
    `BlockPermanents.ForcedWitness.evaluate_eq,
    `BlockPermanents.ForcedWitness.witness_eq_transfer,
    `BlockPermanents.FourAtomExample.gap_fourteen,
    `BlockPermanents.FourAtomExample.proper_values,
    `BlockPermanents.FourNative.four_packet_bend,
    `BlockPermanents.FourTarget.four_average_actual,
    `BlockPermanents.FourTrade.gram_trade,
    `BlockPermanents.FourTradeSquares.gram_identity,
    `BlockPermanents.GramInverse.projection_spec,
    `BlockPermanents.IntroExamples.alternating_ne_zero,
    `BlockPermanents.IntroExamples.bent_interchange_psd,
    `BlockPermanents.IntroExamples.cap_cup_action,
    `BlockPermanents.IntroExamples.interchange_alternating,
    `BlockPermanents.IntroExamples.three_quadratic,
    `BlockPermanents.IntroExamples.three_strands,
    `BlockPermanents.IntroExamples.two_strands,
    `BlockPermanents.IntroExamples.upright_two,
    `BlockPermanents.MarkedBoundaryExample.averaged,
    `BlockPermanents.MarkedBoundaryExample.drawings,
    `BlockPermanents.MarkedBoundaryExample.fixed_boundary,
    `BlockPermanents.MarkedEdges.quadratic_readout,
    `BlockPermanents.MarkedWitness.negative_fifth_full_clasps,
    `BlockPermanents.MatchingCoarse.averaged_peel_identity,
    `BlockPermanents.MatchingCoarse.peel_identity,
    `BlockPermanents.MatchingFineSquares.average_identity,
    `BlockPermanents.MatchingFineSquares.unit_identity,
    `BlockPermanents.MatchingThreshold.marcus_threshold,
    `BlockPermanents.MatchingUpper.permanent_le_upper,
    `BlockPermanents.Negative.all_marked_values,
    `BlockPermanents.Negative.mean_is_defect,
    `BlockPermanents.Negative.witness_factors,
    `BlockPermanents.OccupationCoefficient.routed_entry,
    `BlockPermanents.OccupationRouting.complex_seam,
    `BlockPermanents.OccupationRouting.operator_split,
    `BlockPermanents.OpeningExamples.all_ones_example,
    `BlockPermanents.OpeningExamples.fork_two_one,
    `BlockPermanents.OpeningExamples.whole_permanent_and_gap,
    `BlockPermanents.OpeningExamples.whole_split_counts,
    `BlockPermanents.PairOrthonormalExample.equality_four,
    `BlockPermanents.PairOrthonormalExample.middle_energy,
    `BlockPermanents.PairOrthonormalExample.middle_trace,
    `BlockPermanents.PairResidual.full_caps_residual_operator,
    `BlockPermanents.PairResidual.full_caps_residual_squares,
    `BlockPermanents.PaperCertificate.logarithmic,
    `BlockPermanents.PaperCertificate.manuscript,
    `BlockPermanents.PaperCertificate.spectral_threshold,
    `BlockPermanents.PathSpectrum.spectral_threshold,
    `BlockPermanents.PieceProductSquares.class_squares,
    `BlockPermanents.PieceProductSquares.product_squares,
    `BlockPermanents.PivotCertificate.marcus,
    `BlockPermanents.PivotCertificate.unit_identity,
    `BlockPermanents.Quadratic.four_times_one_cap,
    `BlockPermanents.RawCycleSquares.odd_cycle_real,
    `BlockPermanents.RawCycleSquares.odd_cycle_squares,
    `BlockPermanents.RawFaceCertificate.raw_bound,
    `BlockPermanents.RawFaceCertificate.raw_identity,
    `BlockPermanents.RawTripleFaces.quadruple_faces,
    `BlockPermanents.RawTripleFaces.triple_faces,
    `BlockPermanents.RefinedThreshold.six_four,
    `BlockPermanents.RoutedFamilyProjection.family_gram,
    `BlockPermanents.RoutedFamilyProjection.mem_projection_range,
    `BlockPermanents.RoutedFamilyProjection.projection_spec,
    `BlockPermanents.RoutedSubspaceProjection.dual_range,
    `BlockPermanents.RoutedSubspaceProjection.for_subspace,
    `BlockPermanents.RoutedTrace.clasped_intersection,
    `BlockPermanents.RoutedTrace.last_cap_gram,
    `BlockPermanents.RoutingFibres.iterate_clasp_step,
    `BlockPermanents.RoutingFibres.iterate_expand,
    `BlockPermanents.RoutingFibres.iterate_one,
    `BlockPermanents.RoutingFibres.marked_expand,
    `BlockPermanents.RoutingFibres.quadratic_polynomial,
    `BlockPermanents.RoutingFibres.signedTransfer_eq_marked,
    `BlockPermanents.Routings.capGram_posDef,
    `BlockPermanents.SchurNormalization.homogeneousSchur,
    `BlockPermanents.SchurNormalization.homogeneousSchur_implies_unbent,
    `BlockPermanents.SixCycleExample.class_card,
    `BlockPermanents.SixCycleExample.polynomial,
    `BlockPermanents.Support.orthogonal_cut,
    `BlockPermanents.SupportCup.bubble,
    `BlockPermanents.SupportRouteExamples.crossed_gluing,
    `BlockPermanents.SupportRouteExamples.glued_seam,
    `BlockPermanents.SupportRouteExamples.perpendicular_rows,
    `BlockPermanents.SupportRouteExamples.reflected_agree,
    `BlockPermanents.SupportRouteExamples.reflected_seam,
    `BlockPermanents.SupportRouteExamples.seam_energy,
    `BlockPermanents.SupportRouteExamples.supported_bubble,
    `BlockPermanents.TenEndpoint.marcus_ten,
    `BlockPermanents.ThreeGeneralOpen.canonical_raw,
    `BlockPermanents.ThreeGeneralOpen.original_bent,
    `BlockPermanents.ThreeLastCap.concrete_resolution,
    `BlockPermanents.ThreeOnesExample.physical_terms,
    `BlockPermanents.ThreeOnesExample.raw_permanents,
    `BlockPermanents.ThreePlane.routed_resolution,
    `BlockPermanents.ThreePlane.subspace_compression_psd,
    `BlockPermanents.ThreePlane.subspace_decomposition,
    `BlockPermanents.Threshold.five_coefficients,
    `BlockPermanents.Threshold.pathCoeff,
    `BlockPermanents.Threshold.tradeMatrix_six_four_psd,
    `BlockPermanents.TradePivots.six_four,
    `BlockPermanents.TradePivots.trade_parameter,
    `BlockPermanents.Transfer.packet_transfer,
    `BlockPermanents.Transfer.tensor_packet_transfer,
    `BlockPermanents.TransferBlocks.four_supported,
    `BlockPermanents.TwoCapExample.gram,
    `BlockPermanents.TwoCapExample.joint_energy,
    `BlockPermanents.TwoCapExample.separate_energy,
    `BlockPermanents.TwoFullCaps.full_words,
    `BlockPermanents.TwoMarkedExample.adapted_wire,
    `BlockPermanents.TwoMarkedExample.sole_survivor,
    `BlockPermanents.TwoMarkedExample.subspace_example,
    `BlockPermanents.TwoMarkedExample.three_placements,
    `BlockPermanents.TwoStepSquares.unordered_path_squares,
    `BlockPermanents.VerifiedPaper.four_quadratic,
    `BlockPermanents.VerifiedPaper.plane_compression,
    `BlockPermanents.ZeroCap.opening,
    `BlockPermanents.ZeroCap.singleton_clasp,
    `BlockPermanents.two_block_squares
  ]
  for n in names do
    unless env.contains n do
      throwError "Unknown declaration in the manuscript index: {n}"

#print axioms BlockPermanents.PaperCertificate.manuscript
#print axioms BlockPermanents.PaperCertificate.spectral_threshold
#print axioms BlockPermanents.PaperCertificate.logarithmic
#print axioms BlockPermanents.RoutedCapMatrix.apply_cap
#print axioms BlockPermanents.RoutedCapMatrix.apply_reflect
#print axioms BlockPermanents.RoutedUniform.clasped_intersection
#print axioms BlockPermanents.RoutedOccupationFrame.complete
#print axioms BlockPermanents.RoutedFamilyProjection.family_gram
#print axioms BlockPermanents.RoutedFamilyProjection.mem_projection_range
#print axioms BlockPermanents.RoutedSubspaceProjection.for_subspace
#print axioms BlockPermanents.RoutedSubspaceProjection.dual_range
#print axioms BlockPermanents.MatchingFineSquares.ordered_identity
#print axioms BlockPermanents.MatchingFineSquares.average_identity
#print axioms BlockPermanents.PathJacobi.determinant
#print axioms BlockPermanents.PathJacobi.trace_square
#print axioms BlockPermanents.PathSpectrum.paired_spectrum
#print axioms BlockPermanents.PathMeans.maclaurin_multiset
#print axioms BlockPermanents.PathSpectrum.spectral_threshold
#print axioms BlockPermanents.TradePivots.matrix_pivots
#print axioms BlockPermanents.TradePivots.degree_budget
#print axioms BlockPermanents.TradePivots.six_four
#print axioms BlockPermanents.PivotCertificate.unit_identity
#print axioms BlockPermanents.PivotCertificate.marcus
#print axioms BlockPermanents.PieceScoreProduct.score_split
#print axioms BlockPermanents.PieceProductSquares.product_squares
#print axioms BlockPermanents.PieceProductSquares.class_squares
#print axioms BlockPermanents.DisjointCycleCertificate.certificate
#print axioms BlockPermanents.DisjointCycleCertificate.matrix_gap
#print axioms BlockPermanents.DisjointCycleCertificate.marcus
#print axioms BlockPermanents.NegativeOpenTransport.orthogonal_unit_pair
#print axioms BlockPermanents.NegativeOpenTransport.fine_cuts
#print axioms BlockPermanents.FourAtomExample.middle_matrix
#print axioms BlockPermanents.ThreeOnesExample.raw_gap
#print axioms BlockPermanents.TwoCapExample.joint_energy
#print axioms BlockPermanents.SixCycleExample.class_estimate
