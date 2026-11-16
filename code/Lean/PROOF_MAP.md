# Proof map for the 16 November draft

This is the historical r03 coverage map with subsequent checkpoint notes. The [manuscript index](MANUSCRIPT_INDEX.md) supersedes its early status entries. Stages 5 and 10 establish equation (5C.3) and Theorem 5D.1. [Stage 15](STAGE_15.md) proves the general homogeneous Schur relation and discharges the Schur inputs in Theorem 1A.1. [Stage 20](STAGE_20.md) verifies the explicit residual halfwebs and the polarized Gram identity for Lemma 7A.1. [Stage 25](STAGE_25.md) proves the arbitrary-subspace form of the three-packet decomposition in Theorem 3D.2, from the supported trace cup to the matrix inequality. [Stage 30](STAGE_30.md) verifies the individual border squares in Lemma 6B.1, the supported thick proof of Lemma 6B.3 and the signed cubic proof of Theorem 6C.3. [Stage 32](STAGE_32.md) verifies the global reflected-square identity in Lemma 7E.1. [Stage 34](STAGE_34.md) verifies Lemma AB.1 with the raw matching and cycle counts. [Stage 35](STAGE_35.md) verifies the five-packet expansion of Section 8 and derives the matrix inequality from that expansion.

The public theorem `BlockPermanents.manuscript_theorem` proves every matrix case in Theorem 1A.1. The rows below also track the independent statements about supported operators, routed caps, and the alternative proofs.

Names below omit the namespace prefix `BlockPermanents.`. The matrix index `Fin m × Fin k` is a packet label followed by a slot. `MarcusAt m k` asserts that the difference of mathlib's two complex permanents is a nonnegative real. This formulation also checks that the imaginary part of the difference vanishes.

| Manuscript | Checked declaration | Scope |
|---|---|---|
| Theorem 1A.1, boundary cases | `one_packet`, `thickness_one` | Equality, by reindexing the actual permanent |
| Lemma 1B.2 | `Quadratic.four_times_one_cap`, `two_quadratic` | Independent expansion of the full permanent and all block permanents in arbitrary complex coordinates. No web relation is needed |
| Lemmas 2B.2, 2C.2, 2C.6 | `SchurNormalization.homogeneousSchur_implies_unbent`, `Bend.evaluate_bend`, `Bend.bent_schur` | Normalization, bending on a product, and the open operator equality for all thicknesses |
| Lemma 2D.1 | `Support.orthogonal_cut` | Arbitrary half-map and orthogonal projector |
| Lemma 2E.3 | `Closures.packet_gram`, `Closures.fine_closure`, `Closures.packet_closure`, `Closures.defect_closure` | Arbitrary numbers and sizes of packets, arbitrary finite Gram dimension. Includes the polarized identity for different columns on the two boundaries |
| Lemma 2F.1 | `two_block_squares`, `marcus_two` | Proper-cut identity and matrix inequality for every positive thickness |
| Lemma 3B.2 | `Transfer.packet_transfer`, `Transfer.tensor_packet_transfer` | General packet number. Lean counts the exits from the clasp and uses simultaneous conjugation at the boundary |
| Lemma 3D.1 and Theorem 3D.2 | `Support.lastCap_bubble`, `Support.resolve_last_cap`, `Support.three_full_cap_weight` | Supported bubble, orthogonal decomposition and last coefficient. For k=2 the corrected marked operator is now checked independently. `ThreeLastCap.concrete_resolution` supplies the full projected last-cap identity on supported columns. The independent identification of all general-thickness halves with the original three-packet operator is tracked in the extensions below |
| Lemmas 3E.2–3 and 4B.2 | `Routings.Routing.relativeA_table`, `Routings.Routing.transferred_eq`, `Routings.Routing.transferred_sum`, `Routings.placementAverage_eq` | Routing recurrence, marked coefficients in units of the routing weight, and occupation fiber counts. The identification of the full operator expansion with these tables is open |
| Lemma 5A.3 | `Routings.lastCapOnWords_eq`, `Routings.capGram_posDef`, `Routings.gramProjection_spec` | Word-coordinate gluing, nonsingular Gram matrix and orthogonal projection. The arbitrary singular Gram projector is proved in `GramInverse.projection_spec`. |
| Lemma 5B.1 | `TransferBlocks.correction_mixed`, `TransferBlocks.four_average`, `TransferBlocks.four_supported` | The two mixed coefficients, the simultaneous four-packet average and the ordered-boundary support |
| Lemma 7A.1 | `PacketSupport.splitSupport_dimension`, `TraceBound.trace_normSq_le`, `PairBound.cut_trace`, `PairBound.full_caps_normalized`, `PairSquares.full_caps_squares` | The subset expansion, dimension bound, completed trace and the scalar pair inequality for every thickness. For each fixed first packet, Lean proves that one matrix of linear forms factors the entire remainder on every symmetric second input. This last step uses a PSD square root. Identification with the particular list of drawn residual halfwebs is open |
| Section 7B on three labels | `ThreeCoarse.three_exit_identity_general`, `ThreeBlocks.three_gram`, `marcus_three` | Exact coarse defect as three squared distances between cap exits. Pair strengthening and averaging the three spectator choices prove the matrix inequality for k ≥ 3, including zero packets |
| Theorem 7C.1, coefficient estimate | `Threshold.pathCoeff_le_fine`, `Threshold.matching_sum_le`, `Threshold.threshold_of_square_le_pow` | All m and all degrees. The proof groups weighted path edges and balances integer weights. The new matching estimates carry this bound to the original matrix |
| Sections 7D and Appendix A | `Threshold.tradeMatrix_six_four_psd`, `Cycles.signedProduct_identity` | The (6,4) numerical matrix and the sign expansion on disjoint cycles. `TenEndpoint.marcus_ten` applies the full ten-label class bound to the actual PSD matrix. |
| Lemma 9A.2 and Appendix B | `Negative.witness_factors`, `Negative.all_marked_values`, `Negative.mean_is_defect`, `Occupation.fine_eq_symmetrized_tensor` | Both complex factorizations, all five exact rational marks, their mean, and the fine closure as a true symmetrized tensor inner product. The explicit complex clasp recurrence is checked in MarkedAverage |

## Manuscript correction

At the end of the proof of Lemma 5B.1 the paper uses `[B]=X₃` after declaring that brackets average over S₄. The preceding S₃ identity gives `[B]_{S₄}=[X₃]_{S₄}`. This is exactly the equality required when averaging the term X₄−X₃. The stated conclusion `[Q]_{S₄}=X₄` follows. The original source line is 1857.

## Extensions in this release

| Manuscript | Lean declaration | What is proved |
|---|---|---|
| Three quadratic packets, Sections 3C–D | `ThreeWire.fixed_transfer_quadratic`, `ThreeWire.fixed_transfer_positive`, `marcus_three_quadratic` | Exact marked transfer on a boundary invariant under the three internal exchanges, its positivity on atom packets, and the inequality on every complex PSD matrix. The mean is identified with 288 times its permanent difference. The certificate is specific to k=2. |
| Section 3D, general k | `ThreeTransfer.bend_cross`, `ThreeSupport.fullThree_le`, `ThreeSupport.last_weight_nonnegative` | The mixed operator interchange and the supported full-cap contribution. The independent matching proof gives the matrix statement for all k ≥ 3. |
| Sections 5B–D | `FourTarget.four_average_actual`, `FourTarget.averaged_gap`, `FourRoutes.three_openings`, `FourBend.full_cap_square`, `FourLastCaps.port_gluing`, `FourLastCaps.four_word_bound`, `FourComplement.spectator_cancellation` | The actual four-packet marked average on thin-slot words, the actual matrix gap, three concrete Schur openings, the full-cap square, supported port gluings, and the three-row estimate with its last-cap values as hypotheses. `FourMatrix.marked_cutForm` proves the identification on matrix packets. `FourMatrix.marcus_four_quadratic` gives the original PSD-matrix conclusion; `FourSupportedTensor.nonnegative` proves positivity of the cut form on the entire span of supported products. |
| Section 6 | `MatchingThreshold.four_blocks` | Matrix conclusions for k=3 and all larger thicknesses by the general matching argument. The independent matrix proof `BalancedEndpoint.marcus_four` opens the balanced cut and glues the four survivors; `CubicSquares.cubic_identity` gives the 37/4 square completion on products. |
| Section 7B | `MatchingFine.ordered_fine_bound`, `MatchingFine.average_fine_bound`, `MatchingCoarse.peel_identity`, `MatchingCoarse.averaged_peel_identity`, `MatchingUpper.permanent_le_upper` | Fine and coarse bounds on the actual Gram families for all m. The peeled coarse expression includes the exact squared-error remainder. |
| Section 7C | `MatchingThreshold.gram_threshold`, `MatchingThreshold.marcus_threshold`, `MatchingThreshold.marcus_logarithmic` | Full arbitrary-m matrix theorem and logarithmic consequence. The coefficient proof uses an integer-weight balancing argument. |
| Sections 7D–E and Appendix A | `FourTrade.gram_trade`, `TradeMatrix.compare`, `CycleMatching.path_bound`, `CycleMatching.odd_cycle_cut`, `CycleCoefficients.ten_coefficients` | The weighted four-label estimate for actual unit vectors, spectral comparison given the weighted estimates, the two-step/odd-cycle estimates, and the exact ten-label coefficient table. `RefinedThreshold.marcus` proves the general criterion on the original matrix. `FaceCounts` derives the raw face coefficients. `TenEndpoint.marcus_six` and `TenEndpoint.marcus_ten` give all the thicknesses claimed in the examples. |
| Section 8 | `FiveProjection.testing_free_cable`, `FiveProjection.remainder_posSemidef`, `FiveAverage.plain`, `FiveAverage.weighted`, `FiveCycles.permanent_cycles`, `FiveCycles.long_cycles`, `FiveMain.marcus_five` | All five-packet matrix cases in the draft, including k=3. The proof evaluates the Gram matrix of the actual atoms. Three nonzero cuts already suffice for the uniform constant 41/20. |
| Section 9 and Appendix B | `MarkedWitness.coarse_complex`, `MarkedWitness.fine_complex`, `MarkedWitness.witness_complex_gap`, `MarkedAverage.negative_fifth_full_clasps`, `MarkedEdges.quadratic_readout` | The true complex clasp and Gram-permanent evaluations of the witness, all marks, the recurrence with full packet-clasp sums, and marked-edge inclusion–exclusion on quadratic thin-slot permutations. `ForcedRoutes.fiber` and `ForcedQuadratics.forced_weight` factor the constrained strand sum into the Gram factors and an untouched mixed closure on the unused slots. |

The all-thickness matrix input is the stated homogeneous symmetric-web relation. No original inequality from the manuscript appears as a hypothesis in the documented matrix endpoints. A proof of the matrix conclusion by a second method leaves any stronger or independent operator identities listed above as separate obligations.

## Manuscript fingerprints

| Supplied input | SHA-256 |
|---|---|
| main(8).tex | `d74e3e35195f2a9c8d3d6dd7895afe5f098e8d78da7d761b536237302598ef39` |
| Permanents(3).pdf | `79e1c7053b6966721f1aea3763c23a71f64e72389efe4db643e2c667a9238043` |

## Section 6 after Stage 30

| Manuscript | Lean entry point | Scope |
|---|---|---|
| Three balanced divisions on the upright boundary | `BalancedDivision.three_division_average`, `BalancedDivision.defect_gram` | Actual internally symmetric packet products, the three relabelled marked operators and the original Gram permanent difference |
| Lemma 6B.1 | `BalancedLast.subspace_last_cap_weight` | Independent marked planes, all four trace-cup remainders per pairing and all interior cuts |
| Lemma 6B.3 | `BalancedLast.subspace_marked_decomposition`, `BalancedLast.subspace_compression_psd`, `BalancedLast.marcus_thick` | Exact squared differences, all finite families of supported columns and the averaged matrix inequality for k ≥ 4 |
| Example 6B.4 | `BalancedLastExample.cubic_shortfall` | Four copies of any complex unit packet give single-edge diagonal 9 and coherent energy 16 |
| Theorem 6C.3 | `BalancedCubic.cubic_certificate`, `BalancedCubic.cubic_certificate_all_dimensions`, `BalancedCubicMarcus.marcus` | The signed 37/4 decomposition on physical three-planes, the intrinsic span formula in every Gram dimension, and the cubic matrix inequality |

## Further operator identities

`ThreeGeneralOpen.general_raw` in `ThreeGeneralRaw` checks the two openings, mixed full-cap terms and terminal negative square in all thicknesses, on symmetric upright matrices. `ThreeGeneralOpen.canonical_raw` and `ThreeGeneralOpen.original_bent` identify the original marked operator. `OccupationSplit.clasp_occupation` checks the multicolour probability in the split of a symmetric positive cable.


## Sections 7E, 8 and Appendix AB after Stage 35

| Manuscript | Lean entry point | Scope |
|---|---|---|
| Lemma 7E.1 | `TwoStepSquares.unordered_path_squares`, `TwoStepSpectator.path_squares` | Incident-edge exterior squares and opposite-edge uncrossing squares with their orientation factors, also with a disjoint matching held fixed |
| Lemma AB.1 and (AB.2) | `RawCycleSquares.odd_cycle_squares`, `RawCycleSquares.odd_cycle_real` | Both signs on any unit Gram family with q ≥ 2r+1. The oriented cycle sum is real, and the out-of-range matching sum vanishes when q = 2r+1 |
| Example 8A.2 | `FiveCubicExample.cut_energy`, `FiveCubicExample.disjoint_pairs`, `FiveCubicExample.coarse_five` | The cap energies of the orthogonal cubic packet are 1, 1/3, 1/3 and 1. Two disjoint pair cuts contribute 64, and the coarse closure is 120 |
| Lemma 8A.5 | `FiveFreeResidual.testing_free_cable_squares`, `FiveFreeCoefficient.uniform_eq_iff` | Proper cuts, the full test and the sharp uniform free-cable coefficient on k ≥ 3 |
| Example 8B.2 | `FiveTriangleExample.triangle_sign` | Concrete real cubics with all pair squares equal to 1/64 and signed triangle terms ±1/512 |
| Lemma 8B.3 and (8B.4) | `FiveMixedSquares.physical_trace`, `FiveMixedAverageSquares.plain_squares`, `FiveMixedAverageSquares.weighted_squares` | Polarized Gram halves, a conjugated tensor square before averaging and the exact four- and two-label multiplicities |
| Lemma 8C.1 | `FiveScalarSquares.long_cycle_squares` | Exact squared differences for both long-cycle bounds |
| Theorem 8A.1 | `FiveFullCertificate.unit_identity`, `FiveFullCertificate.marcus_five` | The full five-packet gap on normalized physical data and its consequence for all complex PSD matrices at k ≥ 3 |

Stages 36–39 verify both raw face sums and the propagated square remainder in (AA.2) and (AA.4). See `RawTripleFaces.triple_faces`, `RawTripleFaces.quadruple_faces` and `RawFaceCertificate.raw_identity`. Stage 40 supplies the signed real-parameter product for each disjoint-cycle class, the spectral and pivot proofs, and the joint projection for the actual routed caps. The [manuscript index](MANUSCRIPT_INDEX.md) gives the final verification scope and current entry points for every numbered theorem, lemma and example.
