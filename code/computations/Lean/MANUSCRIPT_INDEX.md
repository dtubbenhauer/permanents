# Manuscript verification index

The 16 November draft of *Positivity in Symmetric Webs and Block Permanents* by Daniel Tubbenhauer contains **6 theorems, 42 lemmas and 24 examples**. The first table gives one row per theorem or lemma in printed order. The second covers the examples. Numbers follow the PDF, including the doubled letters in the appendix numbers. The source column gives the opening line of the statement in the supplied TeX file and its own label when it has one. Lean names below omit the common prefix `BlockPermanents.`.

**The main matrix statement has an unconditional proof.** `PaperCertificate.manuscript` proves the claimed ranges for complex positive semidefinite matrices, with the permanent difference a nonnegative real. `PaperCertificate.logarithmic` gives the logarithmic sufficient condition. These are sufficient ranges. The paper does not claim the inequality for all packet numbers and thicknesses.

**Interpretation.** An open web is interpreted as a matrix on finite-dimensional complex tensor-word spaces. A clasp is the permutation-average projector, bending is partial transpose, reflection is conjugate transpose, and a closed square is the squared norm of the interpreted half. Supported-space theorems specify their marked subspaces, and Gram factorization connects these operators to the permanent inequality. The project proves the homogeneous Schur relation in these coordinates. This index counts statements about those operators and scalars. A presentation of the abstract web category, graphical typography, historical attributions and bibliography fall outside that count.

## Theorems and lemmas

| Printed result | What is checked | Lean entry points | TeX source |
|---|---|---|---|
| Theorem 1A.1 | Matrix inequality for every stated case, including the threshold and its logarithmic consequence. | `PaperCertificate.manuscript`, `PaperCertificate.logarithmic` | 150 (thm:matrix) |
| Lemma 1B.2 | Two quadratic packets. Direct expansion identifies the permanent difference with four times the one-cap energy. | `Quadratic.four_times_one_cap` | 304 (lem:intro-square) |
| Lemma 2A.2 | Both digon identities for the actual symmetric split and merge. | `Digon.merge_split`, `Digon.split_merge` | 618 |
| Lemma 2B.2 | Homogeneous and isometric Schur identities in the finite-dimensional representation, for arbitrary sizes. The proof counts permutation double cosets. | `SchurNormalization.homogeneousSchur`, `SchurNormalization.homogeneousSchur_implies_unbent` | 673 |
| Lemma 2B.6 | Clasp recursion on ordinary words from the one-strand Schur relation. | `Digon.clasp_recursion`, `ZeroCap.singleton_clasp` | 693 |
| Lemma 2C.1 | The trace cup has closed value equal to the dimension. The reverse composite on a product is its evaluation times the trace cup. | `SupportCup.bubble`, `IntroExamples.cap_cup_action` | 709 |
| Lemma 2C.2 | Partial transpose preserves the quadratic-form evaluation on a product when the marked input is conjugated. | `Bend.evaluate_bend` | 727 |
| Lemma 2C.6 | The bent Schur operator is the binomially weighted sum of actual cap-adjoint products. | `Bend.bent_schur`, `SchurNormalization.homogeneousSchur` | 755 (thm:bent) |
| Lemma 2D.1 | Exact orthogonal decomposition of the Gram form at a cut. | `Support.orthogonal_cut` | 799 |
| Lemma 2E.3 | Fine and packet closures equal the respective permanents. The polarized identity allows distinct packets on the two sides. | `Closures.fine_closure`, `Closures.packet_closure`, `Closures.defect_closure` | 842 (loc:gramclosures) |
| Lemma 2F.1 | Exact two-block gap on symmetric packets at every positive thickness, including the empty sum of proper cuts. | `Bend.two_block_gap`, `two_block_squares` | 872 (loc:two) |
| Lemma 3A.2 | Rectangular Schur opening on all ordinary and marked word coordinates, including the zero and terminal terms. | `ZeroCap.opening` | 1183 (prop:tr-zero) |
| Lemma 3B.2 | Transfer under simultaneous upper/lower relabeling, including the tensor-coordinate representation. | `Transfer.packet_transfer`, `Transfer.tensor_packet_transfer` | 1220 (lem:tr-transfer) |
| Lemma 3C.2 | Corrected bend with the two full caps and their mixed terms, for arbitrary thickness and positive ordinary packet count. | `TwoFullCaps.full_words` | 1309 |
| Lemma 3C.5 | Exact three-packet raw opening of the original marked operator, including the negative terminal square. | `ThreeGeneralOpen.canonical_raw`, `ThreeGeneralOpen.original_bent` | 1352 |
| Lemma 3D.1 | Supported trace bubble and last-cap decomposition, with the perpendicular component retained. | `ThreeLastCap.concrete_resolution`, `ThreePlane.routed_resolution` | 1376 |
| Theorem 3D.2 | Supported decomposition and positivity on an arbitrary marked subspace of the stated dimension. This establishes the stronger operator statement independently of the matching proof of the matrix inequality. | `ThreePlane.subspace_decomposition`, `ThreePlane.subspace_compression_psd` | 1402 (thm:three) |
| Lemma 3E.2 | The iterated transfer has the printed coefficient for each routing. Clasp insertion identifies the coefficient recurrence with the actual operator iteration. | `RoutingFibres.iterate_expand`, `RoutingFibres.iterate_clasp_step`, `RoutingFibres.iterate_one` | 1477 |
| Lemma 3E.3 | Split-end coefficient in the signed marked transfer, on the representation of actual strand permutations. | `RoutingFibres.marked_expand`, `RoutingFibres.signedTransfer_eq_marked` | 1495 |
| Lemma 4B.2 | Each clasped routed Gram is scalar on its occupation sector. The generalized inverse of the sector blocks gives the orthogonal projector onto the sum of the reflected cap images, also for an arbitrary marked subspace. | `RoutedTrace.clasped_intersection`, `RoutedFamilyProjection.family_gram`, `RoutedFamilyProjection.projection_spec`, `RoutedFamilyProjection.mem_projection_range`, `RoutedSubspaceProjection.dual_range`, `RoutedSubspaceProjection.for_subspace` | 1607 (prop:routedcaps) |
| Lemma 5A.3 | Gram entries on each sector, nonsingular Gram estimate, and projection onto the span using the generalized inverse in the singular case. | `RoutedTrace.last_cap_gram`, `Routings.capGram_posDef`, `GramInverse.projection_spec` | 1719 (lem:fourports) |
| Lemma 5B.1 | Four-packet marked transfer, support under the clasp, and its simultaneous average. See the proof correction below. | `TransferBlocks.four_supported`, `FourTarget.four_average_actual` | 1795 |
| Lemma 5C.2 | All three families of open cuts, with the signed terminal terms, on the actual four-packet word boundary. | `FourNative.four_packet_bend` | 1894 (lem:fourbend) |
| Theorem 5D.1 | Positive compression on the whole space supported by an arbitrary marked subspace of dimension at most two, and the four-quadratic PSD matrix consequence. | `VerifiedPaper.plane_compression`, `VerifiedPaper.four_quadratic` | 1947 (thm:fourquad) |
| Lemma 6A.3 | Balanced opening with the two crossing pairings, proper caps and terminal terms. | `BalancedAssembly.opening`, `BalancedEvaluation.opening` | 2155 |
| Lemma 6B.1 | Last-cap coefficients and the individual trace-cup remainders on the two independently marked subspaces. | `BalancedLast.subspace_last_cap_weight` | 2175 |
| Lemma 6B.3 | Positivity of each supported balanced compression for thickness at least four, followed by the four-block matrix inequality. | `BalancedLast.subspace_marked_decomposition`, `BalancedLast.subspace_compression_psd`, `BalancedLast.marcus_thick` | 2220 (cor:fourthick) |
| Lemma 6C.1 | Signed gluing identity at every positive real parameter. | `BalancedSigned.signed_gluing` | 2278 |
| Theorem 6C.3 | Four cubic packets in every Gram dimension. Includes the signed square certificate and its PSD matrix consequence. | `BalancedCubic.cubic_certificate_all_dimensions`, `BalancedCubicMarcus.marcus` | 2306 (thm:fourcubic) |
| Lemma 7A.1 | Pair lower bound and the actual residual halfweb Gram factor on arbitrary symmetric second inputs, including its polarized form. | `PairResidual.full_caps_residual_squares`, `PairResidual.full_caps_residual_operator` | 2360 (lem:threshold-pair) |
| Lemma 7B.3 | Fine matching bound on matrix packets. The averaged identity retains the positive cut remainder. | `MatchingFineSquares.average_identity`, `MatchingFineSquares.unit_identity` | 2444 |
| Lemma 7B.5 | Packet peel identity, including its exact exit-square remainder and the average over the marked packet. | `MatchingCoarse.peel_identity`, `MatchingCoarse.averaged_peel_identity` | 2485 |
| Lemma 7B.7 | Matching-moment upper bound for the Gram permanent, with the stated deletion recurrence for its coefficients. | `MatchingUpper.permanent_le_upper`, `Threshold.pathCoeff` | 2498 |
| Theorem 7C.1 | The general matrix threshold follows both from the earlier integer-weight comparison and from the manuscript’s Jacobi spectrum and Maclaurin estimate. | `MatchingThreshold.marcus_threshold`, `PathSpectrum.spectral_threshold`, `PaperCertificate.spectral_threshold` | 2511 (thm:threshold) |
| Lemma 7D.1 | Parameterized four-face trade, including the reflected-square difference for all positive parameters. | `FourTrade.gram_trade`, `FourTradeSquares.gram_identity` | 2558 (lem:th-fourtrade) |
| Lemma 7D.3 | The tridiagonal PSD condition gives the claimed bound on every PSD block matrix. Pivot elimination and parameter trades give the signed square certificate on unit packets. | `PivotCertificate.marcus`, `PivotCertificate.unit_identity`, `TradePivots.trade_parameter` | 2569 (prop:th-matrix) |
| Lemma 7E.1 | Unordered two-step path bound, with incident exterior squares and opposite-edge reflected squares. | `TwoStepSquares.unordered_path_squares` | 2618 (lem:th-path) |
| Theorem 8A.1 | Five matrix packets of thickness at least three in every Gram dimension. The five-packet expansion has its own exact certificate. | `FiveFullCertificate.unit_identity`, `FiveFullCertificate.marcus_five` | 2634 (thm:five) |
| Lemma 8A.5 | Positive free-cable form and the full test with explicit proper-cut remainders. The uniform coefficient is 41/20. | `FiveProjection.remainder_posSemidef`, `FiveFreeResidual.testing_free_cable_squares`, `FiveFreeCoefficient.uniform_eq_iff` | 2714 (lem:five-projection) |
| Lemma 8B.3 | Reflected Gram trace for arbitrary admissible parameters and the plain and spectator-weighted averages. | `FiveMixedSquares.physical_trace`, `FiveMixedAverageSquares.plain_squares`, `FiveMixedAverageSquares.weighted_squares` | 2806 (lem:five-mixed) |
| Lemma 8C.1 | Both long-cycle inequalities with the squared differences retained. | `FiveScalarSquares.long_cycle_squares` | 2844 (lem:five-long) |
| Lemma 9A.2 | Five actual plane quadratics give a negative fifth marked closure. The witness is evaluated using the whole clasps. | `Negative.witness_factors`, `MarkedWitness.negative_fifth_full_clasps` | 2995 |
| Lemma AA.1 | Exact three- and four-subset exit sums with the printed coefficients and the individual weighted remainders. | `RawTripleFaces.triple_faces`, `RawTripleFaces.quadruple_faces` | 3024 |
| Lemma AA.3 | The physical four-face slack summed once per actual face and disjoint matching, including its recurrence, boundary values and nonnegative remainder. | `RawFaceCertificate.raw_identity`, `RawFaceCertificate.raw_bound`, `FaceCounts.coeff_succ` | 3064 |
| Lemma AB.1 | Both signs of the unnormalized odd-cycle cut, with actual matching masses and oriented cycles, including the smallest permitted label set. | `RawCycleSquares.odd_cycle_squares`, `RawCycleSquares.odd_cycle_real` | 3098 |
| Lemma AC.1 | Both signs on each cycle type. Local reflected energies multiply over disjoint assignments, with the parity factor, and the class-size sum yields the matrix criterion. | `PieceProductSquares.product_squares`, `PieceProductSquares.class_squares`, `DisjointCycleCertificate.certificate`, `DisjointCycleCertificate.marcus` | 3153 |
| Lemma BA.3 | Occupation coefficient for a routed cap and the complex Gram seam with its occupation norm factors. | `OccupationCoefficient.routed_entry`, `OccupationRouting.operator_split`, `OccupationRouting.complex_seam` | 3258 (lem:cert-seam) |
| Lemma BB.1 | Forced-edge factorization, polynomial extraction, and the marked readout on the quadratic packets used in this appendix. | `MarkedEdges.quadratic_readout`, `ForcedQuadratics.forced_weight`, `ForcedWitness.evaluate_eq`, `RoutingFibres.quadratic_polynomial` | 3300 (lem:cert-mark) |

## Worked examples

The declarations below evaluate the examples on the specified packets, routings or numerical coefficients. Diagram layouts and adjoining explanatory text are represented through the corresponding algebraic expressions.

| Printed example | Coverage | Lean entry points | TeX source |
|---|---|---|---|
| 1A.2 | Direct 24 and 8 permanent values, with the gap 16 counted by permutations which split both packets. | `OpeningExamples.all_ones_example`, `OpeningExamples.whole_split_counts`, `OpeningExamples.whole_permanent_and_gap` | 186 (ex:style-matchings) |
| 1B.3 | Direct complex matching term, cap matrix, squared norm 5/2 and gap 10. | `ComplexCapExample.matching_term`, `ComplexCapExample.single_cap`, `ComplexCapExample.permanent_gap` | 324 (ex:style-complex) |
| 2A.3 | Direct 2+1 fork on the clasped word with two identical letters, with weights 1/3 and 2/3. | `OpeningExamples.fork_two_one` | 654 (e:oneofthem) |
| 2C.4 | Direct interchange on alternating tensors and positive cap–cup after bending. | `IntroExamples.alternating_ne_zero`, `IntroExamples.interchange_alternating`, `IntroExamples.bent_interchange_psd` | 740 |
| 2C.9 | Direct two- and three-strand bent expansions. | `IntroExamples.two_strands`, `IntroExamples.three_strands` | 777 |
| 2F.3 | Direct nontrivial four-strand cut values and total gap 14. | `FourAtomExample.proper_values`, `FourAtomExample.gap_fourteen` | 889 |
| 3A.4 | Direct three-quadratic opening, including the surviving upright term. | `IntroExamples.three_quadratic`, `IntroExamples.upright_two` | 1197 |
| 3B.4 | Direct evaluation of the four terms on the indicated unaveraged boundary, and their identity after relabeling. | `MarkedBoundaryExample.drawings`, `MarkedBoundaryExample.fixed_boundary`, `MarkedBoundaryExample.averaged` | 1236 |
| 3D.4 | Direct surviving terms, zero perpendicular part, normalized gap 84 and raw permanents 720 and 48. | `ThreeOnesExample.physical_terms`, `ThreeOnesExample.raw_permanents` | 1432 |
| 4A.1 | Direct one-strand bubble, crossed gluing and the behavior of reflected images on the marked line and its orthogonal complement. | `SupportRouteExamples.supported_bubble`, `SupportRouteExamples.crossed_gluing`, `SupportRouteExamples.reflected_agree`, `SupportRouteExamples.perpendicular_rows` | 1531 (ex:inter-thin) |
| 4B.3 | Direct three-placement expansion, the single surviving term and the final clasp factor 1/3. | `TwoMarkedExample.three_placements`, `TwoMarkedExample.sole_survivor`, `TwoMarkedExample.adapted_wire`, `TwoMarkedExample.subspace_example` | 1640 (ex:inter-two-marks) |
| 5A.2 | Direct Gram matrix and the single- and joint-projection energies 1/2 and 2/3. | `TwoCapExample.gram`, `TwoCapExample.separate_energy`, `TwoCapExample.joint_energy` | 1698 |
| 6B.4 | Direct cubic shortfall with single-edge budget 9 and coherent energy 16. | `BalancedLastExample.cubic_shortfall` | 2233 |
| 7A.2 | Direct middle matrix, trace, squared norm and equality on the orthonormal pair. | `PairOrthonormalExample.middle_trace`, `PairOrthonormalExample.middle_energy`, `PairOrthonormalExample.equality_four` | 2390 |
| 7B.2 | Direct four-label evaluations of the one- and two-matching moments. | `CountingExamples.four_matchings` | 2419 (ex:th-matchings) |
| 7C.2 | Four- and five-packet threshold comparison and the four-label coefficient polynomial. | `CountingExamples.four_path_coefficients`, `Threshold.five_coefficients` | 2550 |
| 7D.4 | Direct exact tridiagonal pivots, PSD certificate and six-block consequence. | `TradePivots.six_four`, `Threshold.tradeMatrix_six_four_psd`, `RefinedThreshold.six_four` | 2578 |
| 8A.2 | Direct cap energies of the orthogonal cubic and its disjoint pair cuts. | `FiveCubicExample.cut_energy`, `FiveCubicExample.disjoint_pairs`, `FiveCubicExample.coarse_five` | 2638 |
| 8B.2 | Direct unit Gram constructions with opposite signed triangle terms. | `FiveTriangleExample.triangle_sign` | 2799 |
| 9A.1 | Two marked ends and the five coefficients of the pictured routing. | `CountingExamples.whole_edges`, `CountingExamples.five_marks` | 2967 |
| AC.3 | Direct polynomial for a triangle, a transposition and an allocated fixed point, and class size 120. | `SixCycleExample.polynomial`, `SixCycleExample.class_card` | 3178 |
| AC.4 | Exact ten-label coefficient table and resulting thickness range. | `CycleCoefficients.ten_coefficients`, `TenEndpoint.marcus_ten` | 3201 |
| BA.2 | Direct evaluation of the reflected vector, its squared norm 1/2 and the glued seam value 1/2. | `SupportRouteExamples.reflected_seam`, `SupportRouteExamples.seam_energy`, `SupportRouteExamples.glued_seam` | 3223 (ex:cert-half) |
| BB.2 | Direct rational fine and coarse closures, all five marks, their mean and agreement with the forced-edge calculation. | `Negative.all_marked_values`, `Negative.mean_is_defect`, `ForcedWitness.witness_eq_transfer` | 3341 |

## Reading the result

The negative open-bend observation immediately after Example 3A.4 is also checked. The witness has eigenvalue −2, is nonzero for thickness at least two, and annihilates the fine cuts. See `NegativeOpenBend.eigenvector`, `NegativeOpenBend.nonzero` and `NegativeOpenBend.fine_cuts`.

The manuscript's proof of Lemma 5B.1 moves from an average over three packet labels to one over four. In TeX line 1857, the equality after that second average is `[B]₄ = [X₃]₄`. The proof of `FourTarget.four_average_actual` uses the averaged equality and obtains the printed conclusion. This correction affects the intermediate sentence.

The coverage above concerns numbered mathematical results and examples. The Lean kernel checks proof terms in the stated models. Correspondence between a drawing in the PDF and its chosen strand order, normalization, adjoint or matrix definition is a mathematical interpretation recorded by the declaration, its definitions and the surrounding module.
