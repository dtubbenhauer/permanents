# Stage 35 — The five-packet square identity and Theorem 8A.1

The normalized five-packet permanent difference equals the sum of the straight and proper cuts, the free-cable and scalar test squares, the two mixed exit sums with their assignment multiplicities, the three positive moment terms and the four- and five-cycle squares. The free-cable coefficient uses every positive cut and has minimum 41/20 for k ≥ 3, attained only at k = 3. In Example 8B.2 two explicit real cubic configurations have identical pair squares and opposite signed triangle terms. Positivity of the full identity proves Theorem 8A.1 on the original complex PSD matrix, including singular inputs. Example 8A.2 evaluates the orthogonal cubic pair to 8, two disjoint pairs with a straight fifth packet to 64, and the coarse closure to 120.

The declarations checked individually in this stage are

- `BlockPermanents.FiveResidualGram.remainder_gram`
- `BlockPermanents.FiveResidualGram.rows_gram`
- `BlockPermanents.FiveMixedSquares.test_gram`
- `BlockPermanents.FiveMixedSquares.mixed_gram`
- `BlockPermanents.FiveMixedSquares.physical_trace`
- `BlockPermanents.FiveMixedSquares.physical_trace_lower`
- `BlockPermanents.FiveMixedAverageSquares.plain_squares`
- `BlockPermanents.FiveMixedAverageSquares.weighted_squares`
- `BlockPermanents.FiveMixedAverageSquares.exits_nonneg`
- `BlockPermanents.FiveFreeCoefficient.closed_form`
- `BlockPermanents.FiveFreeCoefficient.strictMono_coefficient`
- `BlockPermanents.FiveFreeCoefficient.cubic`
- `BlockPermanents.FiveFreeCoefficient.uniform_eq_iff`
- `BlockPermanents.FiveFreeResidual.long_resolution`
- `BlockPermanents.FiveFreeResidual.full_test_squares`
- `BlockPermanents.FiveFreeResidual.testing_exact`
- `BlockPermanents.FiveFreeResidual.testing_free_cable_squares`
- `BlockPermanents.FiveFreeResidual.tripleRemainder_nonneg`
- `BlockPermanents.FiveOuterSquares.outer_squares`
- `BlockPermanents.FiveOuterSquares.assignmentRemainder_nonneg`
- `BlockPermanents.FiveScalarSquares.scalar_resolution`
- `BlockPermanents.FiveScalarSquares.long_cycle_squares`
- `BlockPermanents.FiveScalarSquares.coarse_difference`
- `BlockPermanents.FiveScalarSquares.packet_tests`
- `BlockPermanents.FiveScalarSquares.testSquares_nonneg`
- `BlockPermanents.FiveTriangleExample.triangle_trace`
- `BlockPermanents.FiveTriangleExample.thin_gram`
- `BlockPermanents.FiveTriangleExample.thin_minors`
- `BlockPermanents.FiveTriangleExample.thin_determinants`
- `BlockPermanents.FiveTriangleExample.packet_units`
- `BlockPermanents.FiveTriangleExample.triangle_sign`
- `BlockPermanents.FiveFullCertificate.unit_identity`
- `BlockPermanents.FiveFullCertificate.unit_five`
- `BlockPermanents.FiveFullCertificate.marcus_five`
- `BlockPermanents.FiveCubicExample.survivor_gram`
- `BlockPermanents.FiveCubicExample.one_cap`
- `BlockPermanents.FiveCubicExample.cut_energy`
- `BlockPermanents.FiveCubicExample.pair_cuts`
- `BlockPermanents.FiveCubicExample.disjoint_pairs`
- `BlockPermanents.FiveCubicExample.coarse_five`
- `BlockPermanents.FiveCubicExample.one_two_split`
