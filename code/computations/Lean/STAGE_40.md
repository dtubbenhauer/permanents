# Stage 40 — The complete manuscript index and its permanent certificates

This checkpoint completes the paper’s case-by-case assembly of Theorem 1A.1 on complex positive semidefinite matrices. The spectral proof verifies the actual weighted path determinant, the paired eigenvalues and the Maclaurin coefficient estimate. The tridiagonal proof checks each positive pivot before the last, the final nonnegative pivot and the physical permanent identity at the resulting parameters. The signed disjoint-cycle halves compose at arbitrary real positive parameters. Summing their remainders over actual classes gives the exact difference in (AC.2).

For Lemma 4B.2 the normalized occupation basis spans the symmetric output. The family of physical cap matrices determines all Gram blocks with the same route counts in every dimension. The sector pseudoinverses give the Hermitian projection onto the sum of the reflected images, also in singular sectors and in arbitrary marked subspaces. The negative open bend is verified on every orthogonal unit pair.

See [the manuscript index](MANUSCRIPT_INDEX.md) for each of the 6 numbered theorems, 42 lemmas and 24 worked examples in the supplied draft. It records the statement-level scope, the correction in the proof of Lemma 5B.1, and the finite-dimensional interpretation of the diagrams. All cited Lean entry points in its two tables are checked during the audit.

The declarations checked individually in this stage are

- `BlockPermanents.PaperCertificate.manuscript`
- `BlockPermanents.PaperCertificate.spectral_threshold`
- `BlockPermanents.PaperCertificate.logarithmic`
- `BlockPermanents.RoutedCapMatrix.apply_cap`
- `BlockPermanents.RoutedCapMatrix.apply_reflect`
- `BlockPermanents.RoutedUniform.clasped_intersection`
- `BlockPermanents.RoutedOccupationFrame.complete`
- `BlockPermanents.RoutedFamilyProjection.family_gram`
- `BlockPermanents.RoutedFamilyProjection.mem_projection_range`
- `BlockPermanents.RoutedSubspaceProjection.for_subspace`
- `BlockPermanents.RoutedSubspaceProjection.dual_range`
- `BlockPermanents.MatchingFineSquares.ordered_identity`
- `BlockPermanents.MatchingFineSquares.average_identity`
- `BlockPermanents.PathJacobi.determinant`
- `BlockPermanents.PathJacobi.trace_square`
- `BlockPermanents.PathSpectrum.paired_spectrum`
- `BlockPermanents.PathMeans.maclaurin_multiset`
- `BlockPermanents.PathSpectrum.spectral_threshold`
- `BlockPermanents.TradePivots.matrix_pivots`
- `BlockPermanents.TradePivots.degree_budget`
- `BlockPermanents.TradePivots.six_four`
- `BlockPermanents.PivotCertificate.unit_identity`
- `BlockPermanents.PivotCertificate.marcus`
- `BlockPermanents.PieceScoreProduct.score_split`
- `BlockPermanents.PieceProductSquares.product_squares`
- `BlockPermanents.PieceProductSquares.class_squares`
- `BlockPermanents.DisjointCycleCertificate.certificate`
- `BlockPermanents.DisjointCycleCertificate.matrix_gap`
- `BlockPermanents.DisjointCycleCertificate.marcus`
- `BlockPermanents.NegativeOpenTransport.orthogonal_unit_pair`
- `BlockPermanents.NegativeOpenTransport.fine_cuts`
- `BlockPermanents.FourAtomExample.middle_matrix`
- `BlockPermanents.ThreeOnesExample.raw_gap`
- `BlockPermanents.TwoCapExample.joint_energy`
- `BlockPermanents.SixCycleExample.class_estimate`
