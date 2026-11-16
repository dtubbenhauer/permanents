# Positivity in symmetric webs and block permanents

The current checkpoint is [Stage 40](STAGE_40.md). The [manuscript index](MANUSCRIPT_INDEX.md) lists the printed results and examples in PDF order. Earlier checkpoint reports and the [historical proof map](PROOF_MAP.md) are included.

Lean companion to the supplied 16 November 2026 draft. `BlockPermanents.PaperCertificate.manuscript` assembles the two-, three-, four- and five-packet proofs and the spectral proof of Theorem 7C.1 to prove Theorem 1A.1 for arbitrary complex positive semidefinite inputs in the stated parameter range, including singular matrices. `SchurNormalization.homogeneousSchur` proves the symmetric-web relation used in the argument for all ambient dimensions and both packet sizes. Use [PaperCertificate.lean](BlockPermanents/PaperCertificate.lean) for the main theorem and its logarithmic consequence.

| Number of packets | Verified thickness | Entry point within BlockPermanents |
|---|---|---|
| One | Every positive k | `one_packet` |
| Any positive m | k = 1 | `thickness_one` |
| Two | Every positive k | `marcus_two`, `two_block_squares` |
| Three | Every positive k | `ThreePlane.marcus_three` |
| Four | Every positive k | `BalancedLast.marcus_four` combines the thin, quadratic, signed cubic and supported thick proofs |
| Five | k ≥ 3 | `FiveFullCertificate.marcus_five` |
| Any m ≥ 2 | 6⌊m/2⌋(2ᵏ−1) ≥ m(m−1)(2m−1) | `PaperCertificate.spectral_threshold` |
| Any m ≥ 2 | k ≥ 2 log₂ m | `PaperCertificate.logarithmic` |
| Six and ten | k ≥ 4 and k ≥ 5, respectively | `TenEndpoint.marcus_six`, `TenEndpoint.marcus_ten` |

The refined sufficient condition involving a tridiagonal matrix is proved in `PivotCertificate.marcus` using the actual elimination pivots. The disjoint-cycle sufficient condition is `DisjointCycleCertificate.marcus`. See [PROOF_MAP.md](PROOF_MAP.md) for the distinction between a matrix endpoint and an independent diagram identity or proof in the manuscript. [ASSUMPTIONS.md](ASSUMPTIONS.md) describes the combinatorial proof of the homogeneous Schur relation and its use in the matrix endpoints.

## Reproduce

With elan and Git installed, run these commands in this directory.

```sh
lake exe cache get
sh verify.sh
```

The first command fetches mathlib's compiled dependencies. The second builds the project and audits all its public theorem declarations. Lean and mathlib are pinned to v4.19.0. The mathlib commit is `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the lockfile pins its dependencies.

## Reading the proofs

For Lemma 4B.2, `RoutedFamilyProjection.family_gram` computes the block Gram matrix of the routed caps and `RoutedSubspaceProjection.for_subspace` gives their orthogonal projector for an arbitrary marked subspace. The definition uses the inverse on each sector’s range and handles singular blocks.

For Lemma AA.3, `RawFaceCertificate.raw_identity` sums over actual four-sets and spectator matchings with the printed coefficient. `PathSpectrum.spectral_threshold` computes the general matching coefficient bound from the spectrum of the path matrix. For Lemma AC.1, `DisjointCycleCertificate.matrix_gap` separates the signed-cycle squares, the positive cuts of the fine clasp, and the coefficient difference.

For Section 6, `BalancedLast.subspace_last_cap_weight` gives the four-border sum of squares in Lemma 6B.1. `BalancedLast.subspace_compression_psd` proves positivity of the marked operator in Lemma 6B.3 for two independent marked planes. `BalancedLast.marcus_thick` averages the three balanced bends on the original four packets. For Theorem 6C.3, `BalancedCubic.cubic_certificate` gives the full signed formula with coefficient 37/4 and `BalancedCubicMarcus.marcus` gives the original cubic matrix inequality.

For Theorem 3D.2, `ThreePlane.subspace_decomposition` proves the five-term halfweb identity on an arbitrary marked subspace. `ThreePlane.symmetricBoundary_range` identifies the whole intrinsic tensor product, `ThreePlane.intrinsic_compression_psd` tests any finite family of supported columns, and `ThreePlane.marcus_three` passes from this decomposition to the three-block permanent inequality.

For Lemma 7A.1, `PairResidual.full_caps_residual_squares` expresses the gap using the individual trace-cup complements in the paper. `PairResidual.full_caps_residual_operator` gives the complete matrix equality on a family of symmetric second inputs, including the off-diagonal entries. The equality criterion is `PairResidual.full_caps_eq_iff`.

- For (3,2), begin with `ThreeQuadratic.lean`. The corrected six-strand operator is nonnegative on each marked product. A finite coefficient check and the full symmetrizer identify its mean with the Gram-permanent difference.
- For all m, `MatchingFine` proves a lower bound by disjoint pairs. `MatchingCoarse` retains the full squared differences of exits, and `MatchingUpper` proves the coarse upper bound by induction. `MatchingThreshold` compares the two expressions and passes to PSD matrices.
- For Lemma 7E.1, `TwoStepSquares.unordered_path_squares` sums the exterior and uncrossing squares over unordered endpoint pairs. For Lemma AB.1, `RawCycleSquares.odd_cycle_squares` gives the signed, unnormalized cycle formula with the exact factorial weights and includes the case of no spare labels.
- For five packets, `FiveFullCertificate.unit_identity` gives the exact sum on unit matrix packets. `FiveFullCertificate.marcus_five` deduces the original inequality for all complex PSD matrices and all k ≥ 3. `FiveFreeCoefficient.uniform_eq_iff` identifies the unique minimum of the free-cable coefficient.
- For the negative mark in Section 9, `MarkedWitness` and `MarkedAverage` evaluate the actual polarized complex closures at the stated factors. The fifth mark is −565839/2000.

For (4,2), `FourMatrix.marked_cutForm` identifies the genuine marked operator on normalized packets with the signed proper- and full-cap form. `FourRestricted.matrix_of_supported` adapts coordinates separately for each mark and averages to the original permanent difference. This includes singular matrices and linearly dependent packet columns.
