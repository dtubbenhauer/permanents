# Stage 30 — Last-cap weights and the four-packet proofs of Section 6

## The balanced cut

For two independently chosen k-planes, Lemma 6B.1 supplies L/2 times each of the four edge energies and L times each of the two completed-pairing energies. Here L is the sum of choose(k,r)² / choose(2k−r−1,k−r) over 1 ≤ r < k. The remainder consists of the four trace-cup complements and all interior reflected halves in each crossing pairing. The identity holds on arbitrary supported tensors, including entangled states. The turned slices are conjugated upon bending.

For k ≥ 4, the marked quadratic form is the sum of the fine cuts, both border remainders, the six differences of single-edge exits, the difference of the two double caps, and the unused nonnegative diagonals. The complex compression is positive semidefinite on every finite family of supported tensors. On four identical unit packets at k = 3, the available single-edge diagonal is 9 and the sum of the routes has energy 16.

## Upright averaging and matrix endpoint

The three balanced marked operators sum to three times the original defect on products of symmetric packets, at every output coordinate. The proof tracks the internal packet clasps and the coordinate rotation of the actual operators. On packets of Gram atoms the defect is the full Gram permanent minus the permanent of the packet Gram matrix. Via the positive supported bends, this gives a direct proof of the four-block matrix inequality of Lemma 6B.3 in every thickness k ≥ 4.

## The cubic certificate

Theorem 6C.3 is checked via the signed three-division formula with coefficient 37/4. The three fine remainders are the six positive-order cuts of the grouped six-atom packets in each division. On a fixed supporting three-plane, the opposed-edge term τ is nine times the sum of the energies of the two perpendicular proper cuts. Its total is invariant under reversal of the bend. The exterior part is a sum of squared two-by-two minors. The signed survivor term, the t = 1/2 square and the difference of the two full caps appear explicitly. The matrix consequence includes singular PSD inputs. A version of the identity valid in the original Gram dimension also works in dimensions one and two by using the actual survivor spans and retaining the extra full-cap energies.

## Next manuscript target

Lemma 7E.1, “A two-step path”, asserts a global decomposition of its difference into reflected squares. TwoStep.two_step_path proves the bound and TwoStep.path_square gives the local four-cycle square. The next step is to assemble those squares with the adjacent-edge exterior-product squares, retaining their exact multiplicities over all middle and endpoint indices.

The declarations checked individually in this stage are

- `BlockPermanents.BalancedLast.space_symmetricPower`
- `BlockPermanents.BalancedLast.dual_space_iff`
- `BlockPermanents.BalancedLast.supported_iff`
- `BlockPermanents.BalancedLast.exists_packet_frame`
- `BlockPermanents.BalancedLast.borderRemainder_nonneg`
- `BlockPermanents.BalancedLast.pairing_decomposition`
- `BlockPermanents.BalancedLast.subspace_last_cap_weight`
- `BlockPermanents.BalancedLastDifferences.completed_routes`
- `BlockPermanents.BalancedLast.subspace_marked_decomposition`
- `BlockPermanents.BalancedLast.subspace_compression_psd`
- `BlockPermanents.BalancedLastExample.cubic_shortfall`
- `BlockPermanents.BalancedCubicFine.fine_remainder`
- `BlockPermanents.BalancedCubicTau.tau_squares`
- `BlockPermanents.BalancedCubicTau.tau_swap`
- `BlockPermanents.BalancedCubicTau.tau_packet_spans`
- `BlockPermanents.BalancedCubicTau.correction_nonneg`
- `BlockPermanents.BalancedCubicExterior.crossing_exterior`
- `BlockPermanents.BalancedCubicExterior.signedSquares_exterior`
- `BlockPermanents.BalancedCubic.reverse_edge`
- `BlockPermanents.BalancedCubic.cubic_certificate`
- `BlockPermanents.BalancedCubic.cubic_certificate_all_dimensions`
- `BlockPermanents.BalancedCubicMarcus.marcus`
- `BlockPermanents.BalancedDivision.three_division_average`
- `BlockPermanents.BalancedDivision.defect_gram`
- `BlockPermanents.BalancedLast.defect_nonnegative`
- `BlockPermanents.BalancedLast.marcus_thick`
- `BlockPermanents.BalancedLast.marcus_four`
