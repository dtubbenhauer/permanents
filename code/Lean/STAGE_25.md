# Stage 25 — The three-packet decomposition on an arbitrary marked subspace

Theorem 3D.2 holds on (Symᵏ V)⊗² ⊗ (Symᵏ S)* for every complex marked subspace S of dimension s with 1 ≤ s ≤ k and k ≥ 2. Lean pulls back the partial transpose of the original Q₃ along the three symmetric boundary maps. It identifies their range with the intrinsic tensor product, including arbitrary entangled inputs and mixed matrix entries. Set a = choose(2k,k) and write |Y|² = Y†Y. The exact compression is

    2 ∑_{r=1}^{k−2} choose(k,r)² |U_r|²
    + a ∑_{r=1}^{k−1} choose(2k,r) choose(k,r) |V_r|²
    + 2k² |J U_(k−1)|² + |a v − u/2|² + (2k²/s − 9/4) |u|².

The matrix equality only needs s > 0. The condition s ≤ k gives the lower bound 2k²/s − 9/4 ≥ 2k − 9/4 > 0, and Lean verifies positive semidefinite compression on every finite family of supported columns. The small proper-cut sum is empty for k = 2. The proof uses the universal Schur identity already verified in Stage 15.

For the permanent inequality, take the span of the k atoms of the marked packet in the common Gram space and average the six packet orders. If that span is zero, the packet vanishes. With k = 1 handled by the thin-packet identity, this derives Marcus’s inequality for three blocks of every positive common size directly along the route in Theorem 3D.2.

## Next manuscript target

Lemma 6B.1, “Last-cap weight”, asks for the explicit sums of squares left on the four borders of the balanced cut after extracting L/2 copies of each edge cap and L copies of each completed pairing. BalancedTrace.terminal_le, BalancedSupport.border_sum and BalancedPositive.edge_lower provide the existing estimates. The diagrammatic step still to verify is the exact trace-cup complement for the t = k−r symmetric survivors, with bubble choose(k+t−1,t), and its assembly over the borders.

The declarations checked individually in this stage are

- `BlockPermanents.ThreePlane.subspace_decomposition`
- `BlockPermanents.ThreePlane.subspace_compression_psd`
- `BlockPermanents.ThreePlane.family_lifts_iff`
- `BlockPermanents.ThreePlane.family_pullback`
- `BlockPermanents.ThreePlane.intrinsic_compression_psd`
- `BlockPermanents.ThreePlane.full_cap_weight_lower`
- `BlockPermanents.ThreePlane.proper_weights_pos`
- `BlockPermanents.ThreePlane.full_cap_weight_pos`
- `BlockPermanents.ThreePlane.packet_expectation`
- `BlockPermanents.ThreePlane.marcus_three`
