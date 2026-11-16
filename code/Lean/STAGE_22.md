# Stage 22 — The symmetric marked packet on a subspace

For every rectangular linear map E, applying E in each marked slot commutes with the symmetric clasp. Freezing the other k−1 letters of a supported k-packet leaves a single vector in the range of E. For a genuine complex subspace S the orthonormal basis columns give such an isometry, with range exactly S. Lean identifies the image of its symmetrized k-fold tensor power with the span of all normalized k-atom packets whose atoms lie in S. This identifies the whole marked factor Symᵏ S, including linear combinations of packets.

The declarations checked individually in this stage are

- `BlockPermanents.ThreePlane.clasp_power`
- `BlockPermanents.ThreePlane.power_symmetric`
- `BlockPermanents.ThreePlane.power_slice`
- `BlockPermanents.ThreePlane.basis_isometry`
- `BlockPermanents.ThreePlane.basis_range`
- `BlockPermanents.ThreePlane.symmetricPower_range`
