# Stage 10 — Four quadratic packets on an arbitrary marked plane

The support in Theorem 5D.1 can be any complex subspace S of the finite-dimensional ambient space V with dim(S) ≤ 2. Lean constructs a unitary adapted to S and proves that the number of selected coordinates equals its dimension. The marked action on the bent boundary is the complex conjugate of the ordinary action.

The space in the theorem is (Sym² V)⊗³ ⊗ (Sym² S)*. In word coordinates its generators are an arbitrary internally symmetric ordinary triple tensored with the conjugate of a symmetrized pair of vectors in S. The proof checks both inclusions between the span of those generators and the rotated coordinate-supported space. It includes vectors entangled across the ordinary and marked factors. The equality of these spaces holds in every rank.

For rank at most two, the quadratic form is nonnegative on this whole space. For any finite matrix B with columns in the space the Hermitian matrix B† Q^Γ B is positive semidefinite. The columns can be dependent. The proof uses the homogeneous Schur identities at (2,2), (4,2) and (6,2) in the ambient dimension. These are explicit arguments to the positivity theorems.

The matrix endpoint now follows directly from this intrinsic positivity: realize the eight Gram vectors in ℂ⁸, take the span of the two atoms at each mark and average. Thus Marcus's inequality for four quadratic blocks uses just the same three Schur identities in dimension eight. The statement covers every complex positive semidefinite 8 × 8 matrix, including singular inputs.

The declarations checked individually in this stage are

- `BlockPermanents.FourPlaneBasis.exists_plane_coordinates`
- `BlockPermanents.FourCovariance.power_packet`
- `BlockPermanents.FourCovariance.supported_mem_packet_span`
- `BlockPermanents.FourPlaneCompression.planeSupport_eq_rotatedSupport`
- `BlockPermanents.FourPlaneCompression.nonnegative`
- `BlockPermanents.FourPlaneCompression.compression_psd`
- `BlockPermanents.FourPlaneCompression.marcus_four_quadratic`
