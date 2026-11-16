# Stage 9 — Positive semidefinite compression on a rotated support

Start with at most two marked coordinates in dimension d and apply an arbitrary rectangular ambient isometry to the four packets, with its conjugate on the marked foot. The quadratic bent transfer is nonnegative on the entire resulting span. For any finite matrix of columns in that span, its compression is positive semidefinite, including when the columns are dependent. This uses the three homogeneous Schur identities in dimension d at (2,2), (4,2) and (6,2).

The declarations checked individually in this stage are

- `BlockPermanents.FourCovariance.rotatedSupport_eq`
- `BlockPermanents.FourCovariance.rotated_nonnegative`
- `BlockPermanents.FourCovariance.rotated_compression_psd`
