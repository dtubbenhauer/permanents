# Stage 15 — The homogeneous Schur relation and the main matrix theorem

The classical homogeneous exchange is now proved directly on the symmetric word matrices in every ambient dimension for every pair of packet sizes. The proof applies the matrix criterion of Stage 11 to the unconditional permutation average of Stage 14. This discharges the literature input to Theorem 1A.1.

For m,k ≥ 1, the main matrix theorem gives per(A) ≥ per(G) for arbitrary complex positive semidefinite A when m ≤ 4, when m = 5 and k ≥ 3, or when m ≥ 2 and 6⌊m/2⌋(2ᵏ−1) ≥ m(m−1)(2m−1). Here G consists of the permanents of the k × k blocks of A. The difference is proved to be a nonnegative real number. The logarithmic sufficient condition k ≥ 2 log₂ m for m ≥ 2 also has a direct public declaration. The universal switch proof also applies to the conditional diagram identities saved in earlier stages.

Both parts of Theorem 5D.1 have direct declarations with the switches discharged. The compression of the partial transpose is positive semidefinite on the full tensor space over any complex marked subspace of dimension at most two. The four-quadratic matrix inequality follows by cutting and averaging in Gram dimension eight.

## Remaining diagrammatic work

One bounded next target is Lemma 7A.1: identify the residual halfweb in each actual packet cut with the orthogonal trace-cup complement of its cut matrix. The generic identity is in SupportCup.resolution, and PairBound already identifies the cut matrix, its support and its trace. The current positive-square factorization in PairSquares.full_caps_squares gives existence of factors. A second target is the arbitrary-subspace version of the reflected-halfweb equation in Theorem 3D.2 at general thickness; the current three-packet version uses coordinate supports. These are intermediate manuscript assertions beyond the main matrix inequality.

The declarations checked individually in this stage are

- `BlockPermanents.SchurNormalization.homogeneousSchur`
- `BlockPermanents.VerifiedPaper.manuscript`
- `BlockPermanents.VerifiedPaper.logarithmic`
- `BlockPermanents.VerifiedPaper.plane_compression`
- `BlockPermanents.VerifiedPaper.four_quadratic`
