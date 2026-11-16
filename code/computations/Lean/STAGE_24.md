# Stage 24 — Compressing the original partially transposed transfer

A rectangular map V at the marked foot changes to its entrywise conjugate after bending. Lean proves the compression identity for the original three-packet transfer Q₃ for arbitrary V. It also places the ordinary and marked symmetric clasps on the three boundary maps and identifies their compression of the partial transpose Q₃^Γ with the internally clasped formula used to open the halfwebs. The identities are equalities of matrices on the whole boundary, with no Schur or isometry hypothesis.

The range of the resulting boundary matrix is exactly (Symᵏ V)⊗² ⊗ (Symᵏ S)* for an arbitrary subspace S. The proof starts with the range of a rectangular tensor product, identifies the two ordinary symmetric factors, and identifies the conjugate marked symmetric power. This covers arbitrary linear combinations, including entangled inputs.

The residual projector fixes exactly the kernel of the thin cap. In the example following Lemma 3D.1 with S = V = ℂ², the actual two branches send E₁₁ to I/2 and diag(1/2,−1/2). Their squared norms are both 1/2.

The declarations checked individually in this stage are

- `BlockPermanents.ThreePlane.corrected_pullback`
- `BlockPermanents.ThreePlane.original_pullback`
- `BlockPermanents.ThreePlane.bare_compression`
- `BlockPermanents.ThreePlane.tensor_range`
- `BlockPermanents.ThreePlane.bent_tensor_range`
- `BlockPermanents.ThreePlane.symmetricBoundary_range`
- `BlockPermanents.ThreePlane.perpendicular_closes_to_zero`
- `BlockPermanents.ThreePlane.perpendicular_fixes_iff`
- `BlockPermanents.ThreePlane.Example.cup_e11`
- `BlockPermanents.ThreePlane.Example.perpendicular_e11`
- `BlockPermanents.ThreePlane.Example.e11_energies`
