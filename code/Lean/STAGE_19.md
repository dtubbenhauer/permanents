# Stage 19 — The residual halfweb as a matrix in the second input

Fix the first packet. The matrix of each residual halfweb is built by attaching that packet, applying the actual word cap, reading the surviving cable in an orthonormal basis and applying J_r. Entrywise conjugation gives a complex-linear map on the second input Z. Its value is the conjugate of J_rY_r, and its squared norm is exactly ‖J_rY_r‖². The action formula holds on every input word tensor.

For the paper's two standard orthonormal atoms in ℂ² the normalized packet is (e⊗f+f⊗e)/√2. Lean evaluates its actual one-cap matrix as I/2, with trace 1 and squared norm 1/2. The straight, single and double cuts contribute 1, 2 and 1, respectively, and the symmetric product attains 4 in the units of Lemma 7A.1.

The declarations checked individually in this stage are

- `BlockPermanents.PairResidual.residualMatrix_apply`
- `BlockPermanents.PairResidual.residualMatrix_energy`
- `BlockPermanents.PairResidualExample.middle_matrix`
- `BlockPermanents.PairResidualExample.middle_trace`
- `BlockPermanents.PairResidualExample.middle_energy`
- `BlockPermanents.PairResidualExample.cut_values`
- `BlockPermanents.PairResidualExample.equality_four`
