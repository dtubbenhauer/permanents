# Stage 11 — Recovering the Schur relation from the permutation operator

For any dimension d and packet sizes p,q, the coefficient-one homogeneous Schur relation on word matrices is equivalent to the weighted identity on the underlying labelled permutations acting on tensors. The new implication evaluates the operator on individual basis columns and restores the two hollow-fork factors. Thus a combinatorial proof of the permutation average will supply exactly the three switches needed by the quadratic proof, as well as the switches at other thicknesses. This checkpoint proves an equivalence; existence of either side in full generality is a separate assertion.

The declarations checked individually in this stage are

- `BlockPermanents.SchurWireCriterion.homogeneous_of_unbent`
- `BlockPermanents.SchurWireCriterion.unbent_of_operator`
- `BlockPermanents.SchurWireCriterion.of_operator`
- `BlockPermanents.SchurWireCriterion.operator_iff`
