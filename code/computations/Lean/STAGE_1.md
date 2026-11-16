# Stage 1 — verification of the stopped run

This checkpoint incorporates all 239 Lean modules found when the original run stopped on 16 November 2026. All are in the default build. It adds 25 buildable modules to the 214-module recovery checkpoint. Three proof bodies needed local repairs: a complex scalar annotation, a matrix associativity step, and a reindexing of a product. The theorem statements in those files are unchanged.

`sh verify.sh` completed with the pinned Lean 4.19.0 and mathlib revision. It used the existing build cache and checked the transitive axiom dependencies of 2909 project theorem declarations. See VERIFICATION.txt for the output. The homogeneous Schur relation is an explicit mathematical input to the main matrix theorem. ASSUMPTIONS.md describes it.

## Checked in this stage

- `ThreeMarkedAverage.cyclic_gap` writes the three-packet permanent gap as the mean of the three cyclic markings for arbitrary complex input columns.
- `ZeroCap.opening` identifies the preceding defect at zero caps and splits off the proper cuts and the two signed full-cap squares. Its hypotheses are the fine and packet instances of the homogeneous Schur relation.
- `FourThickOpenings.actual_open` expands the compressed four-packet transfer for positive thickness k under the three Schur instances (k,k), (2k,k), and (3k,k).
- `FourNative.read_full` reads the terminal swap between reflected factors as a Gram square, given an upright matrix for the right factor.

## Next stage

Identify the terminal full-cap contribution in `FourThickOpenings.actual_open` with the Gram square of its specific half-map. Instantiate `FourNative.read_full` on the actual factors and discharge the reflection, uprightness, and any clasp support conditions. Check the exact coefficient against the manuscript. End that stage after the named identity and its dependency audit, with a new checkpoint. This archive does not certify every intermediate diagram in the paper.

## Additional modules since the recovery checkpoint

- BendCoordinates.lean
- CycleAllocation.lean
- CycleClasses.lean
- CycleParameters.lean
- CyclePartitionSum.lean
- CycleUnbounded.lean
- Digon.lean
- DisjointCycles.lean
- FourCompressionPSD.lean
- FourExchangeBasis.lean
- FourExchangeKernel.lean
- FourExchangeRoutes.lean
- FourNativeCap.lean
- FourNativeFull.lean
- FourNativeSurvivor.lean
- FourNativeUpright.lean
- FourThickOpenings.lean
- FourThickTransfer.lean
- FullCapWords.lean
- RoutingPacketReadout.lean
- SupportCup.lean
- TensorCoordinates.lean
- ThreeCyclicRead.lean
- ZeroCap.lean
- ZeroCapClasp.lean
