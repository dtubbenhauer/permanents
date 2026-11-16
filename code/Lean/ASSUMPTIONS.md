# Mathematical inputs and computational trust

## The symmetric-web relation

`SchurNormalization.HomogeneousSchur d p q` is the classical homogeneous dumbbell-crossing relation on two packets. It is the equal incoming and outgoing boundary specialization of Latifi–Tubbenhauer, Definition 5.2, equation (5.3), at quantum parameter one. The constraint on the two exchanged thicknesses then forces them equal. The specialization in the symmetric-tensor representation is proved in `SchurNormalization.homogeneousSchur` for every d,p,q. The two packet sizes determine a subgroup of slot permutations. Its double cosets are classified by their number of crossing slots, and counting each class gives the exchange coefficient. [Latifi–Tubbenhauer, arXiv v2, pp. 30–31](https://arxiv.org/pdf/2112.12688v2#page=31).

The basis of a tensor power consists of all words in the finite alphabet. The square fork uses the full permutation average on the input slots. The hollow fork uses the same permutation sum divided by the two output factorials. `homogeneousSchur_implies_unbent` proves the three binomial normalization factors. `Bend.bend_exchange` proves the operator identity converting each exchange into a reflected contraction. `Bridges.two_block_gram_gap` applies the resulting formula to the actual square-root-factorial-normalized matrix packets.

## The straight principal cut

`ThreeFine.LiebPrincipalBlocks I J` gives the classical principal-block bound on an arbitrary complex PSD matrix indexed by the disjoint union of two finite sets. It bounds the product of the two diagonal-block permanents by the permanent of the full matrix. The explicit literature-input route to `ThreeBlocks.marcus_three_of_lieb` uses this result once for each choice of spectator, together with the homogeneous Schur relation on the two equal-sized packets. The improvement by the factor 2^k−1, the three-packet Gram identity and the conclusion for the matrix of block permanents are proved in Lean. [Lieb](https://doi.org/10.1512/iumj.1967.16.16008) and [Djoković](https://doi.org/10.1017/S0017089500000525).

The principal three-block endpoint `marcus_three` also proves this straight cut. `StraightCut.principal_blocks` retains the zero-cap term in the rectangular Schur expansion, reindexes the two sets of raw columns, and passes through Gram factorization. Thus only two instances of the same homogeneous relation enter the public proof, on (k,k) and (2k,k) in dimension 3k.

## Operator hypotheses and domains

The general packet-transfer identity quantifies over an operator B satisfying two-sided clasp absorption. Lean constructs the average of simultaneous relabelings of its upper and lower ends. The theorem also has a concrete instance for the action on tensor coordinates. The four-packet transfer takes two-sided support on the indicated clasps and invariance of the four-packet defect. Its algebraic conclusions apply to every operator satisfying those structural hypotheses.

The trace and support theorems fix the supported subspace before resolving the cut. The two- and three-block matrix inequalities use columns from a Gram factorization. Mathlib supplies that factorization for every PSD matrix. A product across the chosen bend is explicit in the bending evaluation.

## Inputs of the matrix endpoints

The intermediate arbitrary-m threshold and five-packet endpoint accept `∀ p q, HomogeneousSchur d p q` with `d=m*k`. Every invocation is at a specific merge size and the conclusion is about the original complex PSD matrix. The five-packet theorem also uses a Gram factorization and finite-dimensional orthogonal projection facts from mathlib. The isolated three-quadratic endpoint accepts no literature hypothesis. Its finite table certifies an identity of thin-wire permutations. For four quadratics, the only hypotheses of `FourMatrix.marcus_four_quadratic` are the three cited switches at (2,2), (4,2), and (6,2) in arbitrary ambient dimension. The factorization of the marked operator, the five last-cap values, the sector projection inequalities, and the return to the permanent gap are all proved. The universal Schur proof supplies every one of these switches. `VerifiedPaper.manuscript`, `VerifiedPaper.logarithmic`, `VerifiedPaper.plane_compression`, and `VerifiedPaper.four_quadratic` include that proof directly. The condition on the tridiagonal matrix in `RefinedThreshold.marcus` is the stated sufficient numerical condition of that proposition. Its six-block example has its own checked PSD certificate.

## Kernel audit

The project has no new axiom declarations or unfinished proof terms. Literature inputs are arguments appearing in the theorem types. `Audit.lean` traverses the transitive dependencies of all public project theorems and fails on any axiom outside `propext`, `Classical.choice` and `Quot.sound`. The Section 9 rational computations use `decide +kernel`. No externally computed numerical result enters a Lean proof. The axiom audit checks the proof dependencies. The mathematical content of a literature parameter is visible in its declaration.
