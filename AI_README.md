# Reading the paper with its Lean proofs

To find the proof of a numbered result or example, look up its printed label in the manuscript index. The table gives its Lean declaration, its scope and the corresponding TeX line or label. Use the PDF for figures and the TeX source for strand order, coefficients and labels. [Clickable theorem index](ai/theorem-index.md) · [Verification scope](code/Lean/MANUSCRIPT_INDEX.md) · [PDF](paper/paper.pdf) · [TeX](paper/main.tex) · [Searchable paper](ai/paper.md)

## The main statement

`BlockPermanents.PaperCertificate.manuscript` proves Theorem 1A.1. An input is a complex positive semidefinite matrix indexed by `Fin m × Fin k`. If $G$ is the matrix of permanents of its $k$-by-$k$ blocks, `MarcusAt m k` says that `A.permanent - G.permanent` equals a nonnegative real embedded in `ℂ`. Singular inputs are included. [Definitions](code/Lean/BlockPermanents/Statement.lean) · [Proof](code/Lean/BlockPermanents/PaperCertificate.lean)

For positive integers $m,k$, the theorem covers $m\le4$, or $m=5$ and $k\ge3$, or $m\ge2$ and $m(m-1)(2m-1)\le6\lfloor m/2\rfloor(2^k-1)$. The division `m / 2` in Lean is natural-number division. `PaperCertificate.logarithmic` gives the sufficient condition $k\ge2\log_2 m$ for $m\ge2$. `BlockPermanents.thickness_one` gives equality for every packet count when $k=1$. [Main theorem and corollary](code/Lean/BlockPermanents/PaperCertificate.lean) · [Thickness-one case](code/Lean/BlockPermanents/Statement.lean)

## Following a proof

All declaration names below are relative to `BlockPermanents`.

| To inspect | Start with | What to check |
|---|---|---|
| The Schur relation | [SchurNormalization.homogeneousSchur](code/Lean/BlockPermanents/HomogeneousSchurProof.lean) | Proves the classical symmetric-word operator identity for all dimensions and packet sizes. Earlier lemmas can take that identity as an explicit argument. |
| A supported operator | [RoutedSubspaceProjection.for_subspace](code/Lean/BlockPermanents/RoutedSubspaceProjection.lean) | Gives the projection for the whole family of routed caps on an arbitrary marked subspace in Lemma 4B.2. |
| The five-packet case | [FiveFullCertificate.unit_identity and marcus_five](code/Lean/BlockPermanents/FiveFullCertificate.lean) | The square identity assumes normalized matrix packets. The matrix theorem applies to every complex PSD input at $k\ge3$. |
| The negative fifth mark | [MarkedWitness.negative_fifth_full_clasps](code/Lean/BlockPermanents/MarkedAverage.lean) | Evaluates the real part of the specified marked closure as `-565839/2000`. The five-packet quadratic matrix inequality remains open in the manuscript. |

## Reproducing a check

From the repository root, with Git and elan installed, run

```sh
cd code/Lean
lake exe cache get
sh verify.sh
```

The script checks that the umbrella module imports each project module, builds the package, and runs the transitive axiom audit. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. To see a theorem’s hypotheses directly, run the following in a Lean file in the project. [Verification script](code/Lean/verify.sh) · [Audit source](code/Lean/Audit.lean)

```lean
import BlockPermanents.PaperCertificate

#print BlockPermanents.ManuscriptTheorem
#check BlockPermanents.PaperCertificate.spectral_threshold
#print axioms BlockPermanents.PaperCertificate.manuscript
```
