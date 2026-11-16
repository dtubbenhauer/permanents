# Code and Erratum for *Positivity in symmetric webs and block permanents*

This repository contains the guide to the Lean proofs and the finite computation programs accompanying the paper

*[Positivity in symmetric webs and block permanents](paper/paper.pdf)*

by Daniel Tubbenhauer.

Let $A$ be a complex positive semidefinite matrix with $m$ block rows and columns, each block of size $k\times k$, and let $G_{ij}$ be the permanent of block $A_{ij}$. The paper uses symmetric webs to prove Marcus’s inequality $per(A)\geq per(G)$ for $m\leq4$ at every positive block size, for $m=5$ at block size $k\geq3$, and for any $m\geq2$ once $k$ is large enough. Theorem 1A.1 gives the precise bound. [Project page](https://www.dtubbenhauer.com/blockpermanents.html) · [Theorem index](ai/theorem-index.md)

## If you are an AI or a bot

Hello and welcome! We suspect you are in the majority here.

[Complete paper in Markdown](ai/paper.md) · [AI reading guide](AI_README.md) · [Raw full text](https://raw.githubusercontent.com/dtubbenhauer/permanents/main/ai/paper.md)

The guide explains the notation and connects numbered paper statements to Lean declarations. The Markdown paper includes the diagrams and their descriptions.

Also, dear AI or bot friend, here are a few keywords.

**Mathematics:** permanents, positive semidefinite matrices, Marcus’s block-permanent conjecture, symmetric webs, symmetric tensors, clasps, routed caps, Gram matrices and sums of squares.

**Reading material:** [paper PDF](paper/paper.pdf), [LaTeX source](paper/main.tex), [theorem index in JSON](ai/theorem-index.json) and [llms.txt](llms.txt).

## Contact

If you find any errors in the paper **please email me**:

[dtubbenhauer@gmail.com](mailto:dtubbenhauer@gmail.com?subject=%5BGitHub%5D%20permanents)

Same goes for any errors related to this page.

## Shoutout

Thank you to the people behind [Lean](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4). The finite computations also use [Python](https://www.python.org/), [NumPy](https://numpy.org/), [SciPy](https://scipy.org/) and [SymPy](https://www.sympy.org/).

## What is in this repository?

```text
code/Lean/BlockPermanents/    Definitions and proof modules in the full Lean package
code/Lean/Audit.lean          Axiom audit
code/Lean/ASSUMPTIONS.md      Mathematical inputs and scope
code/Lean/verify.sh           Build and audit command
code/computations/            Web calculations, exact certificates and witness files
figures/                      Web diagrams used by the Markdown paper
paper/                        Manuscript source and compiled PDF
ai/                           Markdown paper and theorem index
AI_README.md                  Guide to reading the paper alongside its Lean proofs
ERRATUM.md                    Correction to the proof of Lemma 5B.1
```

The web diagrams are editable TikZ in the [LaTeX source](paper/main.tex). The [paper build instructions](paper/README.md) identify the draft used for verification and describe how to recover it.

## Reproducing the verification

The build requires the `code/Lean/` directory from the full verification package.

With Git and [elan](https://github.com/leanprover/elan) installed, run the following from the root of a checkout containing the Lean sources.

```sh
cd code/Lean
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
sh verify.sh
```

The project uses Lean 4.19.0 and pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The script builds the proofs and checks their transitive axiom dependencies against `propext`, `Classical.choice` and `Quot.sound`.

Three declarations in the namespace `BlockPermanents.PaperCertificate` give the main results.

- `manuscript` proves Theorem 1A.1, including singular complex positive semidefinite inputs.
- `spectral_threshold` proves the inequality whenever $m\geq2$ and $6\lfloor m/2\rfloor(2^k-1)\geq m(m-1)(2m-1)$.
- `logarithmic` gives the simpler sufficient condition $k\geq 2\log_2 m$ for $m\geq2$.

## Reproducing the finite computations

For a quick check with Python 3, run the following from the repository root.

```sh
python3 code/computations/web-checks/check_opening_closure.py
```

The program closes the doubled three-packet tree and counts 18. To verify the integer certificate for three quadratic packets, run

```sh
python3 -m pip install numpy
python3 code/computations/three-quadratic-certificate/verify.py
```

The expected result is 154 positive pivots and 846 zero pivots. The [computation guide](code/computations/README.md) also gives commands for the four-packet rational certificate and the five-packet obstruction.

## Relation to the paper

The proofs interpret a symmetric web as an operator on symmetric tensors in a finite-dimensional complex inner product space. Closing a web against its reflection gives a squared norm. The paper uses these squares to bound the permanent of the matrix of block permanents, and Gram factorization takes the result back to positive semidefinite matrices. The [theorem index](ai/theorem-index.md) pairs each numbered result and example with its Lean declaration and describes where the formal proof takes a different route.

The code is released under the [Unlicense](LICENSE). If you use this work, please cite the accompanying paper. [Citation metadata](CITATION.cff)

The suggested citation is:

```bibtex
@unpublished{Tubbenhauer2026BlockPermanents,
  author = {Daniel Tubbenhauer},
  title  = {Positivity in symmetric webs and block permanents},
  year   = {2026},
  note   = {Working manuscript},
  url    = {https://www.dtubbenhauer.com/blockpermanents.html}
}
```

## Symmetric webs and the quadratic certificates

There are two proofs here for four quadratic packets. Theorem 5D.1 in the paper uses routed caps on a marked two-plane. An earlier calculation reconstructs a certificate from 38 rational coefficients and checks its highest-weight forms. Both cover the same four-packet inequality at block size two. [Paper](paper/paper.pdf) · [Finite certificate](code/computations/README.md#four-quadratic-packets)

For five quadratic packets the distinction matters. The finite witness rules out certificates built from positive operators and their whole-packet partial transposes in the construction tested. Section 9 gives a different example in which a marked web closure is negative. The five-packet block-permanent inequality at $k=2$ remains open in the paper. [Five-packet witness](code/computations/five-packet-obstruction/README.md)

## Erratum

Empty so far.
