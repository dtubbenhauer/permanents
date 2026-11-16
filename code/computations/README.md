# Companion computations

These are finite calculations from earlier versions of Daniel Tubbenhauer’s work on block permanents. The web checks give small examples of the clasp and bending operations used in the paper. The three-, four- and five-packet programs examine specific certificate constructions. The Lean development has a separate build.

| Directory | Calculation | Expected result |
| --- | --- | --- |
| [web-checks](web-checks/) | Two- and three-packet identities in explicit coordinates, web reductions and small rank examples | The doubled three-packet tree evaluates to 18, and its bubble scalar is 3. |
| [three-quadratic-certificate](three-quadratic-certificate/) | An integer transport certificate for three quadratic packets in four variables | All 140 weight blocks are positive semidefinite. The largest has order 37. |
| [four-quadratic-certificate](four-quadratic-certificate/) | A dimension-six two-bend certificate for four quadratic packets | 38 rational coefficients and 43 positive semidefinite highest-weight forms, each of order at most four. |
| [five-packet-obstruction](five-packet-obstruction/) | An obstruction to certificates using positive operators and whole-packet partial transposes for five quadratic packets in dimension eight | All three representative partial transposes of the witness are positive definite, and its normalized pairing with the gap is −105532792597/155520000000. |

## Web calculations

From this directory, run the following with Python 3. NumPy and SymPy are needed for the full set. The loop also regenerates the checked-in JSON record of the closed web reductions.

```sh
python3 -m pip install numpy sympy
cd web-checks
for script in *.py; do python3 "$script" || exit 1; done
```

For a single calculation with the Python standard library, run `python3 check_opening_closure.py` from `web-checks/`. It directly enumerates the six-port closure and prints 18. The rank and general-degree scripts check the specific dimensions and degrees in their output.

## Three quadratic packets

The 21 coefficients in the [transport verifier](three-quadratic-certificate/verify.py) index the distinct ways that a permutation of six slots routes three quadratic packets. The verifier averages the transport coefficients over packet permutations and compares the result with an independently assembled Fock-space target. It then partially transposes the third packet and checks the resulting 1,000-dimensional matrix by rational elimination.

```sh
python3 -m pip install numpy
python3 three-quadratic-certificate/verify.py
```

The expected output reports 154 positive pivots and 846 zero pivots. A second check reconstructs the rational LDLᵀ factors for representatives of all twelve weight types. This calculation supplies an independent finite example for the three-packet case of the paper.

## Four quadratic packets

The certificate is an earlier proof for four quadratic packets. The current paper proves its quadratic four-packet result in Theorem 5D.1 using routed caps. The following checks replay the separate highest-weight certificate from its stored matrices. Run them from `four-quadratic-certificate/` with Python 3 and the listed packages.

```sh
python3 -m pip install numpy scipy sympy
python3 audit/check_rational38.py
python3 audit/audit_exact_one.py
python3 audit/audit_exact_balanced.py
```

The two `audit_exact` scripts test rational determinants and compare with stored numerical spectra. The one-bend subspace has dimension 37,191 and rank 8,001. The balanced subspace, counting the two mixed sectors, has dimension 194,481 and rank 58,031. The file `two_bends/rational38_d6.json` contains the exact coefficients.

To reconstruct the rational blocks from the contractions, run the original generators below in a working copy of `four-quadratic-certificate/`. They write the JSON blocks beside the scripts. Reconstruction also requires python-flint. For this release the stored-block checks above were rerun, and the FLINT reconstruction was not rerun.

```sh
python3 -m pip install -r requirements.txt
python3 two_bends/one_exact.py 6
python3 two_bends/balanced_exact.py 1 1
python3 two_bends/balanced_exact.py 1 -1
python3 two_bends/balanced_exact.py -1 -1
```

## Five quadratic packets

The three binary files encode an exact rational witness. The C++ programs rebuild its diagram multiplication tables and verify positivity and the negative pairing with integer arithmetic. This distinguishes a restriction on a proof method from a violation of the block-permanent inequality. Section 9 of the current paper studies a different negative marked closure. The full replay and an additional independent Python audit are described in the [witness guide](five-packet-obstruction/README.md).

## Sources

The web checks and their reduction record come from the verification material for *Webs and block permanents* and *Block permanents through clasps and webs*. The three-packet integer verifier collects the executable checks in Sections 3–4 of the project notebook `Permanent_three_two_blocks.ipynb`. The two-bend certificate, frozen coefficients and independent audits come from the Section 5 supplement to *Block permanents and webs*. The five-packet generators, verifier and witness files come from the five-packet obstruction supplement to *Webs and block permanents*. The stored one-bend record and its generator use the coefficient filename relative to their directory.
