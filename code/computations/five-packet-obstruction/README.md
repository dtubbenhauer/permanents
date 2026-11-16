# Five quadratic packets in dimension eight

Let $K=\operatorname{Sym}^2(\mathbb C^8)$, which has dimension 36. This example studies the gap operator $X_5=113400 E_{10}-120 R_5$, where $E_{10}$ symmetrizes the ten individual strands and $R_5$ symmetrizes the five quadratic packets. The three binary files encode a common rational witness $Z$ and certificates for its partial transposes. A whole-packet partial transpose acts on a subset of the five packet factors.

The verifier establishes that each partial transpose of $Z$ is positive definite and that

$$
\frac{\operatorname{Tr}(Z X_5)}{36^5}
= -\frac{105532792597}{155520000000}.
$$

A sum of whole-packet partial transposes of positive semidefinite operators would have nonnegative pairing with this witness. The negative value therefore excludes that representation of the gap. Marcus’s inequality at five quadratic blocks concerns the value on factored packet states.

## Replay

Use GCC with C++17 on a little-endian 64-bit machine. Copy this directory to a working directory and run the following there. The three regenerated algebra tables use about 150 MiB in total.

```sh
g++ -O3 -std=c++17 five_packet_density.cpp -o five_packet_density
g++ -O3 -std=c++17 verify_five_packet_ppt.cpp -o verify_five_packet_ppt
for cut in 0 1 2; do
  ./five_packet_density "$cut" 8 "five_packet_density_cut${cut}_d8.bin" || exit 1
  ./verify_five_packet_ppt "five_packet_density_cut${cut}_d8.bin" \
    "five_packet_ppt_witness_cut${cut}.bin" || exit 1
done
```

The verifier prints `EXACT PASS` for cut sizes 0, 1 and 2, with matrix orders 85, 310 and 588. Packet permutation symmetry and full transposition cover all remaining subsets. Cut 0 also prints the exact negative trace pairing as an unreduced fraction. The displayed margins use floating point. All sign decisions use integer arithmetic.

The independent Python audit checks 400 signed arithmetic operations, diagram contractions and selected congruence rows. After the C++ replay, install NumPy and run it in the same working directory.

```sh
python3 -m pip install numpy
python3 audit_five_packet_webs.py
```
