# Stage 5 — the complete four-packet bend

The declaration `BlockPermanents.FourNative.four_packet_bend` in FourBendIdentity.lean proves the open matrix identity in Lemma 5C.2, equation (5C.3) of the 16 November manuscript. It starts at Q on the four packet clasps in complex word coordinates. It applies for every ambient dimension d and every k > 0 given the three homogeneous Schur relations at (k,k), (2k,k) and (3k,k).

With a = binom(2k,k), b = binom(3k,k), c = ab, and |D|² = D†D, the formula reads

    Q^Γ = ∑_{1 ≤ r < k} binom(k,r) [
               6 binom(k,r) |Uᵣ|²
             + 3a binom(2k,r) |Wᵣ|²
             + c binom(3k,r) |Vᵣ|² ]
          + cb |v − pu/b|² + 3a² |w|² − 12 |u|² − 4a |pu|².

The formal statement has a single index `i : Fin (k-1)`; its cap number is i.val + 1. Thus k = 1 gives the empty proper-cut sum. The definition of p is the symmetric 2k-clasp on the two outputs of u. The equality is an identity on the whole clasped boundary, including off-diagonal matrix entries.

## Third family

Definition 5C.1 averages the ordinary packets, joins them in order 1, 2, 3, applies the 3k-clasp and contracts r strands with the dual marked packet. `thirdProperHalf` gives precisely the resulting map on the two through words. The proof identifies the symmetric merge with its native clasped exchange. It shows that the 3k-clasp absorbs the ordinary average, and that the empty spectator contributes a factor of one. `third_proper_term` and `third_proper_family` need no Schur hypotheses. The three stated Schur inputs enter when expanding Q.

## Quadratic specialization

The theorem `four_packet_bend_quadratic` checks the proper-cut part as 24 |U₁|² + 144 |W₁|² + 1080 |V₁|². The full-cap row is the one verified in Stage 2, with coefficients 1350, 108, −12 and −24 and correction v − pu/15.

## Next bounded stage

Check the last sentence of Definition 5C.1 on these same word matrices: the survivor clasp fixes the terminal half v, so pv = v. This would connect the terminalV half in (5C.3) to the projected output used in the following supported estimates. Stop after this identity and the project audit.
