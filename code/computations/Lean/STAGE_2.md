# Stage 2 — the full-cap row of the four-packet bend

Lemma 5C.2, equation (5C.3) in the 16 November draft, bends packet 4. At the full cap, packet 1 contracts with packet 4 and the outputs occur in the order 2, 3. Write p for the fine clasp on those two outputs. With a = binom(2k,k), b = binom(3k,k), c = ab, the four terms are

    cb |v − pu/b|² + 3a² |w|² − 12 |u|² − 4a |pu|².

Here |D|² = D†D. The three half-maps u, w and v are LF, LPF and LE in Definition 5C.1. The theorem uses the complex word matrices of the specified clasps and contractions. The matrix of the moved pair and the survivor identity commute the fine 2k-clasp past L to identify pu. At k = 2 the four signed coefficients are 1350, 108, −12 and −24, and the internal coefficient is 1/15.

## Entry points

All declarations below are in the namespace `BlockPermanents.FourNative`.

- `full_cap_row` in FourFullCapRow.lean starts from the original marked transfer on four packet clasps. For any dimension d and k > 0 its only mathematical inputs are the homogeneous Schur relations at (k,k), (2k,k) and (3k,k) in dimension d. It concludes the equality to three grouped proper-cut terms plus the full-cap row.
- `terminalSquares` and `read_raw` in FourNativeTerminal.lean give the four squares on rectangular feet. The proof obtains the reflection and uprightness identities for the actual ordinary factors.
- `boundary_fixed` and `clasps_fixed` in FourNativeBoundary.lean discharge the compression condition on independently symmetric columns and on the canonical clasped boundary.
- `corrected_square_weight` and `quadratic_weights` check the manuscript coefficient cb = ab² and its specialization at k = 2.

## Next bounded stage

Identify the proper cuts in the first family for arbitrary 1 ≤ r < k with the diagram U_r. Prove that its contribution after reading the bend is 6 binom(k,r)² |U_r|² on the packet boundary. The two other proper-cut families remain separate. End with a project build, an axiom audit and a checkpoint.
