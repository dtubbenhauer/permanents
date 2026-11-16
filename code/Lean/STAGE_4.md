# Stage 4 — the second family of proper cuts

In the middle diagram of Definition 5C.1, packet 1 passes straight through. Packets 2 and 3 merge, in order, through the symmetric 2k-clasp. The r-fold cap with packet 4 leaves through words of lengths 2k−r and k−r, with the marked word dualized.

For 1 ≤ r < k the contribution in equation (5C.3) is

    3 a binom(2k,r) binom(k,r) Wᵣ† Wᵣ,   a = binom(2k,k).

The two binomial factors count choices on the merged and marked cables. The coefficient of the second family in the transfer is 3a. For k = 2 the single term is 144 W₁† W₁.

## Lean entry points

All declarations below are in the namespace `BlockPermanents.FourNative`.

- `secondProperHalf` uses the explicit 2k-clasp at the merge. `routed_merge_clasp` proves that the fork absorbs this clasp with coefficient one.
- `drawnMergedSlice_apply` records the spectator and both merged inputs. `drawn_merged_eq` identifies the drawn placement with the native one using cyclic invariance of the three-packet average. Together these yield the rectangular matrix identity `secondProperHalf_native`.
- `second_proper_term`, `second_proper_family`, and `quadratic_second_family` prove the fixed-cut, summed, and quadratic formulas on the packet-clasp boundary. These identities use no Schur hypothesis.
- `transfer_second_proper` inserts the first two families into the original bent four-packet transfer. It takes the homogeneous Schur relation at (k,k), (2k,k) and (3k,k), retains the full-cap row of Stage 2, and leaves the third proper-cut family grouped.

## Next bounded stage

Identify the third proper-cut family Vᵣ, in which all three ordinary packets merge. Prove its coefficient c binom(3k,r) binom(k,r) with c = (3k)!/(k!)³, and combine all three proper-cut families with the verified full-cap row to conclude equation (5C.3). Stop after checking the combined operator identity, building and auditing the project, and saving the checkpoint.
