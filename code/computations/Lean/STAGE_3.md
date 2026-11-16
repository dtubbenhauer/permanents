# Stage 3 — the first family of proper cuts

In Definition 5C.1, Uᵣ bends packet four against one ordinary packet after F averages the ordinary packet labels. The other two ordinary packets pass straight through in order. The two active cables each have k−r through strands. On the marked cable the through strands are dual.

For every proper index 1 ≤ r < k, the contribution in the first family of Lemma 5C.2 is

    6 binom(k,r)² Uᵣ† Uᵣ.

The two binomial factors count the choices on the ordinary and marked cable. The factor 6 comes from the marked transfer. At k = 2 there is a single proper cut, with contribution 24 U₁† U₁. At k = 1 the index set is empty.

## Lean entry points

The declarations below are in `BlockPermanents.FourNative`.

- `firstProperHalf` takes the rightmost ordinary cable as in the figure. Its word matrix records both spectators and both through words. The routed cap conjugates the marked foot.
- `drawn_half_eq` proves that this matrix equals the one obtained by capping packets 1 and 4 and retaining packets 2 and 3 in order. The cyclic permutation of the ordinary labels is absorbed by F.
- `first_proper_term` checks the coefficient and the Gram square of each individual native exchange. `first_proper_family` sums over the proper indices. Neither statement requires a Schur hypothesis.
- `transfer_first_proper` substitutes this family into the original bent four-packet transfer on the packet-clasp boundary. It uses the three Schur instances at (k,k), (2k,k) and (3k,k). It retains the Stage 2 full-cap row and leaves the two other proper-cut families grouped.
- `quadratic_first_family` proves the k = 2 specialization as an operator equality.

## Next bounded stage

Identify the second family Wᵣ, which merges two ordinary packets before the bend. Check the term 3a binom(2k,r) binom(k,r) Wᵣ† Wᵣ with a = binom(2k,k), including the surviving packet and the order of the through strands. End after the project build and axiom audit.
