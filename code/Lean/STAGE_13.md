# Stage 13 — Classifying and counting the block double cosets

Let the two blocks of labelled slots have sizes p and q. Every permutation factors into a within-block permutation, a standard exchange of r slots, and another within-block permutation. Such a factorization exists exactly when r left slots go to the right block. Thus r classifies the double cosets of the subgroup S_p × S_q in S_(p+q).

Every chosen image of the left block admits exactly p! q! orderings. Together with Stage 12 this gives p! q! choose(p,r) choose(q,r) permutations in the double coset with r crossings. These results hold for every pair of packet sizes, including zero.

The declarations checked individually in this stage are

- `BlockPermanents.SchurClass.factorization_iff`
- `BlockPermanents.SchurFibreCount.card_leftImage_fibre`
- `BlockPermanents.SchurFibreCount.card_cross_fibre`
