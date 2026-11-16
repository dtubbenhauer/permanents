# Stage 12 — Counting the choices of crossing slots

For blocks of p and q labelled slots, the possible images of the first block are the p-element subsets of their disjoint union. The proof splits each image that meets the right block in r slots into a (p−r)-element subset of the left block and an r-element subset of the right block. The bijection proves that the number of distinct images is choose(p,r) choose(q,r). It also covers empty packets.

The declarations checked individually in this stage are

- `BlockPermanents.SchurSubsetCount.card_subsets`
