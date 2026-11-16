# Stage 16 — The dimension of the surviving cable

Fix a nonzero decomposable packet and cut r of its k strands. The surviving positive word lies in W_r, the span of the uncontracted atom products. Freezing the r contracted letters gives a slice in W_r; if all slices vanished then the full packet would vanish. Thus its dimension d_r satisfies 1 ≤ d_r ≤ choose(k,r). The result covers the straight and full cuts, and requires no independence of the atom vectors.

The declarations checked individually in this stage are

- `BlockPermanents.PairResidual.slice_mem`
- `BlockPermanents.PairResidual.rank_pos`
- `BlockPermanents.PairResidual.rank_le`
