# Stage 38 — The raw face sums in (AA.2) and the deletion recurrence

Each three-set and four-set is counted once. Summing the actual marked partners gives the coefficients 3/q and 4/[q(q−3)] in (AA.2). The recursion for the prescribed four-face slack retains both remainders with weights 1/4 and 3/4. With three labels left the terminal term is the averaged squared exit, and with four the propagated remainder vanishes.

The declarations checked individually in this stage are

- `BlockPermanents.RawTripleFaces.face_card`
- `BlockPermanents.RawTripleFaces.subset_sum`
- `BlockPermanents.RawTripleFaces.exitTotal_marked`
- `BlockPermanents.RawTripleFaces.triple_faces`
- `BlockPermanents.RawTripleFaces.quadruple_faces`
- `BlockPermanents.RawTripleFaces.three_face_bound`
- `BlockPermanents.RawTripleFaces.four_face_bound`
- `BlockPermanents.FacePropagationSquares.propagate_squares`
- `BlockPermanents.FacePropagationSquares.propagation_nonneg`
