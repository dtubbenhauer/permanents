# Stage 17 — The two branches of a partial cap

The cap e on the surviving cable closes each actual cut Y_r to the pairing ⟨H,F⟩. Reopening it gives the bubble d_r. Its complement J_r = I − e†e/d_r fixes precisely the vectors annihilated by e; in particular e(J_rY_r)=0. For C = choose(k,r), the contribution at that cut is C²‖J_rY_r‖² + (C²/d_r)|⟨F,H⟩|². Retaining C copies of the completed cap leaves the nonnegative coefficient C²/d_r − C. The first packet may be scaled, and the second input can be any symmetric tensor.

The declarations checked individually in this stage are

- `BlockPermanents.PairResidual.close_cut`
- `BlockPermanents.PairResidual.cut_bubble`
- `BlockPermanents.PairResidual.cut_resolution`
- `BlockPermanents.PairResidual.surplus_nonneg`
- `BlockPermanents.PairResidual.J_fixes_iff`
- `BlockPermanents.PairResidual.residual_closes_to_zero`
