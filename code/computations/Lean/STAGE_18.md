# Stage 18 — The exact residual sum in Lemma 7A.1

Fix a unit F proportional to a decomposable symmetric packet. For every symmetric second input Z the difference in Lemma 7A.1 equals the sum over 1 ≤ r ≤ k of C_r²‖J_rY_r‖² + (C_r²/d_r − C_r)|⟨F,Z⟩|², where C_r = choose(k,r) and d_r = dim W_r. The support and projector at each cut depend only on the chosen first packet data. Lean proves nonnegativity for each summand separately. The straight cut supplies ‖Z‖²; the retained completed caps sum to (2ᵏ−1)|⟨F,Z⟩|². The proof uses the homogeneous Schur relation proved in Stage 15.

Equality is also characterized: at each nonzero cut J_rY_r must vanish and either the full pairing is zero or d_r = C_r. This follows by testing the two nonnegative terms separately.

The declarations checked individually in this stage are

- `BlockPermanents.PairResidual.summand_nonneg`
- `BlockPermanents.PairResidual.full_caps_residual_squares`
- `BlockPermanents.PairResidual.summand_eq_zero_iff`
- `BlockPermanents.PairResidual.full_caps_eq_iff`
