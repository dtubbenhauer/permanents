# Stage 20 — The polarized halfweb identity of Lemma 7A.1

The explicit residual halfwebs in Lemma 7A.1 give an equality of Hermitian Gram matrices on any finite family of symmetric second inputs. Let B have these inputs as columns, A denote symmetric multiplication by the fixed unit packet, T be the pairing row composed with B, and R_r the conjugated residual halfweb of Stage 19. Write |U|² for U†U. With C_r = choose(k,r), the equality is

    choose(2k,k) |AB|² − |B|² − (2ᵏ−1)|T|²
      = ∑_{r=1}^k [ C_r² |R_r B|² + (C_r²/d_r − C_r)|T|² ].

The right-hand factors come from the open cap in the manuscript and its trace complement. Polarization proves the equality for off-diagonal entries, so B can include arbitrary dependent columns. The algebraic hypotheses are the unit normalization of the decomposable first packet and symmetry of each second input.

For any orthonormal pair e,f in ℂᵈ, put X = [e f]. Lean computes the true middle-cut matrix of their normalized symmetric packet as XX†/2. It has trace 1 and squared norm 1/2. The straight, single and double cuts contribute 1, 2 and 1, so the example attains 4 for any orthonormal pair in the ambient space.

## Next manuscript target

Theorem 3D.2 gives the reflected-halfweb decomposition of the three-packet transfer on every marked subspace S with 1 ≤ dim S ≤ k. The present three-packet proof (ThreeGeneralOpen.original_supported and the corresponding supported square expansion) uses a coordinate subset. The next step is to transport the named halfwebs and their coefficients to an arbitrary complex subspace, including the coefficient 2k²/dim S − 9/4 on the completed cap.

The declarations checked individually in this stage are

- `BlockPermanents.PairResidual.full_caps_residual_operator`
- `BlockPermanents.PairOrthonormalExample.middle_matrix`
- `BlockPermanents.PairOrthonormalExample.middle_trace`
- `BlockPermanents.PairOrthonormalExample.middle_energy`
- `BlockPermanents.PairOrthonormalExample.cut_values`
- `BlockPermanents.PairOrthonormalExample.equality_four`
