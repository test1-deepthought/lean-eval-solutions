# Failed Lean-Eval Submission

Problem: irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
(not supplied)

## Exact Failed Lean Error
Unable to complete proof of Perron-Frobenius theorem. The theorem requires proving that an irreducible nonnegative matrix has a positive eigenvector at its spectral radius. The proof approach uses:
1. Variational characterization: r* = sup {r : ∃ v ≥ 0, Av ≥ rv}
2. Compactness of simplex to extract maximizing sequence
3. Upper semicontinuity to show limit point satisfies Av* ≥ r*v*
4. Maximality + irreducibility to show Av* = r*v* and v* > 0
5. Proof that r* = (spectralRadius ℝ A).toReal

Key lemmas needed: Matrix.isIrreducible_iff_exists_pow_pos, isCompact_stdSimplex, spectral radius properties.

## Next Lemma To Prove
(not supplied)
