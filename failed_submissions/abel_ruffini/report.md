# Failed Lean-Eval Submission

Problem: abel_ruffini
Mode: new
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
irreducible_Φ (Eisenstein criterion for X^5 - 4X + 2 over ℚ)

## Exact Failed Lean Error
Proof incomplete - this is the Abel-Ruffini theorem, a major theorem requiring the full solvability theory of polynomials by radicals. The (→) direction requires constructing a quintic with Galois group S₅, proving its irreducibility via Eisenstein, showing 3 real roots via calculus, then applying galActionHom_bijective_of_prime_degree' to get S₅, and using Equiv.Perm.fin_5_not_solvable with isSolvable_gal_of_irreducible to conclude. The (←) direction requires proving that all degree ≤ 4 polynomials have all roots solvable by radicals, either via explicit Cardano/Ferrari formulas or via Galois correspondence with solvable S₁,S₂,S₃,S₄. Both directions require extensive formalization beyond what was achievable in this session.

## Next Lemma To Prove
irreducible_Φ (Eisenstein criterion for X^5 - 4X + 2 over ℚ)
