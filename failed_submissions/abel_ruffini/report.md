# Abel-Ruffini Theorem — Partial Progress

## What was completed
1. **Quintic polynomial irreducibility**: Proved `Irreducible (X^5 - 4X + 2)` over ℚ using Eisenstein criterion with p=2 over ℤ then mapping to ℚ.
   - Key lemmas: `irreducible_Φ`, `separable_Φ`, `map_Φ_eq`
2. Basic lemmas about `coeff` and polynomial degree used in the Eisenstein proof.

## What remains
1. **Galois group = S₅**: The lemma `not_solvable_by_rad_Φ` needs the Galois group computation using `galActionHom_bijective_of_prime_degree'` which requires:
   - Root count of Φ over ℝ (at least 2, at most 3)
   - Root count over ℂ (exactly 5)
   - These require analysis lemmas (`card_rootSet_le_derivative`, intermediate value theorem)
2. **Forward direction (n ≤ 4)**: Need to show all roots of degree 1-4 polynomials are in `solvableByRad`:
   - n=1: trivial (rational roots)
   - n=2: quadratic formula via `solvableByRad.rad_mem`
   - n=3,4: cubic/quartic formulas (Cardano/Ferrari) or Galois-theoretic argument
3. **Padding for n > 5**: Construct counterexample polynomial of any degree n ≥ 5.

## Key verified lemmas
- `irreducible_Φ : Irreducible (X^5 - C(4:ℚ)*X + C(2:ℚ))`
- `separable_Φ : Φ.Separable`
- `map_Φ_eq` connecting the ℤ and ℚ forms