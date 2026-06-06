# Abel-Ruffini Theorem — Failed Attempt

**Problem ID**: `abel_ruffini`  
**Date**: Saturday, June 6, 2026  
**Status**: INCOMPLETE (partial proof with sorries)

## What was accomplished

1. **Problem analysis and proof strategy** fully planned:
   - → direction (n ≥ 5): counterexample via X⁵ - 4X + 2 with Galois group S₅
   - ← direction (n ≤ 4): constructive formulas (linear, quadratic, cubic, quartic)

2. **Mathlib exploration completed** — all key theorems identified and verified:
   - `solvableByRad.isSolvable'` — the forward direction (radical → solvable Galois)
   - `Polynomial.Gal.galActionHom_bijective_of_prime_degree'` — sufficient condition for S₅
   - `Equiv.Perm.fin_5_not_solvable` — S₅ not solvable
   - `irreducible_of_eisenstein_criterion` — Eisenstein criterion
   - `IsPrimitive.Int.irreducible_iff_irreducible_map_cast` — ℤ ↔ ℚ irreducibility

3. **Eisenstein irreducibility proof** (partial):
   - Polynomial coefficients, natDegree=5, monic, leading coefficient=1 all computed
   - Eisenstein structure assembled but not fully filled in

4. **Existing Mathlib Archive reference**: The Archive/Wiedijk100Theorems/AbelRuffini.lean
   in mathlib4 at commit c63252f contains a related but different proof
   (constructing an algebraic number not solvable by radicals for the specific
   quintic X⁵ - 4X + 2).

## What remains

- Complete Eisenstein case analysis in `irreducible_of_eisenstein_criterion` call
- Real root count lemma (IVT for 2 roots, derivative bound for ≤3)
- Apply `galActionHom_bijective_of_prime_degree'` with root count data
- Contradiction with `Equiv.Perm.fin_5_not_solvable`
- Handle n > 5 padding
- Full ← direction (n≤4) using solvableByRad induction

## Why it failed

This is a **deeply challenging formalization** requiring:
- Galois theory (S₅ Galois group from root-counting conditions)
- Real analysis (IVT, derivative bounds for root counting)
- Eisenstein criterion application
- Constructive radical formulas for degrees 1-4
- solvableByRad induction principles

The proof is approximately 300-500 lines of Lean across multiple lemmas,
requiring expertise in Galois theory, analysis, and ring theory in Mathlib.
