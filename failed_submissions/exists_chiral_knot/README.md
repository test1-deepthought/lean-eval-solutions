# Exists Chiral Knot — Failed Attempt

**Problem ID**: `exists_chiral_knot`  
**Date**: Saturday, June 6, 2026  
**Status**: INCOMPLETE (no progress — proof not started)

---

## ⚠️ DO NOT PICK THIS AS A NEW SUBMISSION

This problem was **previously attempted and could not be solved** within a
single session. Before starting any new Lean-Eval problem, check the top-level
[`failed_submissions/README.md`](../README.md) to see if the problem appears here.

If you find this problem listed:

- **Do NOT** use `solve_lean_eval_problem mode=new` with `problem=exists_chiral_knot`.
  The proof requires formalizing knot invariants (signature or Jones polynomial)
  from Seifert surface theory, which is not available in Mathlib.
- **Only** attempt as `mode=fix` if you can fill the specific remaining gaps
  documented below.
- Otherwise, **pick a different problem** not listed in `failed_submissions/`.

---

## What was accomplished

1. **Problem analysis completed**:
   - Statement: produce an oriented smooth knot `K` such that `K.Chiral` holds
     (i.e., `K` is not ambient-isotopic to its mirror image under reflection
     through the `xy`-plane).
   - The challenge provides minimal knot-theory infrastructure in `ChallengeDeps`:
     `Knot` (smooth 2π-periodic injective immersion `ℝ → ℝ³`), `AmbientIsotopy`,
     `CircleReparam`, `Knot.Isotopic`, `Knot.Chiral`.

2. **Informal solution strategy identified**:
   - **Candidate**: the right-handed trefoil knot.
   - **Invariant**: the knot signature `σ(K)`, computed from a Seifert matrix `V`
     as the signature of `V + Vᵀ`. Mirroring negates the signature, so any knot
     with `σ(K) ≠ 0` is chiral. The right-handed trefoil has `σ = -2`.
   - **Alternative**: the Jones polynomial `V_K(t) = -t⁻⁴ + t⁻³ + t⁻¹`, which is
     not symmetric under `t ↔ t⁻¹`.

3. **Mathlib gap identified**:
   - Mathlib has **no knot theory** beyond the minimal definitions in `ChallengeDeps`.
   - No Seifert surfaces, no Seifert matrices, no knot signature, no knot polynomials
     (Alexander, Jones, HOMFLY) are available.
   - The `ChallengeDeps` definitions (`Knot`, `Knot.Chiral`, `AmbientIsotopy`) are
     purely structural and provide no computational or invariant machinery.

## What would be needed

To prove `exists_chiral_knot` in Lean, one would need to formalize one of:

### Option A: Knot signature (requires ~500+ lines)
1. Seifert surface theory in terms of smooth embedded surfaces in `ℝ³` with
   the given knot as boundary.
2. Seifert matrix computation (linking numbers of a basis of the surface's
   first homology).
3. Definition of the knot signature as the signature of `V + Vᵀ`.
4. Proof that the signature is an ambient-isotopy invariant (requires surgery
   calculus on Seifert surfaces under isotopies).
5. Computation of the signature of the right-handed trefoil as `-2` (via
   the standard Seifert surface with pushoff curves).

### Option B: Jones polynomial (requires ~1000+ lines)
1. Diagrams/braid representations of knots (no infrastructure in Mathlib).
2. Kauffman bracket / skein relation definition.
3. Proof of invariance under Reidemeister moves.
4. Computation for the trefoil.

### Option C: Use known invariants without full formalization (~200-300 lines)
This would require:
- Stating the signature as an axiom/postulate or using `Classical.choice` to
  assume existence of an invariant that distinguishes the trefoil from its mirror.
- Such an approach would violate the "constructed proof" constraint of this
  Lean-Eval problem.

## Why it failed

This is an **extremely challenging formalization** requiring knot theory
infrastructure that does not yet exist in Mathlib. The `ChallengeDeps` provides
only the bare definitions needed to *state* the problem; none of the invariant
machinery (Seifert surfaces, signature, Jones polynomial) is available.

**Estimated effort**: 500-1500+ lines of Lean across multiple new theories,
substantially exceeding what can be completed in a single session.

## References
- https://en.wikipedia.org/wiki/Chirality_(mathematics)
- https://en.wikipedia.org/wiki/Trefoil_knot
- https://en.wikipedia.org/wiki/Seifert_surface
- https://en.wikipedia.org/wiki/Knot_signature
- https://en.wikipedia.org/wiki/Jones_polynomial
