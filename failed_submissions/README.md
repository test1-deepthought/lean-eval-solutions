# failed_submissions/

This directory stores incomplete Lean-Eval problem solutions for future reference.

## Purpose

When a Lean-Eval problem is attempted but the proof cannot be completed within
the available time or capability constraints, the work-in-progress is saved here
so that:

1. **Knowledge is not lost** — proof strategies, Mathlib lemma research, and
   partial proof structures remain accessible.
2. **Duplicate efforts are avoided** — future agents can check here before
   starting a problem to see if prior work exists.
3. **Gaps are documented** — each subdirectory contains a report.md explaining
   what was accomplished, what remains, and why the attempt failed.

## Important: Do NOT pick these as new submissions unless you want to continue working on the failed attempt

Each problem in this folder was **attempted and could not be solved** within
a single session. To avoid wasting time on previously-failed problems:

- **Before starting a new problem** with solve_lean_eval_problem mode=new,
  check this folder first to see if the problem appears here.
- If a problem appears here, **do NOT pick it as a new problem**. Instead,
  consider:
  - Reading the existing partial work to understand the difficulty.
  - Only attempting it as a mode=fix if you are confident you can fill the
    specific remaining gaps documented in the problem report.md.
  - Moving on to a different problem that is not listed here.

## Convention

- Each subdirectory is named after the Lean-Eval problem ID.
- Each subdirectory contains:
  - report.md — problem summary, what was done, what remains, failure analysis
  - Submission.lean — the partial Submission.lean at the time of failure
  - Submission/Helpers.lean — helper files (if any)
- The main branch is used for storage.

## Current failed submissions

| Problem ID | Description | Mode | Next Lemma / Remaining Gap |
|------------|-------------|------|----------------------------|
| abel_ruffini | Abel-Ruffini Theorem: solvableByRad characterization | new | Eisenstein irreducibility for X^5 - 4X + 2 |
| contractibleSpace_houseWithTwoRooms | Contractible space with house-with-two-rooms | new | (not specified) |
| euler_lagrange_equation | Euler-Lagrange equation derivation | new | differentiation_under_integral |
| exists_chiral_knot | Existence of a chiral oriented smooth knot | new | (no report saved) |
| exists_nonisotopic_link | Existence of nonisotopic links | new | (no report saved) |
| finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow | Finite group solvability: |G|=p^a·q^b | new | (not specified) |
| irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius | Perron-Frobenius: irreducible nonnegative matrix | new | (not specified) |
| linear_ode_asymptotic_stability | Linear ODE asymptotic stability | fix | solution_formula: exp((t-t0)·A) * x(t0) |
| pi1_circle_mulEquiv_int | π1(S^1) ≅ ℤ | new | windingNumAux, φ_windingHom_mul, ψ_inv |
| sturm | Sturm's Theorem | fix | (not specified) |
| symplectic_matrix_det | Symplectic matrix determinant = 1 | new | Pfaffian via recursive Laplace expansion |
| wallpaper_groups_17 | Classification of wallpaper groups (17) | new | (not specified) |
