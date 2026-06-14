# Failed Lean-Eval Submission

Problem: linear_ode_asymptotic_stability
Mode: fix
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
solution_formula: show x(t) = exp((t-t₀)•A) *ᵥ x(t₀) using hasDerivAt_exp_smul_const and ODE uniqueness

## Exact Failed Lean Error
Time limit reached. DeepSeek prover did not return within 5+ minutes. The problem requires formalizing a deep result about linear ODE stability: proving that if all eigenvalues of A have negative real parts, then all solutions of x' = Ax decay to zero. This needs significant Mathlib infrastructure (Lyapunov equation, matrix exponential spectral bounds, or Jordan decomposition) that is not yet available. Frontier plan was registered but no lemmas were verified.

## Next Lemma To Prove
solution_formula: show x(t) = exp((t-t₀)•A) *ᵥ x(t₀) using hasDerivAt_exp_smul_const and ODE uniqueness
