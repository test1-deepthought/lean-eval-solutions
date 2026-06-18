# Failed Lean-Eval Submission

Problem: sturm
Mode: fix
Submission ref before failure: (none)

## Verified Lemmas Completed
(record in PROVE frontier state / attached candidate files)

## Current Frontier Lemma
sigma_drop_at_p_root - prove that at a root r of p (with p'(r) ≠ 0), there exists δ > 0 such that for u ∈ (r-δ, r), v ∈ (r, r+δ), sigma u - sigma v = 1. This uses the factor theorem to show sign(p) changes while sign(p') doesn't.

## Exact Failed Lean Error
Proof incomplete - the full formalization of Sturm's theorem requires proving that sigma drops by exactly 1 at each root of p and is locally constant elsewhere, then partitioning the interval at all roots of all chain members. The key lemmas (eval_mod_eq_eval_of_root, squarefree_no_common_root, opposite_signs_at_root, sign_const_between, factor_theorem, factor_deriv) have been proven. The complete proof requires approximately 200+ additional lines to formalize the chain analysis and interval partition.

## Next Lemma To Prove
sigma_drop_at_p_root - prove that at a root r of p (with p'(r) ≠ 0), there exists δ > 0 such that for u ∈ (r-δ, r), v ∈ (r, r+δ), sigma u - sigma v = 1. This uses the factor theorem to show sign(p) changes while sign(p') doesn't.
