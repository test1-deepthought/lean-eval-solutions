# sturm — Current State

**Last updated:** 20260712T031132Z
**Total attempts:** 11
**Status:** PARTIALLY VERIFIED

## Target Theorem

See `Submission.lean` in the repository root or the latest attempt below.

## Verified Lemmas

**3 lemmas verified across all attempts**

| # | Lemma | SHA256 | Attempts |
|---|-------|--------|----------|
| 1 | `-------` | `--------` | ---------- |
| 2 | `no_common_root` | `a4f272cc8365` | ? |
| 3 | `squarefree_imp_separable` | `49ab5685abfc` | ? |

## Unproven Components

**0 component(s) remaining**

All frontier lemmas verified — main theorem assembly remains.

**Last error:** The proof of Sturm's theorem requires several deep analytic lemmas that are not yet formalized:
1. Lemma: sigma is locally constant on intervals where no Sturm chain entry vanishes (needs continuity of polynomials and sign stability)
2. Lemma: At a simple root r of p (p(r)=0, p'(r)≠0), sigma drops b

## Strategy History

| # | Timestamp | Lemma | Approach | Result |
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
| 1 | 20260707T022127Z | `(unknown)` | agent-provided report | saved |
| 3 | 20260707T085800Z | `(unknown)` | agent-provided report | saved |
| 5 | 20260711T101631Z | `(unknown)` | agent-provided report | saved |
| 7 | 20260711T122249Z | `sigma_drop_at_simple_root: Prove that at a simple root x of p (where p(x)=0, p'(x)≠0), sigma(p,x-ε) - sigma(p,x+ε) = 1 for sufficiently small ε. This requires analyzing the sign of p and p' near x using continuity and the derivative.` | failed: Unable to complete the full formal proof of Sturm's theorem within the session b | blocked |
| 9 | 20260711T135047Z | `sigma_const_on_interval (proved) → then main theorem induction` | failed: The full formalization of Sturm's theorem is a research-level undertaking (~1000 | blocked |
| 11 | 20260712T031132Z | `lemma_sigma_const_between_roots` | failed: The proof of Sturm's theorem requires several deep analytic lemmas that are not  | blocked |

## Recommended Next Steps

1. **Assemble main theorem** — all lemmas verified, wire them into `Submission.lean` and CI-verify.
