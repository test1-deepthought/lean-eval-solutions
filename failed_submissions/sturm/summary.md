# sturm — Current State

**Last updated:** 20260712T033903Z
**Total attempts:** 17
**Status:** PARTIALLY VERIFIED

## Target Theorem

See `Submission.lean` in the repository root or the latest attempt below.

## Verified Lemmas

**16 lemmas verified across all attempts**

| # | Lemma | SHA256 | Attempts |
|---|-------|--------|----------|
| 1 | `-------` | `--------` | ---------- |
| 2 | `Lemma_1036` | `737d483e79ee` | ? |
| 3 | `Lemma_4689` | `a0a796e0238b` | ? |
| 4 | `Lemma_7925` | `25828b01ed7a` | ? |
| 5 | `no_common_root` | `a4f272cc8365` | ? |
| 6 | `nodup_roots_of_squarefree` | `7f282722dd0b` | ? |
| 7 | `not_root_of_eval_ne_zero` | `1511660bbbe5` | ? |
| 8 | `signChanges_append_zeros` | `fe69e68f301a` | ? |
| 9 | `signChanges_cons_zero` | `cf7d7250e257` | ? |
| 10 | `signChanges_nil` | `ec4ac8f09f0e` | ? |
| 11 | `signChanges_pair` | `00e22926e6c1` | ? |
| 12 | `signChanges_singleton` | `0f086c54885b` | ? |
| 13 | `signChanges_zeros_irrelevant` | `744d4a053843` | ? |
| 14 | `squarefree_imp_no_common_root` | `b9313dcd4032` | ? |
| 15 | `squarefree_imp_separable` | `49ab5685abfc` | ? |
| 16 | `sturm` | `d83e4dc18e50` | ? |

## Unproven Components

**0 component(s) remaining**

All frontier lemmas verified — main theorem assembly remains.

## Strategy History

| # | Timestamp | Lemma | Approach | Result |
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
|---|-----------|-------|----------|--------|
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
| 13 | 20260712T032027Z | `(unknown)` | agent-provided report | saved |
| 15 | 20260712T032717Z | `(unknown)` | agent-provided report | saved |
| 17 | 20260712T033903Z | `signChanges_filter_lemmas` | agent-provided report | saved |

## Recommended Next Steps

1. **Assemble main theorem** — all lemmas verified, wire them into `Submission.lean` and CI-verify.
