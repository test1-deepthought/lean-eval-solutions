# sturm — Current State

**Last updated:** 20260628T100936Z
**Total attempts:** 11
**Status:** PARTIALLY VERIFIED

## Target Theorem

See `Submission.lean` in the repository root or the latest attempt below.

## Verified Lemmas

**32 lemmas verified across all attempts**

| # | Lemma | SHA256 | Attempts |
|---|-------|--------|----------|
| 1 | `-------` | `------` | --------- |
| 2 | `Lemma_196` | `0b0af530a7e8` | ? |
| 3 | `Lemma_2557` | `ab3705b2e28e` | ? |
| 4 | `Lemma_8055` | `38df291f909e` | ? |
| 5 | `Lemma_8120` | `571b733a8a15` | ? |
| 6 | `eval_derivative_ne_zero_of_squarefree_root` | `eval_derivative_ne_zero_of_squarefree_root.lean` | At a squarefree root, $p'(r) \neq 0$ |
| 7 | `eval_mod_eq_eval_of_root` | `11d2695a21fc` | ? |
| 8 | `eval_remainder_at_root` | `eval_remainder_at_root.lean` | $(a \% b).\text{eval}\, r = a.\text{eval}\, r$ when $b(r)=0$ |
| 9 | `factor_theorem_with_deriv` | `factor_theorem_with_deriv.lean` | $p = (X-r) \cdot q$ with $q(r) = p'(r)$ |
| 10 | `hp_ne_zero` | `524e116fba7c` | ? |
| 11 | `next_chain_entry_eval` | `next_chain_entry_eval.lean` | $(-(a \% b)).\text{eval}\, r = -a.\text{eval}\, r$ when $b(r)=0$ |
| 12 | `nonzero_near` | `nonzero_near.lean` | If $q(r) \neq 0$, there's a $\delta$-neighborhood where $q(x) \neq 0$ |
| 13 | `signChanges_cons_cons` | `6d3716938a52` | ? |
| 14 | `signChanges_cons_cons_nonzero` | `signChanges_cons_cons_nonzero.lean` | Recurrence: $a \neq 0, b \neq 0 \implies \text{signChanges}(a::b::\text{rest}) = [ab<0] + \text{signChanges}(b::\text{rest})$ |
| 15 | `signChanges_cons_nonzero` | `5eb9d4145d19` | ? |
| 16 | `signChanges_cons_triple` | `020071b9ef24` | ? |
| 17 | `signChanges_cons_zero` | `signChanges_cons_zero.lean` | Leading zero removed without affecting count |
| 18 | `signChanges_filter_eq` | `signChanges_filter_eq.lean` | Invariant under zero removal |
| 19 | `signChanges_flip_first` | `1294366b0016` | ? |
| 20 | `signChanges_nil` | `signChanges_nil.lean` | `signChanges [] = 0` |
| 21 | `signChanges_pair` | `signChanges_pair.lean` | `signChanges [a,b] = 1` iff $ab < 0$ |
| 22 | `signChanges_singleton` | `signChanges_singleton.lean` | `signChanges [a] = 0` |
| 23 | `signChanges_splice_zero` | `signChanges_splice_zero.lean` | Inserting zero doesn't change count |
| 24 | `signChanges_triple_opposite` | `signChanges_triple_opposite.lean` | $\text{signChanges}[a,b,c] = 1$ when $a\cdot c < 0$ |
| 25 | `sign_constant_ac` | `a693798c3e25` | ? |
| 26 | `sign_constant_on_Ioo` | `sign_constant_on_Ioo.lean` | If $q$ has no root in $(c,d)$, sign is constant there (via IVT) |
| 27 | `sign_near` | `089470b69bfc` | ? |
| 28 | `sign_near_neg` | `06987b56cf7d` | ? |
| 29 | `squarefree_imp_separable` | `squarefree_imp_separable.lean` | Over $\mathbb{R}$, `Squarefree` $\implies$ `Separable` (via `PerfectField`) |
| 30 | `squarefree_no_common_root` | `3a1e7f3f7a9f` | ? |
| 31 | `sturm_adjacent_opposite` | `d33018619834` | ? |
| 32 | `triple_sign_lemma` | `triple_sign_lemma.lean` | For $a \cdot c < 0, b \neq 0$: $[ab<0] + [bc<0] = 1$ |

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
| 1 | 20260628T022441Z | `(unknown)` | agent-provided report | saved |
| 3 | 20260628T022640Z | `(unknown)` | agent-provided report | saved |
| 5 | 20260628T024341Z | `(unknown)` | agent-provided report | blocked |
| 7 | 20260628T032656Z | `sigma_constant_on_rootless_interval` | agent-provided report | blocked |
| 9 | 20260628T041414Z | `(unknown)` | agent-provided report | saved |
| 11 | 20260628T100936Z | `(unknown)` | agent-provided report | saved |

## Recommended Next Steps

1. **Assemble main theorem** — all lemmas verified, wire them into `Submission.lean` and CI-verify.
