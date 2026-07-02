# sturm — Current State

**Last updated:** 20260702T053716Z
**Total attempts:** 20
**Status:** PARTIALLY VERIFIED

## Target Theorem

See `Submission.lean` in the repository root or the latest attempt below.

## Verified Lemmas

**46 lemmas verified across all attempts**

| # | Lemma | SHA256 | Attempts |
|---|-------|--------|----------|
| 1 | `-------` | `------` | --------- |
| 2 | `Lemma_196` | `0b0af530a7e8` | ? |
| 3 | `Lemma_2557` | `ab3705b2e28e` | ? |
| 4 | `Lemma_2902` | `f5e3801843a3` | ? |
| 5 | `Lemma_3536` | `25cc595febe8` | ? |
| 6 | `Lemma_3915` | `a8117b26ace8` | ? |
| 7 | `Lemma_6271` | `f1ed9fda782c` | ? |
| 8 | `Lemma_8055` | `38df291f909e` | ? |
| 9 | `Lemma_8120` | `571b733a8a15` | ? |
| 10 | `deriv_eq_poly_deriv` | `8d99761725c5` | ? |
| 11 | `deriv_ne_zero_at_root` | `c9b22c4ffbee` | ? |
| 12 | `eval_derivative_ne_zero_of_squarefree_root` | `eval_derivative_ne_zero_of_squarefree_root.lean` | At a squarefree root, $p'(r) \neq 0$ |
| 13 | `eval_mod_eq_eval_of_root` | `11d2695a21fc` | ? |
| 14 | `eval_remainder_at_root` | `eval_remainder_at_root.lean` | $(a \% b).\text{eval}\, r = a.\text{eval}\, r$ when $b(r)=0$ |
| 15 | `exist_interval_deriv_pos` | `c7681b9548a2` | ? |
| 16 | `factor_theorem_with_deriv` | `factor_theorem_with_deriv.lean` | $p = (X-r) \cdot q$ with $q(r) = p'(r)$ |
| 17 | `filter_id_of_all_nonzero` | `a8114fd7947c` | ? |
| 18 | `first_flip_opposite` | `f17d08d5331c` | ? |
| 19 | `hp_ne_zero` | `524e116fba7c` | ? |
| 20 | `mvt_eq` | `4a4ecf4dbcb0` | ? |
| 21 | `next_chain_entry_eval` | `next_chain_entry_eval.lean` | $(-(a \% b)).\text{eval}\, r = -a.\text{eval}\, r$ when $b(r)=0$ |
| 22 | `nonzero_near` | `nonzero_near.lean` | If $q(r) \neq 0$, there's a $\delta$-neighborhood where $q(x) \neq 0$ |
| 23 | `opposite_signs` | `a45689a99e23` | ? |
| 24 | `signChanges_cons_cons` | `6d3716938a52` | ? |
| 25 | `signChanges_cons_cons_nonzero` | `signChanges_cons_cons_nonzero.lean` | Recurrence: $a \neq 0, b \neq 0 \implies \text{signChanges}(a::b::\text{rest}) = [ab<0] + \text{signChanges}(b::\text{rest})$ |
| 26 | `signChanges_cons_nonzero` | `5eb9d4145d19` | ? |
| 27 | `signChanges_cons_triple` | `020071b9ef24` | ? |
| 28 | `signChanges_cons_zero` | `signChanges_cons_zero.lean` | Leading zero removed without affecting count |
| 29 | `signChanges_filter_eq` | `signChanges_filter_eq.lean` | Invariant under zero removal |
| 30 | `signChanges_flip_first` | `1294366b0016` | ? |
| 31 | `signChanges_nil` | `signChanges_nil.lean` | `signChanges [] = 0` |
| 32 | `signChanges_pair` | `signChanges_pair.lean` | `signChanges [a,b] = 1` iff $ab < 0$ |
| 33 | `signChanges_singleton` | `signChanges_singleton.lean` | `signChanges [a] = 0` |
| 34 | `signChanges_splice_zero` | `signChanges_splice_zero.lean` | Inserting zero doesn't change count |
| 35 | `signChanges_triple_opposite` | `signChanges_triple_opposite.lean` | $\text{signChanges}[a,b,c] = 1$ when $a\cdot c < 0$ |
| 36 | `sign_constant_ac` | `a693798c3e25` | ? |
| 37 | `sign_constant_on_Ioo` | `sign_constant_on_Ioo.lean` | If $q$ has no root in $(c,d)$, sign is constant there (via IVT) |
| 38 | `sign_near` | `089470b69bfc` | ? |
| 39 | `sign_near_neg` | `06987b56cf7d` | ? |
| 40 | `sign_opposite_at_simple_root` | `b0465aa1281a` | ? |
| 41 | `sign_opposite_pos_deriv` | `67dcf4f2e86b` | ? |
| 42 | `sqfree_imp_sep` | `8750f4f0dede` | ? |
| 43 | `squarefree_imp_separable` | `squarefree_imp_separable.lean` | Over $\mathbb{R}$, `Squarefree` $\implies$ `Separable` (via `PerfectField`) |
| 44 | `squarefree_no_common_root` | `3a1e7f3f7a9f` | ? |
| 45 | `sturm_adjacent_opposite` | `d33018619834` | ? |
| 46 | `triple_sign_lemma` | `triple_sign_lemma.lean` | For $a \cdot c < 0, b \neq 0$: $[ab<0] + [bc<0] = 1$ |

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
|---|-----------|-------|----------|--------|
| 1 | 20260628T022441Z | `(unknown)` | agent-provided report | saved |
| 3 | 20260628T022640Z | `(unknown)` | agent-provided report | saved |
| 5 | 20260628T024341Z | `(unknown)` | agent-provided report | blocked |
| 7 | 20260628T032656Z | `sigma_constant_on_rootless_interval` | agent-provided report | blocked |
| 9 | 20260628T041414Z | `(unknown)` | agent-provided report | saved |
| 11 | 20260628T100936Z | `(unknown)` | agent-provided report | saved |
| 13 | 20260628T115822Z | `(unknown)` | agent-provided report | saved |
| 15 | 20260628T141408Z | `(unknown)` | agent-provided report | saved |
| 17 | 20260702T050818Z | `(unknown)` | agent-provided report | saved |
| 19 | 20260702T052654Z | `(unknown)` | agent-provided report | saved |
| 21 | 20260702T053716Z | `sigma_drop_at_root and sigma_const_no_root` | agent-provided report | saved |

## Recommended Next Steps

1. **Assemble main theorem** — all lemmas verified, wire them into `Submission.lean` and CI-verify.
