# sturm — Current State

**Last updated:** 20260723T221828Z
**Total attempts:** 20
**Status:** PARTIALLY VERIFIED

## Target Theorem

See `Submission.lean` in the repository root or the latest attempt below.

## Verified Lemmas

**28 lemmas verified across all attempts**

| # | Lemma | SHA256 | Attempts |
|---|-------|--------|----------|
| 1 | `-------` | `--------` | ---------- |
| 2 | `Lemma_1036` | `737d483e79ee` | ? |
| 3 | `Lemma_4286` | `0c2cd859dc7b` | ? |
| 4 | `Lemma_4689` | `a0a796e0238b` | ? |
| 5 | `Lemma_4888` | `99218334fa8a` | ? |
| 6 | `Lemma_7428` | `cdf70d503528` | ? |
| 7 | `Lemma_7925` | `25828b01ed7a` | ? |
| 8 | `VerifiedLemmas` | `662b3f1ae138` | ? |
| 9 | `lt_of_le_and_ne` | `38f3f4e06664` | ? |
| 10 | `no_common_root` | `a4f272cc8365` | ? |
| 11 | `nodup_roots_of_squarefree` | `7f282722dd0b` | ? |
| 12 | `not_root_of_eval_ne_zero` | `1511660bbbe5` | ? |
| 13 | `signChanges_append_zeros` | `fe69e68f301a` | ? |
| 14 | `signChanges_cons_zero` | `cf7d7250e257` | ? |
| 15 | `signChanges_flip_first_eq` | `a499bd42b791` | ? |
| 16 | `signChanges_nil` | `ec4ac8f09f0e` | ? |
| 17 | `signChanges_opposite_ends` | `bb37e18fddca` | ? |
| 18 | `signChanges_pair` | `00e22926e6c1` | ? |
| 19 | `signChanges_singleton` | `0f086c54885b` | ? |
| 20 | `signChanges_zeros_irrelevant` | `744d4a053843` | ? |
| 21 | `sign_constant_on_closed_interval` | `3ae4ace4be1b` | ? |
| 22 | `squarefree_imp_no_common_root` | `b9313dcd4032` | ? |
| 23 | `squarefree_imp_separable` | `49ab5685abfc` | ? |
| 24 | `sturm` | `d83e4dc18e50` | ? |
| 25 | `sturmAux_succ_ne_zero` | `e79690260a2d` | ? |
| 26 | `sturmAux_zero_end` | `5d9a4f55737b` | ? |
| 27 | `zero_between_neg_and_pos` | `ac650f5c8161` | ? |
| 28 | `zero_between_pos_and_neg` | `86afac525c77` | ? |

## Unproven Components

**0 component(s) remaining**

All frontier lemmas verified — main theorem assembly remains.

**Last error:** mod_opposition: eval_neg rewrite issue (trivial). Main theorem: proof assembly incomplete.

## Strategy History

| # | Timestamp | Lemma | Approach | Result |
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
| 19 | 20260712T034133Z | `sigma_drop_at_simple_root` | agent-provided report | saved |
| 21 | 20260712T040726Z | `(unknown)` | agent-provided report | saved |
| 22 | 20260712T042508Z | `(unknown)` | agent-provided report | saved |
| 22 | 20260712T070915Z | `sigma_locally_constant: show sigma is constant on intervals where no chain entry vanishes` | agent-provided report | blocked |
| 22 | 20260720T084850Z | `sign_near_simple_root: For squarefree p with simple root r, sigma drops by exactly 1 across r. Then use induction on Finset of roots in (a,b) to complete the main theorem.` | agent-provided report | blocked |
| 22 | 20260720T091205Z | `sign_constant_on_interval (IVT-based lemma for sign constancy)` | failed: Sturm's theorem requires a substantial proof (~4000 lines in Isabelle AFP). The  | blocked |
| 22 | 20260723T114407Z | `sigma_constant_if_no_chain_root: prove sigma(a)=sigma(b) when no chain entry has a root in [a,b]` | agent-provided report | blocked |
| 22 | 20260723T132326Z | `(unknown)` | agent-provided report | saved |
| 22 | 20260723T220725Z | `signChanges_flip_first - just need `rw [add_comm]` or `omega` to finish` | failed: signChanges_flip_first: remaining goal `1 + S = S + 1` - trivial add_comm fix ne | blocked |
| 22 | 20260723T221632Z | `Complete sturm_opposition_at_root using the Euclidean algorithm property, then assemble the main theorem via Finset induction over the finite root set` | failed: Two remaining sorrys: sturm_opposition_at_root (chain recurrence evaluation) and | blocked |
| 22 | 20260723T221828Z | `Complete mod_opposition with eval_neg, prove interior_root_opposition lemma, then assemble main theorem via Finset induction.` | agent-provided report | blocked |

## Recommended Next Steps

1. **Assemble main theorem** — all lemmas verified, wire them into `Submission.lean` and CI-verify.
