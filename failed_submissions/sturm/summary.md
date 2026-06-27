# Sturm Problem — Current State

## Problem

**Sturm's theorem**: For a squarefree real polynomial $p$ and interval $(a,b)$ with $a < b$ whose endpoints are not roots of $p$, the number of distinct roots of $p$ in $(a,b)$ equals $\sigma_p(a) - \sigma_p(b)$, where $\sigma_p(x)$ counts sign changes in the Sturm chain evaluated at $x$.

**Target theorem** (from `Submission.lean`):

```lean4
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  sorry
```

## Repository

`test1-deepthought/lean-eval-solutions/failed_submissions/sturm/`

- 10 saved attempts in git history (latest: `97257c8`)
- 3 top-level files: `Submission.lean`, `Sturm.lean`, `summary.md` (this file)
- 26 files in `Submission/` directory
- 1 file in `sturm_prelims/` directory

---

## Achieved — 16 Verified Lemmas

All verified via `lean4_exec` (exit code 0) across multiple attempts. Each lemma exists as its own `.lean` file in `Submission/`.

| # | Lemma | File | Purpose |
|---|-------|------|---------|
| 1 | `signChanges_nil` | `signChanges_nil.lean` | `signChanges [] = 0` |
| 2 | `signChanges_singleton` | `signChanges_singleton.lean` | `signChanges [a] = 0` |
| 3 | `signChanges_cons_zero` | `signChanges_cons_zero.lean` | Leading zero removed without affecting count |
| 4 | `signChanges_cons_cons_nonzero` | `signChanges_cons_cons_nonzero.lean` | Recurrence: $a \neq 0, b \neq 0 \implies \text{signChanges}(a::b::\text{rest}) = [ab<0] + \text{signChanges}(b::\text{rest})$ |
| 5 | `signChanges_filter_eq` | `signChanges_filter_eq.lean` | Invariant under zero removal |
| 6 | `signChanges_splice_zero` | `signChanges_splice_zero.lean` | Inserting zero doesn't change count |
| 7 | `signChanges_pair` | `signChanges_pair.lean` | `signChanges [a,b] = 1` iff $ab < 0$ |
| 8 | `squarefree_imp_separable` | `squarefree_imp_separable.lean` | Over $\mathbb{R}$, `Squarefree` $\implies$ `Separable` (via `PerfectField`) |
| 9 | `eval_derivative_ne_zero_of_squarefree_root` | `eval_derivative_ne_zero_of_squarefree_root.lean` | At a squarefree root, $p'(r) \neq 0$ |
| 10 | `sign_constant_on_Ioo` | `sign_constant_on_Ioo.lean` | If $q$ has no root in $(c,d)$, sign is constant there (via IVT) |
| 11 | `triple_sign_lemma` | `triple_sign_lemma.lean` | For $a \cdot c < 0, b \neq 0$: $[ab<0] + [bc<0] = 1$ |
| 12 | `eval_remainder_at_root` | `eval_remainder_at_root.lean` | $(a \% b).\text{eval}\, r = a.\text{eval}\, r$ when $b(r)=0$ |
| 13 | `factor_theorem_with_deriv` | `factor_theorem_with_deriv.lean` | $p = (X-r) \cdot q$ with $q(r) = p'(r)$ |
| 14 | `nonzero_near` | `nonzero_near.lean` | If $q(r) \neq 0$, there's a $\delta$-neighborhood where $q(x) \neq 0$ |
| 15 | `next_chain_entry_eval` | `next_chain_entry_eval.lean` | $(-(a \% b)).\text{eval}\, r = -a.\text{eval}\, r$ when $b(r)=0$ |
| 16 | `signChanges_triple_opposite` | `signChanges_triple_opposite.lean` | $\text{signChanges}[a,b,c] = 1$ when $a\cdot c < 0$ |

---

## Remaining Work — 3 Unproven Components

### 1. `sigma_drop_at_simple_root` (Critical — blocks everything)

**Statement**: At a simple root $r$ of squarefree $p$ (so $p'(r) \neq 0$), there exists $\delta > 0$ such that for all $u \in (r-\delta, r)$ and $v \in (r, r+\delta)$, $\sigma_p(u) - \sigma_p(v) = 1$.

**Why stuck**: The proof requires showing that only the first pair $(p, p')$ of the Sturm chain contributes a sign change difference of exactly 1 when crossing $r$, while all deeper entries contribute a net difference of zero. This requires:

- Analyzing the **recursive structure** of the Sturm chain: when $p(r)=0$ and $p'(r)\neq0$, the remainder $p\%p'$ evaluated at $r$ equals the next polynomial $p_2(r)$, and deeper entries come from the Sturm chain of $p'$.
- Formalizing the **invariant** that $\sigma_p(x)$ decomposes as $\text{sgn}(p(x))$ analysis on the first pair plus $\sigma_{p'}(x)$ for the tail.
- Using the **sign flip** of $p$ crossing the root (negated by sign constant of $p'$) to get exactly 1.

**Failed attempt**: A direct Lean proof via `posReal`/`negReal` thresholds ran into Finset membership issues ($0 \notin \text{Sign}$). The error: `failed to synthesize instance OfNat Sign 0`.

**Hypothesis**: The `Sign` type (from `Mathlib`) is a sum type $\{-1,0,1\}$ with no zero constant defined. The fix is to avoid `0 : Sign` and use `Sign.zero` or carry out sign analysis on $\mathbb{R}$ values instead.

### 2. `sigma_at_nonroot` (Must support induction)

**Statement**: If $p(r) \neq 0$, then there exists $\delta > 0$ such that for all $u,v \in (r-\delta, r+\delta)$, $\sigma_p(u) = \sigma_p(v)$. (In other words, the Sturm sign change count is locally constant away from roots.)

**Why stuck**: The proof is by induction on $\deg(p)$ (or more precisely, on the Sturm chain length). For the induction step:

- Base: $\deg(p) = 0$ is trivial.
- Inductive step: Show that if $p(r) \neq 0$ and $p'(r) \neq 0$ (or $p'(r) = 0$), the sign changes in the chain are stable. Uses continuity of polynomial evaluation: `sign_constant_on_Ioo` on each entry together with `next_chain_entry_eval` to relate remainders.
- The main difficulty is generalizing across arbitrary chain lengths without hardcoding the case analysis.

**Current state**: An inductive proof skeleton exists in early attempts but was never made to type-check.

### 3. Main theorem `sturm` (contains `sorry`)

**Current state** in `Submission.lean`:

```lean4
theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have h_sep : Separable p := squarefree_imp_separable p hp
  -- Induction on the number of roots in (a,b)
  sorry
```

The plan was:
1. **Base case**: Let $\text{roots}(p) \cap (a,b) = \emptyset$. Then $\text{sgn}(p)$ is constant on $(a,b)$ (by IVT/sign_constant_on_Ioo), the Sturm chain length is 2, and direct calculation gives $\sigma_p(a) = \sigma_p(b)$.
2. **Inductive case**: Pick a root $r \in (a,b)$, split $(a,b)$ into $(a,r) \cup (r,b)$, apply the IH to each subinterval, and use `sigma_drop_at_simple_root` to account for the contribution at $r$. The interval endpoints $a$ and $b$ are non-roots by hypothesis.

Neither the base case nor the inductive step has been written formally.

---

## Summary Table

| Component | Status | Effort Spent |
|-----------|--------|-------------|
| `signChanges` auxiliary lemmas (1–7) | **Verified** | ~20 attempts across 3 sessions |
| `sigma_drop_at_simple_root` | **Not proven** | 2 attempts (Finset Sign error) |
| `sigma_at_nonroot` | **Not proven** | 1 attempt (induction skeleton) |
| `squarefree_imp_separable` | **Verified** | imported, 1 attempt |
| `eval_derivative_ne_zero_of_squarefree_root` | **Verified** | 2 attempts |
| `sign_constant_on_Ioo` | **Verified** | 2 attempts |
| `triple_sign_lemma` | **Verified** | 1 attempt |
| `eval_remainder_at_root` | **Verified** | 2 attempts |
| `factor_theorem_with_deriv` | **Verified** | 3 attempts |
| `nonzero_near` | **Verified** | 1 attempt |
| `next_chain_entry_eval` | **Verified** | 1 attempt |
| `signChanges_triple_opposite` | **Verified** | 1 attempt |
| `sturm` (main theorem) | **Contains sorry** | skeleton exists |
| Induction framework, interval splitting | **Not started** | — |
| Final CI verification | **Not started** | — |

## Next Steps (Recommended Order)

1. **Repair `sigma_drop_at_simple_root`**: Replace uses of `0 : Sign` with `Sign.zero` or restructure using `ℝ` sign analysis to avoid the `OfNat Sign 0` typeclass failure.
2. **Prove `sigma_at_nonroot`** by induction on the Sturm chain length, using `sign_constant_on_Ioo` per entry and the remainder evaluation lemmas for the chain step.
3. **Assemble the main theorem**: induction on the number of roots in $(a,b)$, splitting at a root and applying the two sigma lemmas.
4. **Final verification**: `lean4_exec` on the full `Submission.lean`, then `solve_lean_eval_problem` CI preflight.
